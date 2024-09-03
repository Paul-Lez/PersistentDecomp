import Mathlib.Algebra.Category.ModuleCat.Abelian --ModuleCat is an abelian category
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Algebra.Module.Prod
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Artinian
import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.SetLike.Fintype
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import PHFormalisation.PHFormalisation.thm1_1with_decomp_struct

open CategoryTheory Classical CategoryTheory.Limits
open Filter

/- In this file we sketch what we'll need to prove to
get Step 2 done. Most of the work is setting the stage so
we can apply Zorn's lemma.-/

/- For now we work with types in the 0-th universe. To make the code universe polymorphic we'll need to
make a few edits below-/
variable {C : Type} [Category.{0, 0} C] {K : Type} [DivisionRing K] (M : FunctCat C K)

section Submodules

@[ext]
structure PH.Submodule where
    (mods (x : C) : Submodule K (M.obj x))
    /- TODO: add condition that the inclusion of the submodules
    is compatible with the "transition" maps of the functor M,
    i.e if we have f : x ⟶ y then the image of `mods x` by `M f` lies
    in the submodule `mods y`. -/
    (h_mods : ∀ {x y : C} (f : x ⟶ y), (mods x).map (M.map f) ≤ mods y)


-- TODO: make this better.
@[ext]
lemma PH.Submodule.ext' (N₁ N₂ : Submodule M) (h :
  ∀ x, N₁.mods x = N₂.mods x) : N₁ = N₂ := by
  aesop

-- Persistence submodules are ordered by pointwise inclusion
instance : PartialOrder (PH.Submodule M) where
  le N₁ N₂ := ∀ x, N₁.mods x ≤ N₂.mods x
  le_refl N := fun x => le_refl _
  le_trans N₁ N₂ N₃ := by
    intro h h' x
    exact le_trans (h x) (h' x)
  le_antisymm N₁ N₂ := by
    intro h h'
    apply PH.Submodule.ext'
    intro x
    exact le_antisymm (h x) (h' x)

/- There's a notion of the supremum of two submodules, given by `⊕`,
and a notion of an infimum, given by `∩`.-/
instance : Lattice (PH.Submodule M) where
  sup N₁ N₂ := {
    mods := fun x => (N₁.mods x) ⊔ (N₂.mods x)
    h_mods := by
      intro x y f
      rw [Submodule.map_sup]
      apply sup_le_sup (N₁.h_mods f) (N₂.h_mods f) }
  le_sup_left := by
    intro a b x
    aesop
  le_sup_right := by
    intro a b x
    aesop
  sup_le := by
    intro a b c h h' x
    aesop
  inf N₁ N₂ := {
    mods := fun x => (N₁.mods x) ⊓ (N₂.mods x)
    h_mods := by
      intro x y f
      apply le_trans (Submodule.map_inf_le _) (inf_le_inf (N₁.h_mods f) (N₂.h_mods f)) }
  inf_le_left a b x := by aesop
  inf_le_right a b x := by aesop
  le_inf := by
    intro a b c h h' x
    aesop

/- There's a notion of a minimal submodule, namely `0`-/
instance : OrderBot (PH.Submodule M) where
  bot := {
    mods := fun x => ⊥
    h_mods := by aesop }
  bot_le N := fun x => bot_le

/- There's a notion of a maximal submodule, namely `M`-/
instance : OrderTop (PH.Submodule M) where
  top := {
    mods := fun x => ⊤
    h_mods := by aesop }
  le_top N := fun x => le_top

section

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (p p' : Submodule R M) (q q' : Submodule R₂ M₂)
variable {x : M}
variable [RingHomSurjective σ₁₂] {F : Type*} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]
variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]

lemma Submodule.map_sSup (f : F) (S : Set (Submodule R M)) :
  (sSup S).map f = sSup (map f '' S) := by sorry

lemma Submodule.map_sInf (f : F) (S : Set (Submodule R M)) :
  (sInf S).map f ≤ sInf (map f '' S) := by sorry

end

-- There's a notion of supremum over arbitrary sets of submodules
instance : SupSet (PH.Submodule M) where
  sSup S := {
    -- The direct sum over arbitrary sets is just the pointwise direct sum
    mods := fun x => sSup {(N.mods x) | (N : PH.Submodule M) (_ : N ∈ S)}
    h_mods := by
      intro x y f
      rw [Submodule.map_sSup]
      sorry }

-- There's a notion of infimums over arbitrary sets of submodules
instance : InfSet (PH.Submodule M) where
  sInf S := {
    -- The intersection over arbitrary sets is just the pointwise direct sum
    mods := fun x => sInf {(N.mods x) | (N : PH.Submodule M) (_ : N ∈ S)}
    h_mods := by
      intro x y f
      apply le_trans (Submodule.map_sInf _ _)
      apply sInf_le
      -- Here we're using the compatibility condition on submodules
      sorry }

-- The sups and infs over possibly infinite sets are compatible with the lattice structure
instance : CompleteLattice (PH.Submodule M) where
  le_sSup := sorry
  sSup_le := sorry
  sInf_le := sorry
  le_sInf := sorry
  le_top := sorry
  bot_le := sorry

end Submodules

section DirectSumDecomposition

variable {M} in
structure DirectSumDecomposition (N : PH.Submodule M) where
  {S : Set (PH.Submodule M)}
  -- This needs to change a bit since we're saying that we're summing to M and then to N.
  -- But let's take care of that later on.
  {h : ∀ (x : C), DirectSum.IsInternal (fun p : S => (p.val.mods x : Submodule _ _)) }
  -- `N` is the direct sum of the submodules in `S`
  (h' : N = sSup S)

variable {M : FunctCat C K} in
def IsRefinement (N : PH.Submodule M) : DirectSumDecomposition N → DirectSumDecomposition N → Prop :=
  fun D₁ D₂ => ∃ d : D₂.S → Set (PH.Submodule M), (∀ (N : D₂.S), N.val = sSup ((d N))) ∧ (∀ N, d N ⊆ D₁.S)

/- The decompositions are ordered by refinement. With the current definition of
refinement, this might be a bit awkward to prove, so let's leave it sorried out for now.-/
instance (N : PH.Submodule M) : Preorder (DirectSumDecomposition N) :=
  sorry

end DirectSumDecomposition

section Chains

/- In this section we set up what's needed to take an inverse limit of direct sum
decompositions. Since these are defined in terms of sets, we could construct the
inverse limit explicitly but I think this would be really painful and messy...-/

-- Here we write some code to go from chains in directSumDecompositions to diagrams in the category of types
variable {M} in
def ToTypeCat (N : PH.Submodule M) : (DirectSumDecomposition N) ⥤ Type where
  obj D := Subtype D.S
  -- Define the maps f_{IJ} induced by I ≤ J
  map f := sorry

/- This is possibly useful to make things a bit cleaner so let's keep it for now but possibly remove it later -/
variable {M} in
def ChainToTypeCat (N : PH.Submodule M) (T : Set (DirectSumDecomposition N)) :
  Subtype T ⥤ Type where
  obj D := sorry
  map f := sorry

/- Construct the element `L` (in the notation of our doc) -/
def ChainToInverseLimit (N : PH.Submodule M) (T : Set (DirectSumDecomposition N)) :
  Type := limit (ChainToTypeCat N T)


variable (N : PH.Submodule M) (T : Set (DirectSumDecomposition N)) (L : limit (ChainToTypeCat N T))
variable (I : Subtype T)
#check limit.π (ChainToTypeCat N T) I -- this is how we access the morphism L ⟶ I


/- Get a direct sum out of a chain (this should be the index set 𝓤 in out doc)-/
variable {M} in
def DirectSumDecomposition_of_chain {N : PH.Submodule M} {T : Set (DirectSumDecomposition N)} (hT : IsChain
  LE.le T) : DirectSumDecomposition N := sorry

/- The set `𝓤` is an upper bound for the chain `T` -/
lemma every_chain_has_an_upper_bound (N : PH.Submodule M)
  {T : Set (DirectSumDecomposition N)} (hT : IsChain LE.le T) :
  ∀ D ∈ T, D ≤ DirectSumDecomposition_of_chain hT := by
  sorry

/-Every chain has an upper bound, hence there is a maximal direct sum decomposition `D`-/
lemma zorny_lemma (N : PH.Submodule M) : ∃ (D : DirectSumDecomposition N), IsMax D := by
  apply zorn_le
  rintro T hT
  rw[bddAbove_def]
  use (DirectSumDecomposition_of_chain hT)
  exact (every_chain_has_an_upper_bound M N hT)

end Chains

section Indecomposable

/--`M` is indecomposable iff its only non-trivial submodule is the zero submodule `⊥`-/
def Indecomposable : Prop := IsAtom (⊤ : PH.Submodule M)

-- Maximal direct sum decompositions consist of indecomposable submodules.
lemma Indecomposable_of_mem_Max_Direct_sum_decomposition
  (D : DirectSumDecomposition ⊤) (N : PH.Submodule M) (hN : N ∈ D.S) :
  IsAtom N := by sorry

end Indecomposable

section

/- TODO in this section: construct the persistence module associated to a submodule,
and show that submodules that are atoms yield indecomposable persistence modules-/

end
