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
  inf_le_left := by
    intro a b x
    aesop
  inf_le_right := by
    intro a b x
    aesop
  le_inf := by
    intro a b c h h' x
    aesop

/- There's a notion of a minimal submodule, namely `0`-/
instance : OrderBot (PH.Submodule M) where
  bot := {
    mods := fun x => ⊥
    h_mods := by aesop
  }
  bot_le N := fun x => bot_le

/- There's a notion of a maximal submodule, namely `M`-/
instance : OrderTop (PH.Submodule M) where
  top := {
    mods := fun x => ⊤
    h_mods := by aesop
  }
  le_top N := fun x => le_top

-- There's a notion of supremum over arbitrary sets of submodules
instance : SupSet (PH.Submodule M) where
  sSup S := {
    -- The direct sum over arbitrary sets is just the pointwise direct sum
    mods := fun x => sSup {(N.mods x) | (N : PH.Submodule M) (_ : N ∈ S)}
    h_mods := by
      intro x y f x hx
      sorry

  }

-- There's a notion of infimums over arbitrary sets of submodules
instance : InfSet (PH.Submodule M) where
  sInf S := {
    -- The intersection over arbitrary sets is just the pointwise direct sum
    mods := fun x => sInf {(N.mods x) | (N : PH.Submodule M) (_ : N ∈ S)}
    h_mods := sorry
  }

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
  -- The submodules in the direct sum decomposition are linearly independent.
  -- There are several ways of stating this, but we should have a think
  -- about which is the most convenient to work with
  {h : true}
  -- `N` is the direct sum of the submodules in `S`
  (h' : N = sSup S)

variable {M : FunctCat C K} in
def IsRefinement (N : PH.Submodule M) : DirectSumDecomposition N → DirectSumDecomposition N → Prop :=
  sorry
  --fun D₁ D₂ => ∃ d : D₂ → Set (D₁.val), ∀ N, N = sSup ((d N))

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
def ToTypeCat (N : PH.Submodule M) : (DirectSumDecomposition N) ⥤ Type 1 where
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

/- Get a direct sum out of a chain (this should be the index set 𝓤 in out doc)-/
variable {M} in
def DirectSumDecomposition_of_chain {N : PH.Submodule M} {T : Set (DirectSumDecomposition N)} (hT : IsChain
  LE.le T) : DirectSumDecomposition N := sorry

/- The set `𝓤` is an upper bound for the chain `T` -/
lemma every_chain_has_an_upper_bound (N : PH.Submodule M)
  {T : Set (DirectSumDecomposition N)} (hT : IsChain LE.le T) :
  ∀ D ∈ T, D ≤ DirectSumDecomposition_of_chain hT := by
  sorry

end Chains