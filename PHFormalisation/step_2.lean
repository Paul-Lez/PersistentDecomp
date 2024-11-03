import Mathlib.Algebra.Category.ModuleCat.Abelian
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
import Mathlib.Order.SetNotation
import Mathlib.Order.Disjoint
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import PHFormalisation.thm1_1with_decomp_struct
import PHFormalisation.Mathlib.Algebra.Module.Submodule.Pointwise
import PHFormalisation.Mathlib.Algebra.DirectSum.Basic

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
lemma PH.Submodule.ext' {N₁ N₂ : Submodule M} (h :
  ∀ x, N₁.mods x = N₂.mods x) : N₁ = N₂ := by
  aesop

-- Persistence submodules are ordered by pointwise inclusion
instance Submod_le : PartialOrder (PH.Submodule M) where
  le N₁ N₂ := ∀ x, N₁.mods x ≤ N₂.mods x
  le_refl N := fun x => le_refl _
  le_trans N₁ N₂ N₃ h h' x := le_trans (h x) (h' x)
  le_antisymm N₁ N₂ h h' := PH.Submodule.ext' _ (fun x => le_antisymm (h x) (h' x))

/- There's a notion of the supremum of two submodules, given by `⊕`,
and a notion of an infimum, given by `∩`.-/
instance : Lattice (PH.Submodule M) where
  sup N₁ N₂ := {
    mods := fun x => (N₁.mods x) ⊔ (N₂.mods x)
    h_mods := by
      intro x y f
      rw [Submodule.map_sup]
      apply sup_le_sup (N₁.h_mods f) (N₂.h_mods f) }
  le_sup_left a b x := by aesop
  le_sup_right a b x := by aesop
  sup_le a b c h h' x := by aesop
  inf N₁ N₂ := {
    mods := fun x => (N₁.mods x) ⊓ (N₂.mods x)
    h_mods := by
      intro x y f
      apply le_trans (Submodule.map_inf_le _) (inf_le_inf (N₁.h_mods f) (N₂.h_mods f)) }
  inf_le_left a b x := by aesop
  inf_le_right a b x := by aesop
  le_inf a b c h h' x := by aesop

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


-- There's a notion of supremum over arbitrary sets of submodules
@[simp]
instance : SupSet (PH.Submodule M) where
  sSup S := {
    -- The direct sum over arbitrary sets is just the pointwise direct sum
    mods := fun x => sSup {(N.mods x) | (N : PH.Submodule M) (_ : N ∈ S)}
    h_mods := by
      intro x y f
      rw [Submodule.map_sSup]
      sorry }


-- There's a notion of infimums over arbitrary sets of submodules
@[simp]
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


-- If S is a set of PH.Submodule, then ⨆ (p : S), (p.val.mods X) = (⨆ (p : S), p.val).mods X
-- In other words, we can take Sup and mods in whichever order we want.
lemma mods_iSup {ι : Sort*} (f : ι → PH.Submodule M)
  : (⨆ i, f i).mods X = ⨆ i, (f i).mods X := by
  apply eq_of_forall_ge_iff
  intro c
  simp
  simp [iSup]


lemma mods_sSup (S : Set (PH.Submodule M))
  : (sSup S).mods X = ⨆ (N : S), N.val.mods X := by
  rw [sSup_eq_iSup']
  exact mods_iSup ..


-- The sups and infs over possibly infinite sets are compatible with the lattice structure
instance : CompleteLattice (PH.Submodule M) where
  le_sSup S A h_mem X := by
    -- maybe write some API to get rid of these annoying sSups without
    -- resorting to the simp nuke?
    simp
    let A' : {x | ∃ N ∈ S, N.mods X = x} := ⟨A.mods X, by simp; use A⟩
    apply le_sSup_of_le (A'.prop) (by simp)
  sSup_le S A h_le X := by
    simp
    intro a h_mem_a
    exact h_le a h_mem_a X
  sInf_le S A h_mem X := by
    simp
    let A' : {x | ∃ N ∈ S, N.mods X = x} := ⟨A.mods X, by simp; use A⟩
    apply sInf_le_of_le A'.prop
    rfl
  le_sInf S A h_le X := by
    simp
    intro a h_mem_a
    exact h_le a h_mem_a X
  le_top A X := le_top
  bot_le A X := bot_le

end Submodules

section DirectSumDecomposition

@[ext]
structure DirectSumDecomposition where
  (S : Set (PH.Submodule M))
  -- TODO Paul: FIXME
  -- This needs to change a bit since we're saying that we're summing to M and then to N.
  -- But we can take care of that later on.
  (h_indep : CompleteLattice.SetIndependent S)
  (h_top : sSup S = ⊤)
  --(h : ∀ (x : C), DirectSum.IsInternal (M := M.obj x) (S := Submodule K (M.obj x))
    --(fun (p : PH.Submodule M) (hp : p ∈ S) => p.mods x))
  (bot_notin : ⊥ ∉ S)

lemma Indep_fun_eq_Indep_set (ι α κ : Type*) [CompleteLattice κ] [CompleteLattice α] :
  ∀ f : ι → κ → α, CompleteLattice.Independent f ↔ ∀ (k : κ), CompleteLattice.Independent (f · k) := by
  intro f
  constructor
  intro h_indep k
  simp [CompleteLattice.Independent] at *
  intro i
  have h_indep_i := h_indep i
  rw[Pi.disjoint_iff] at h_indep_i
  simp_all [iSup_apply]
  intro h_indep i
  simp [CompleteLattice.Independent] at h_indep
  rw[Pi.disjoint_iff]
  simp_all [iSup_apply]


lemma DirectSumDecomposition.pointwise_iSup_eq_top (D : DirectSumDecomposition M)
  (x : C) : ⨆ (p : PH.Submodule M) (_ : p ∈ D.S), p.mods x = ⊤ := sorry

lemma DirectSumDecomposition.pointwise_sSup_eq_top (D : DirectSumDecomposition M)
  (x : C) : ⨆ (p : PH.Submodule M) (_ : p ∈ D.S), p.mods x = ⊤ := sorry


variable {M : FunctCat C K} in
lemma DirectSumDecompositionIsInternal (I : DirectSumDecomposition M) :
  ∀ (x : C), DirectSum.IsInternal (M := M.obj x) (S := Submodule K (M.obj x))
  (fun (p : I.S) => p.val.mods x) := by
  intro X
  rw[DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top]
  constructor
  sorry
  rw[←mods_iSup, ←sSup_eq_iSup', I.h_top]
  rfl

-- We should probably go for this definition instead of the one above
variable {M : FunctCat C K} in
def IsRefinement : DirectSumDecomposition M → DirectSumDecomposition M → Prop :=
  fun D₁ D₂ => ∀ N ∈ D₂.S, ∃ B ⊆ D₁.S, N = sSup B


theorem right_lt_sup_of_left_ne_bot [SemilatticeSup α] [OrderBot α] {a b : α}
    (h : Disjoint a b) (ha : a ≠ ⊥) : b < a ⊔ b :=
  le_sup_right.lt_of_ne fun eq ↦ ha (le_bot_iff.mp <| h le_rfl <| sup_eq_right.mp eq.symm)


variable {M : FunctCat C K} in
lemma RefinementMapSurj' (I : DirectSumDecomposition M) (J : DirectSumDecomposition M)
  (h : IsRefinement J I) : (∀ N : J.S, ∃ A : I.S, N.val ≤ A.val) := by
  by_contra h_contra
  push_neg at h_contra
  rcases h_contra with ⟨N₀, h_not_le⟩
  have h_ge : N₀.val ⊔ sSup I.S ≤ sSup J.S := by
    rw[←sSup_pair]
    apply sSup_le_iff.mpr
    intro b h_mem
    rcases h_mem with ⟨h_n⟩
    · exact (le_sSup (h_n ▸ N₀.prop))
    · rename b ∈ {sSup I.S} => h_i
      have h' : sSup I.S ≤ sSup J.S := by
        rw[I.h_top, J.h_top]
      simp only [Set.mem_singleton_iff] at h_i
      exact (h_i ▸ h')
  let B : Set (PH.Submodule M) := {C | ∃ A : I.S, C ≤ A.val ∧ C ∈ J.S}
  have h_sub : B ⊆ J.S := by
    intro C h_C_mem
    simp [B] at h_C_mem
    exact h_C_mem.right
  have h_aux : sSup B = sSup I.S := by
    apply le_antisymm
    apply sSup_le
    intro b h_mem
    simp [B] at h_mem
    rcases h_mem with ⟨h₁, _⟩
    rcases h₁ with ⟨a, h_a, h_le⟩
    exact (le_sSup_of_le h_a h_le)
    have h_le_subset : ∀ A : I.S, ∃ C ⊆ B, A ≤ sSup C := by
      intro A
      choose f hf hf' using h
      let C' := f A.val (A.prop)
      use C'
      constructor
      intro α h_α
      simp [B]
      constructor
      use A
      constructor
      exact A.prop
      rw[(hf' A.val A.prop)]
      exact (le_sSup h_α)
      exact ((hf A.val A.prop) h_α)
      rw[←(hf' A.val A.prop)]
    apply sSup_le
    intro A h_A_mem
    rcases (h_le_subset ⟨A, h_A_mem⟩) with ⟨C, h_C⟩
    simp only at h_C
    exact (le_trans h_C.right (sSup_le_sSup h_C.left))
  have h_aux' : N₀.val ∉ B := by
    intro h_contra
    simp [B] at h_contra
    rcases h_contra with ⟨A, h₁, h₂⟩
    exact (h_not_le (⟨A, h₁⟩) h₂)
  have h_disj : Disjoint N₀.val (sSup B) := by
    exact (CompleteLattice.SetIndependent.disjoint_sSup J.h_indep N₀.prop h_sub h_aux')
  have h_not_bot : N₀.val ≠ ⊥ := by
    intro h_contra
    exact J.bot_notin (h_contra ▸ N₀.prop)
  have h_gt : sSup I.S < N₀.val ⊔ sSup I.S := by
    rw[←h_aux]
    --No clue why I couldn't use this theorem from mathlib directly and had to copy paste it here instead
    --assuming it has to do with needing to bump
    exact (right_lt_sup_of_left_ne_bot h_disj h_not_bot)
  have contra : (⊤ : PH.Submodule M) < ⊤ := by
    rw [I.h_top, J.h_top] at *
    apply lt_of_lt_of_le h_gt h_ge
  exact (lt_self_iff_false (⊤ : PH.Submodule M)).mp contra


instance : Preorder (DirectSumDecomposition M) where
  le D₁ D₂ := IsRefinement D₂ D₁
  --D₁ ≤ D₂ iff D₂ refines D₁.
  le_refl D := by intro N _; use {N}; aesop
  le_trans I₁ I₂ I₃ h12 h23 := by
    intro N h_mem
    rcases (h12 N h_mem) with ⟨C, h_sub, h_eq⟩
    choose f hf hf' using h23
    let A := ⨆ (c : C), (f c.val (h_sub c.prop))
    use A
    constructor
    · apply iSup_le_iff.mpr
      intro c
      exact (hf c.val (h_sub c.prop))
    · have h_aux' : sSup A = sSup C := by
        apply le_antisymm
        apply sSup_le_iff.mpr
        intro a h_a
        have h_aux'' : ∃ (c : C), a ∈ (f c.val (h_sub c.prop)) := by aesop
        rcases h_aux'' with ⟨c_a, h_ca⟩
        have h_le : a ≤ c_a := by
          rw[hf' c_a _]
          apply le_sSup h_ca
        apply le_sSup_of_le c_a.prop h_le
        apply sSup_le
        intro c h_mem_c
        let c' : C := ⟨c, h_mem_c⟩
        have h_le_c : c ≤ sSup (f c'.val (h_sub c'.prop)) := by
          rw[← (hf' c'.val (h_sub c'.prop))]
        apply le_trans h_le_c
        apply sSup_le
        intro a h_mem_a
        have h_a_in_A : a ∈ A := by
          have h_subs : (f c'.val (h_sub c'.prop)) ≤ A := by
            apply le_iSup_of_le c'
            exact le_rfl
          exact h_subs h_mem_a
        exact le_sSup h_a_in_A
      rwa [h_aux']


instance : PartialOrder (DirectSumDecomposition M) where
  --I suspect this will be painful to prove
  le_antisymm := by
    intro I J h_I_le_J h_J_le_I
    have h_final_left : ∀ N ∈ J.S, N ∈ I.S := by
      intro N
      by_contra h_neg
      push_neg at h_neg
      rcases h_neg with ⟨h_N_in_J, h_N_not_in_I⟩
      let N' : J.S := ⟨N, h_N_in_J⟩
      have h_A : ∃ A : I.S, N ≤ A.val := by
        exact (RefinementMapSurj' I J h_I_le_J) N'
      rcases h_A with ⟨A, h_N_le_A⟩
      choose f hf hf' using h_J_le_I
      let B := f N'.val N'.prop
      let h_B₁ := hf' N'.val N'.prop
      let h_B₂ := hf N'.val N'.prop
      simp only at h_B₁
      have h_mem : A.val ∈ B := by
        by_contra h_A_not_mem
        have h_aux : Disjoint A.val (sSup B) := by
          exact (CompleteLattice.SetIndependent.disjoint_sSup I.h_indep A.prop h_B₂ h_A_not_mem)
        have h_aux' : sSup B ≤ A.val := by
          exact (h_B₁ ▸ h_N_le_A)
        have h_last : sSup B = (⊥ : PH.Submodule M) := by
          rw [disjoint_comm] at h_aux
          exact (Disjoint.eq_bot_of_le h_aux h_aux')
        rw[←h_B₁] at h_last
        subst h_last
        exact (J.bot_notin h_N_in_J)
      have h_A_le_N : A.val ≤ N := by
        rw[h_B₁]
        exact le_sSup h_mem
      have h_A_eq_N : A.val = N := by
        exact (le_antisymm h_A_le_N h_N_le_A)
      have h_contra : N ∈ I.S := by
        exact h_A_eq_N ▸ A.prop
      aesop
    have h_final_right : ∀ N ∈ I.S, N ∈ J.S := by
      sorry
    aesop




end DirectSumDecomposition

section Chains

/- In this section we set up what's needed to take an inverse limit of direct sum
decompositions. Since these are defined in terms of sets, we could construct the
inverse limit explicitly but I think this would be really painful and messy...-/

-- Here we write some code to go from chains in directSumDecompositions to diagrams in the category of types
variable {M} in
noncomputable def ToTypeCat : (DirectSumDecomposition M) ⥤ Type where
  obj D := Subtype D.S
  -- Define the maps f_{IJ} induced by "J refines I"
  map {I J} f := by
    dsimp
    let h_le := leOfHom f
    let g : J.S → I.S := fun N => (RefinementMapSurj' I J h_le N).choose
    sorry
    --exact g is what we want but this is wrong arrow direction


/- This is possibly useful to make things a bit cleaner so let's keep it for now but possibly remove it later -/
variable {M} in
noncomputable def ChainToTypeCat (T : Set (DirectSumDecomposition M)) :
  Subtype T ⥤ Type where
  obj D := ToTypeCat.obj D.val
  map {J I} f := ToTypeCat.map f
  map_id := by
    dsimp
    intro I
    rw [←ToTypeCat.map_id]
    rfl
  map_comp := by
    dsimp
    intro I J K f g
    rw [←ToTypeCat.map_comp]
    rfl


/- Construct the element `L` (in the notation of our doc) -/
def ChainToInverseLimit (T : Set (DirectSumDecomposition M)) :
  Type := limit (ChainToTypeCat T)


variable (N : PH.Submodule M) (T : Set (DirectSumDecomposition M)) (l : limit (ChainToTypeCat T))
variable (I : Subtype T)
variable (D : DirectSumDecomposition M)
#check (limit.π (ChainToTypeCat T)) --this is the morphism L ⟶ ChainToTypeCat.obj I
#check ((limit.π (ChainToTypeCat T) I) l) -- apply this morphism to l. This has type (ChainToTypeCat T).obj I - other words, Subtype I.val.S
#check ((limit.π (ChainToTypeCat T) I) l).val --PH.Submodule
#check ((limit.π (ChainToTypeCat T) I) l).prop
#check (ChainToTypeCat T)
#check I.val
#check (ChainToTypeCat T)
#check (ChainToTypeCat T).obj I

/-Construct `M[λ]` in the notation of our doc -/
variable {M} in
noncomputable def Submodule_of_chain {T : Set (DirectSumDecomposition M)} (hT : IsChain
  LE.le T) (l : limit (ChainToTypeCat T)) : PH.Submodule M := by
  let f : Subtype T → PH.Submodule M := fun (I : Subtype T) ↦ ((limit.π (ChainToTypeCat T) I) l).val
  let M_l : (PH.Submodule M) := ⨅ (I : Subtype T), f I
  exact M_l







/-`M` is the direct sum of all the `M[λ]` -/
variable {M} in
lemma M_is_dir_sum_lambdas {T : Set (DirectSumDecomposition M)} (hT : IsChain
  LE.le T) (x : C) :
  DirectSum.IsInternal (fun (l : limit (ChainToTypeCat T)) => ((Submodule_of_chain hT l).mods x : Submodule K (M.obj x))) := by
  rw[DirectSum.isInternal_iff]
  constructor
  · intro m h_ker
    let Λ I := limit.π (ChainToTypeCat T) I
    obtain ⟨J, hJ⟩ : ∃ (J : T), Pairwise fun l₁ l₂ ↦ Λ J l₁ ≠ Λ J l₂ := by
      sorry

    sorry
  · sorry



/- Get a direct sum out of a chain (this should be the index set 𝓤 in out doc)-/
variable {M} in
def DirectSumDecomposition_of_chain {T : Set (DirectSumDecomposition M)} (hT : IsChain
  LE.le T) : DirectSumDecomposition M where
  S := {(Submodule_of_chain hT l) | (l : limit (ChainToTypeCat T)) (_ : ¬ IsBot (Submodule_of_chain hT l))}
  h_top := by sorry
  h_indep := by sorry
  bot_notin := sorry

/- The set `𝓤` is an upper bound for the chain `T` -/
lemma every_chain_has_an_upper_bound (N : PH.Submodule M)
    {T : Set (DirectSumDecomposition M)} (hT : IsChain LE.le T) :
    ∀ D ∈ T, D ≤ DirectSumDecomposition_of_chain hT := by
  intro D hD
  sorry

/-Every chain has an upper bound, hence there is a maximal direct sum decomposition `D`-/
lemma zorny_lemma (N : PH.Submodule M) : ∃ (D : DirectSumDecomposition M), IsMax D := by
  apply zorn_le
  rintro T hT
  rw [bddAbove_def]
  use (DirectSumDecomposition_of_chain hT)
  exact (every_chain_has_an_upper_bound M N hT)

end Chains

section Indecomposable

-- For this to work we would need to change the definition of a DirectSumDecompositon
-- since at the moment it only work for `⊤`.
-- Alternatively, we could also construct the subfunctor that arises from a submodule
def TrivialDecomp (N : PH.Submodule M) : DirectSumDecomposition M where
  S := {N}
  h_indep := by sorry
  h_top := by sorry
  bot_notin := sorry

/--`M` is indecomposable iff its only non-trivial submodule is the zero submodule `⊥`-/
def Indecomposable : Prop := IsMax (TrivialDecomp M ⊤)

variable {M} in
/--This is the definition of indecomposability we should be using since it's more general
(works at a lattice theoretic level)-/
-- TODO: we don't need `a ≤ N` and `b ≤ N` in the implications
def Indecomposable' (N : PH.Submodule M) : Prop :=
  ∀ a b : PH.Submodule M, a ≤ N → b ≤ N → a ⊓ b = ⊥ → a ⊔ b = N → a = ⊥ ∨ b = ⊥

-- Maximal direct sum decompositions consist of indecomposable submodules.
lemma Indecomposable_of_mem_Max_Direct_sum_decomposition
  (D : DirectSumDecomposition M) (N : PH.Submodule M) (hN : N ∈ D.S) (hmax : IsMax D) :
  IsMax (TrivialDecomp M N) := by
  by_contra hNotMax
  rw[IsMax] at hNotMax
  push_neg at hNotMax
  rcases hNotMax with ⟨P, hle, hneq⟩
  let S : Set (PH.Submodule M) := (D.S \ {N}) ⊔ P.S
  have h (x : C) : DirectSum.IsInternal (fun p : S => (p.val.mods x : Submodule _ _)) := by sorry
  have h' : ⊤ = sSup S := by sorry
  let Cex : DirectSumDecomposition M := ⟨S, sorry, sorry, sorry⟩
  have contra : ¬ IsMax D := by sorry
  exact contra hmax

variable {M} in
/--
If `D` is a direct sum decomposition of `M` and for each `N` appearing in `S` we are given a direct
sum decomposition of `N`, we can construct a refinement of `D`.
-/
def RefinedDirectSumDecomposition
    {D : DirectSumDecomposition M}
    (B : ∀ (N : PH.Submodule M), N ∈ D.S → Set (PH.Submodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, CompleteLattice.SetIndependent (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) :
    DirectSumDecomposition M where
    S := ⋃ (N) (hN), B N hN
    h_indep := by
      intro x
      · intro a b ha hb
        --We need to show that the submodules appearing in the decomposition are independent
        --might be a little annoying
        sorry
    h_top := by
      simp_rw [sSup_iUnion]
      calc
        ⨆ i, ⨆ (i_1 : i ∈ D.S), sSup (B i i_1) = ⨆ (i) (i_1 : i ∈ D.S), i := by
          apply iSup_congr
          intro I
          by_cases hI : I ∈ D.S
          · simp only [hB I hI, instSupSetSubmodule, exists_prop]
          · simp only [hI, instSupSetSubmodule, exists_prop, not_false_eq_true, iSup_neg]
        _ = ⊤ := by rw [←D.h_top, sSup_eq_iSup]
    bot_notin := by
      intro h
      simp_rw [Set.mem_iUnion] at h
      obtain ⟨N, hN, hbot⟩ := h
      exact hB'' N hN hbot

lemma RefinedDirectSumDecomposition_le
    {D : DirectSumDecomposition M}
    (B : ∀ (N : PH.Submodule M), N ∈ D.S → Set (PH.Submodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, CompleteLattice.SetIndependent (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) :
    (RefinedDirectSumDecomposition B hB hB' hB'') ≤ D := sorry

lemma RefinedDirectSumDecomposition_lt_of_exists_ne_singleton
    {D : DirectSumDecomposition M}
    (B : ∀ (N : PH.Submodule M), N ∈ D.S → Set (PH.Submodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, CompleteLattice.SetIndependent (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN)
    (H : ∃ (N : PH.Submodule M) (hN : N ∈ D.S), B N hN ≠ {N}) :
    (RefinedDirectSumDecomposition B hB hB' hB'') < D := sorry

lemma Indecomposable'_of_mem_Min_Direct_sum_decomposition
  (D : DirectSumDecomposition M) (N : PH.Submodule M) (hN : N ∈ D.S) (hmax : IsMin D) : Indecomposable' N := by
  by_contra hNotMax
  rw [Indecomposable'] at hNotMax
  simp only [not_forall, Classical.not_imp, not_or, exists_and_left] at hNotMax
  obtain ⟨x, hx, y, hx', hy', hxy, hxy', hy⟩ := hNotMax
  set B : ∀ (N : PH.Submodule M), N ∈ D.S → Set (PH.Submodule M) :=
    fun (M : PH.Submodule M) (hM : M ∈ D.S) => if M = N then {x, y} else {M} with hB
  set newD : DirectSumDecomposition M := RefinedDirectSumDecomposition
    B sorry sorry sorry
  have contra : ¬ IsMin D := by
    simp only [not_isMin_iff]
    use newD
    apply RefinedDirectSumDecomposition_lt_of_exists_ne_singleton
    use N, hN
    simp only [hB, if_true]
    intro h
    --This should be easy
    sorry
  sorry

-- /-- If `N` is a submodule of `M` that is part of a minimal direct sum decomposition, then `N` is indecomposable -/
-- lemma Indecomposable'_of_mem_Min_Direct_sum_decomposition'
--   (D : DirectSumDecomposition M) (N : PH.Submodule M) (hN : N ∈ D.S) (hmax : IsMin D) : Indecomposable' N := by
--   by_contra hNotMax
--   rw [Indecomposable'] at hNotMax
--   simp only [not_forall, Classical.not_imp, not_or, exists_and_left] at hNotMax
--   obtain ⟨x, hx, y, hx', hy', hxy, hxy', hy⟩ := hNotMax
--   set newD : DirectSumDecomposition M := RefinedDirectSumDecomposition
--     (fun (M : PH.Submodule M) (hM : M ∈ D.S) => if M = N then {x, y} else {M}) sorry sorry sorry

--   set S : Set (PH.Submodule M) := (D.S \ {N}) ∪ {x, y} with hS
--   have h : ∀ (x : C), DirectSum.IsInternal (fun p : S => (p.val.mods x : Submodule _ _)) := by
--     intro x'
--     rw [DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top]
--     constructor
--     · --this is going to be a bit of a pain to prove
--       intro a b hab hb'
--       by_cases ha : a = x
--       · have : b ≤ N.mods x' := le_trans (ha ▸ hab) (hx' x')
--         --this should now follow from the independence of the direct sum decomposition `D`
--         --have := calc b ≤ (⨆ j, ⨆ (_ : j ≠ a), (fun (p : S) ↦ p.val.mods x') j) := by sorry
--         --_ ≤ (⨆ j, ⨆ (_ : j ≠ a), (fun (p : D.S) ↦ p.val.mods x') j)
--         sorry
--       · by_cases hb : a = y
--         · have : b ≤ N.mods x' := le_trans (hb ▸ hab) (hy' x')
--           --this should now follow from the independence of the direct sum decomposition `D`
--           sorry
--           --Since the sum is over j ≠ a, it will include `x ⊔ y = N` so we can rewrite it in a nicer way
--         · have : (⨆ j, ⨆ (_ : j ≠ a), (fun (p : S) ↦ p.val.mods x') j) =
--             ⨆ j, ⨆ (_ : j.val ≠ a.val), (fun (p : D.S) => p.val.mods x') j := by
--             sorry
--           --this should now follow from the independence of the direct sum decomposition `D`
--           rw [this] at hb'
--           sorry
--       --The direct sum is indexed over all `j` in `S` so we can rewrite it in a nicer way by using `x ⊔ y = N`.
--     · calc (⨆ (p : S), p.val.mods x') = (⨆ (p : D.S), p.val.mods x') := by sorry
--       _ = ⊤ := ((DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top _).mp <| D.h x').right
--   let Cex : DirectSumDecomposition M := ⟨S, h, sorry⟩
--   have contra : ¬ IsMin D := by
--     simp only [not_isMin_iff]
--     use Cex
--     apply lt_of_le_of_ne
--     --this is very golfable
--     · set d : D.S → Set (PH.Submodule M) := fun (I : D.S) ↦ if I.val = N then {x, y} else {I.val} with hd
--       use d, fun I => ?_, fun I => ?_
--       · by_cases hI : I.val = N
--         · simp only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton, ← hxy']
--         · simp only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton]
--       · by_cases hI : I.val = N
--         · simpa only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton, hS] using Set.subset_union_right
--         · simp only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton, Set.singleton_subset_iff]
--           apply Set.mem_union_left _ (Set.mem_diff_of_mem I.prop _)
--           rw [Set.mem_singleton_iff]
--           exact hI
--     · --this can probably be golfed with the right API
--       intro h
--       have : D.S ≠ Cex.S := by
--         simp only [ne_eq]
--         intro h'
--         have: N ∉ S := by
--           intro h''
--           rw [hS, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_diff, Set.mem_singleton_iff] at h''
--           simp only [not_true_eq_false, and_false, false_or] at h''
--           rcases h'' with h'' | h''
--           · rw [←h'', inf_eq_right.mpr hy'] at hxy
--             exact hy hxy
--           · rw [←h'', inf_eq_left.mpr hx'] at hxy
--             exact hx hxy
--         rw [h'] at hN
--         exact this hN
--       exact this (congrArg DirectSumDecomposition.S h.symm)
--   exact contra hmax

end Indecomposable

section

/- TODO in this section: construct the persistence module associated to a submodule,
and show that submodules that are atoms yield indecomposable persistence modules-/

end
