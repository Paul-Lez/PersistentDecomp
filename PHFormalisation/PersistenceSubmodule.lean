import PHFormalisation.Mathlib.Algebra.Module.Submodule.Pointwise
import PHFormalisation.thm1_1with_decomp_struct

open CategoryTheory Classical CategoryTheory.Limits
open Filter


/- In this file we sketch what we'll need to prove to
get Step 2 done. Most of the work is setting the stage so
we can apply Zorn's lemma.-/

/- For now we work with types in the 0-th universe. To make the code universe polymorphic we'll need to
make a few edits below-/
variable {C : Type} [Category.{0, 0} C] {K : Type} [DivisionRing K] {M : FunctCat C K}

variable (M) in
structure PersistenceSubmodule where
    toFun (c : C) : Submodule K (M.obj c)
    /- TODO: add condition that the inclusion of the submodules
    is compatible with the "transition" maps of the functor M,
    i.e if we have f : x ⟶ y then the image of `toFun x` by `M f` lies
    in the submodule `toFun y`. -/
    map_le' {x y : C} (f : x ⟶ y) : (toFun x).map (M.map f) ≤ toFun y

namespace PersistenceSubmodule

instance :
    DFunLike (PersistenceSubmodule M) C fun c ↦ Submodule K (M.obj c) where
  coe := toFun
  coe_injective' N₁ N₂ := by cases N₁; cases N₂; congr!

lemma map_le {x y : C} (N : PersistenceSubmodule M) (f : x ⟶ y) :
    (N x).map (M.map f) ≤ N y := N.map_le' _

@[ext]
lemma ext {N₁ N₂ : PersistenceSubmodule M} (h : ∀ c, N₁ c = N₂ c) : N₁ = N₂ :=
  DFunLike.ext _ _ h

/-- Persistence submodules are ordered pointwise. -/
instance : PartialOrder (PersistenceSubmodule M) :=
  PartialOrder.lift (⇑) DFunLike.coe_injective

instance : Sup (PersistenceSubmodule M) where
  sup N₁ N₂ := {
    toFun := fun c ↦ N₁ c ⊔ N₂ c
    map_le' := by
      intro x y f
      rw [Submodule.map_sup]
      apply sup_le_sup (N₁.map_le f) (N₂.map_le f) }

instance : Inf (PersistenceSubmodule M) where
  inf N₁ N₂ := {
    toFun := fun c ↦ N₁ c ⊓ N₂ c
    map_le' := by
      intro x y f
      apply le_trans (Submodule.map_inf_le _)
        (inf_le_inf (N₁.map_le f) (N₂.map_le f)) }

@[simp, norm_cast]
lemma coe_sup (N₁ N₂ : PersistenceSubmodule M) : ⇑(N₁ ⊔ N₂) = ⇑N₁ ⊔ ⇑N₂ := rfl

@[simp, norm_cast]
lemma coe_inf (N₁ N₂ : PersistenceSubmodule M) : ⇑(N₁ ⊓ N₂) = ⇑N₁ ⊓ ⇑N₂ := rfl

lemma sup_apply (N₁ N₂ : PersistenceSubmodule M) (c : C) :
    (N₁ ⊔ N₂) c = N₁ c ⊔ N₂ c := rfl

lemma inf_apply (N₁ N₂ : PersistenceSubmodule M) (c : C) :
    (N₁ ⊓ N₂) c = N₁ c ⊓ N₂ c := rfl

/-- There's a notion of the supremum of two submodules, given by `⊕`,
and a notion of an infimum, given by `∩`. -/
instance : Lattice (PersistenceSubmodule M) :=
  DFunLike.coe_injective.lattice _ coe_sup coe_inf

/-- There's a notion of a minimal persistence submodule, namely `0`. -/
instance : OrderBot (PersistenceSubmodule M) where
  bot := {
    toFun := ⊥
    map_le' := by simp }
  bot_le N c := bot_le

/-- There's a notion of a maximal persistence submodule, namely `M`. -/
instance : OrderTop (PersistenceSubmodule M) where
  top := {
    toFun := ⊤
    map_le' := by simp }
  le_top N c := le_top

@[simp, norm_cast]
lemma coe_top : ⇑(⊤ : PersistenceSubmodule M) = ⊤ := rfl

@[simp, norm_cast]
lemma coe_bot : ⇑(⊥ : PersistenceSubmodule M) = ⊥ := rfl

lemma top_apply (c : C) : (⊤ : PersistenceSubmodule M) c = ⊤ := rfl

lemma bot_apply (c : C) : (⊥ : PersistenceSubmodule M) c = ⊥ := rfl


-- There's a notion of supremum over arbitrary sets of submodules
@[simp]
instance : SupSet (PersistenceSubmodule M) where
  sSup S := {
    -- The direct sum over arbitrary sets is just the pointwise direct sum
    toFun := fun x => sSup {(N  x) | (N : PersistenceSubmodule M) (_ : N ∈ S)}
    map_le' := by
      intro x y f
      rw [Submodule.map_sSup]
      sorry }


-- There's a notion of infimums over arbitrary sets of submodules
@[simp]
instance : InfSet (PersistenceSubmodule M) where
  sInf S := {
    -- The intersection over arbitrary sets is just the pointwise direct sum
    toFun := fun c ↦ sInf {N c | (N : PersistenceSubmodule M) (_ : N ∈ S)}
    map_le' := by
      intro x y f
      apply le_trans (Submodule.map_sInf _ _)
      apply sInf_le
      -- Here we're using the compatibility condition on submodules
      sorry }


-- If S is a set of PersistenceSubmodule, then ⨆ (p : S), (p.val  X) = (⨆ (p : S), p.val)  X
-- In other words, we can take Sup and toFun in whichever order we want.
lemma iSup_apply {ι : Sort*} (f : ι → PersistenceSubmodule M) (c : C) :
    (⨆ i, f i) c = ⨆ i, f i c := by
  apply eq_of_forall_ge_iff
  intro c
  simp
  sorry

lemma sSup_apply (S : Set (PersistenceSubmodule M)) (c : C) : (sSup S c) = ⨆ (N : S), N.val c := by
  rw [sSup_eq_iSup']
  exact iSup_apply ..


-- The sups and infs over possibly infinite sets are compatible with the lattice structure
instance : CompleteLattice (PersistenceSubmodule M) where
  le_sSup S A h_mem X := by
    -- maybe write some API to get rid of these annoying sSups without
    -- resorting to the simp nuke?
    simp
    let A' : {x | ∃ N ∈ S, N  X = x} := ⟨A  X, by simp; use A⟩
    apply le_sSup_of_le (A'.prop) (by simp)
  sSup_le S A h_le X := by
    simp
    intro a h_mem_a
    sorry
    --exact h_le
  sInf_le S A h_mem X := by
    simp
    let A' : {x | ∃ N ∈ S, N  X = x} := ⟨A  X, by simp; use A⟩
    apply sInf_le_of_le A'.prop
    rfl
  le_sInf S A h_le X := by
    simp
    intro a h_mem_a
    sorry
    --exact h_le h_mem_a X
  le_top A X := le_top
  bot_le A X := bot_le

end PersistenceSubmodule
