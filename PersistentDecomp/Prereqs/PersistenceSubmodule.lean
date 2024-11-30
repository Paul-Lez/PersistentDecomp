import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Submodule.Range
import PersistentDecomp.Mathlib.Algebra.Module.Submodule.Map

/-!
# Persistence Submodules

In this file we define persistence submodules and we equip them with a complete lattice structure.
-/

open CategoryTheory

variable {C : Type} [Category C] {K : Type} [DivisionRing K] {M : C ⥤ ModuleCat K} {c d : C}

variable (M) in
/--A persistence submodule of a persistence module `M` is a family of submodules `N_c ≤ M_c`
indexed by `c : C` that is compatible with the transition maps of `M`, in the sense that for
all morphisms `c ⟶ d` in `C`, the induced morphism `M_c ⟶ M_d` sends `N_c` into `N_d`.-/
structure PersistenceSubmodule where
  toFun (c : C) : Submodule K (M.obj c)
  map_le' {c d : C} (f : c ⟶ d) : (toFun c).map (M.map f) ≤ toFun d

namespace PersistenceSubmodule

instance : DFunLike (PersistenceSubmodule M) C fun c ↦ Submodule K (M.obj c) where
  coe := toFun
  coe_injective' N₁ N₂ := by cases N₁; cases N₂; congr!

/-- The inclusion of the submodules `N c` and `N d` is compatible with the "transition" maps of the
functor `M`, i.e if we have `f : c ⟶ d` then the image of `N c` by `M f` lies in the submodule
`N d`. -/
lemma map_le (N : PersistenceSubmodule M) (f : c ⟶ d) : (N c).map (M.map f) ≤ N d := N.map_le' _

/--We can check equality of persistence modules pointwise-/
@[ext]
lemma ext {N₁ N₂ : PersistenceSubmodule M} (h : ∀ c, N₁ c = N₂ c) : N₁ = N₂ := DFunLike.ext _ _ h

/--Persistence submodules are ordered pointwise. -/
instance : PartialOrder (PersistenceSubmodule M) := PartialOrder.lift (⇑) DFunLike.coe_injective

/-- There is a notion of a maximum of two persistence submodules `N N'` , namely the
(pointwise) sum `c ↦ N_c + N'_c`-/
instance : Max (PersistenceSubmodule M) where
  max N₁ N₂ := {
    toFun := fun c ↦ N₁ c ⊔ N₂ c
    map_le' := by
      intro c d f
      rw [Submodule.map_sup]
      apply sup_le_sup (N₁.map_le f) (N₂.map_le f) }

/-- There is a notion of a maximum of two persistence submodules `N N'` , namely the
(pointwise) intersection `c ↦ N_c + N'_c`-/
instance : Min (PersistenceSubmodule M) where
  min N₁ N₂ := {
    toFun := fun c ↦ N₁ c ⊓ N₂ c
    map_le' := by
      intro c d f
      apply le_trans (Submodule.map_inf_le _)
        (inf_le_inf (N₁.map_le f) (N₂.map_le f)) }

@[simp, norm_cast] lemma coe_sup (N₁ N₂ : PersistenceSubmodule M) : ⇑(N₁ ⊔ N₂) = ⇑N₁ ⊔ ⇑N₂ := rfl
@[simp, norm_cast] lemma coe_inf (N₁ N₂ : PersistenceSubmodule M) : ⇑(N₁ ⊓ N₂) = ⇑N₁ ⊓ ⇑N₂ := rfl

lemma sup_apply (N₁ N₂ : PersistenceSubmodule M) (c : C) : (N₁ ⊔ N₂) c = N₁ c ⊔ N₂ c := rfl
lemma inf_apply (N₁ N₂ : PersistenceSubmodule M) (c : C) : (N₁ ⊓ N₂) c = N₁ c ⊓ N₂ c := rfl

/-- There's a notion of the supremum of two submodules, given by `+`,
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

@[simp, norm_cast] lemma coe_top : ⇑(⊤ : PersistenceSubmodule M) = ⊤ := rfl
@[simp, norm_cast] lemma coe_bot : ⇑(⊥ : PersistenceSubmodule M) = ⊥ := rfl

lemma top_apply (c : C) : (⊤ : PersistenceSubmodule M) c = ⊤ := rfl
lemma bot_apply (c : C) : (⊥ : PersistenceSubmodule M) c = ⊥ := rfl

/-- There's a notion of supremum over arbitrary sets of submodules. -/
instance : SupSet (PersistenceSubmodule M) where
  sSup S := {
    -- The direct sum over arbitrary sets is just the pointwise direct sum
    toFun := ⨆ N ∈ S, N
    map_le' := by
      intro c d f
      rw [iSup_apply, Submodule.map_iSup, iSup_le_iff]
      sorry }

/-- There's a notion of infimums over arbitrary sets of submodules. -/
instance : InfSet (PersistenceSubmodule M) where
  sInf S := {
    -- The intersection over arbitrary sets is just the pointwise direct sum
    toFun := ⨅ N ∈ S, N
    map_le' := by
      intro c d f
      apply le_trans (Submodule.map_sInf_le _ _)
      apply sInf_le
      -- Here we're using the compatibility condition on submodules
      sorry }

@[simp, norm_cast] lemma coe_sSup (S : Set (PersistenceSubmodule M)) : sSup S = ⨆ N ∈ S, ⇑N := rfl
@[simp, norm_cast] lemma coe_sInf (S : Set (PersistenceSubmodule M)) : sInf S = ⨅ N ∈ S, ⇑N := rfl

@[simp, norm_cast] lemma coe_iSup {ι : Sort*} (f : ι → PersistenceSubmodule M) :
    ⇑(⨆ i, f i) = ⨆ i, ⇑(f i) := by rw [iSup, coe_sSup]; simp [iSup_comm]

@[simp, norm_cast] lemma coe_iInf {ι : Sort*} (f : ι → PersistenceSubmodule M) :
    ⇑(⨅ i, f i) = ⨅ i, ⇑(f i) := by rw [iInf, coe_sInf]; simp [iInf_comm]

lemma sSup_apply (S : Set (PersistenceSubmodule M)) (c : C) : sSup S c = ⨆ N ∈ S, N c := by simp
lemma sInf_apply (S : Set (PersistenceSubmodule M)) (c : C) : sInf S c = ⨅ N ∈ S, N c := by simp

lemma iSup_apply {ι : Sort*} (f : ι → PersistenceSubmodule M) (c : C) :
    (⨆ i, f i) c = ⨆ i, f i c := by simp

lemma iInf_apply {ι : Sort*} (f : ι → PersistenceSubmodule M) (c : C) :
    (⨅ i, f i) c = ⨅ i, f i c := by simp

/-- The sups and infs over possibly infinite sets are compatible with the lattice structure -/
instance : CompleteLattice (PersistenceSubmodule M) :=
  DFunLike.coe_injective.completeLattice _ coe_sup coe_inf coe_sSup coe_sInf coe_top coe_bot

end PersistenceSubmodule
