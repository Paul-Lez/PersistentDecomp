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
