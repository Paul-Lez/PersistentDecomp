module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Preorder.Chain

/-!
# Chain helpers

This file contains small finite-subset facts for chains.
-/

public section

/-- A finite subset of a nonempty chain has a lower bound inside the chain. -/
lemma exists_finset_lower_bound {α : Type*} [Preorder α] {T : Set α}
    (hT : IsChain (fun x y ↦ x ≤ y) T) (hTne : T.Nonempty)
    (u : Finset T) : ∃ J : T, ∀ I ∈ u, J ≤ I := by
  classical
  induction u using Finset.induction with
  | empty =>
      rcases hTne with ⟨J, hJ⟩
      exact ⟨⟨J, hJ⟩, by simp⟩
  | insert I u hIu ih =>
      rcases ih with ⟨J, hJ⟩
      by_cases hIJ : I = J
      · refine ⟨J, ?_⟩
        intro K hK
        rw [Finset.mem_insert] at hK
        rcases hK with rfl | hK
        · simp [hIJ]
        · exact hJ K hK
      · have hvalne : I.val ≠ J.val := fun h ↦ hIJ (Subtype.ext h)
        rcases hT I.prop J.prop hvalne with hle | hle
        · refine ⟨I, ?_⟩
          intro K hK
          rw [Finset.mem_insert] at hK
          rcases hK with rfl | hK
          · exact le_rfl
          · exact hle.trans (hJ K hK)
        · refine ⟨J, ?_⟩
          intro K hK
          rw [Finset.mem_insert] at hK
          rcases hK with rfl | hK
          · exact hle
          · exact hJ K hK
