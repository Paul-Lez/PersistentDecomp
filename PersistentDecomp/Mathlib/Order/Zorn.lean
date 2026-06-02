module

public import Mathlib.Order.Max
public import Mathlib.Order.Zorn

/-!
# Zorn helpers

This file contains small order-dual variants of the Zorn API used in the project.
-/

public section

/-- If every chain is bounded below, then there is a minimal element. -/
lemma zorn_le_of_bddBelow_chains {α : Type*} [Preorder α]
    (h : ∀ c : Set α, IsChain (fun x y ↦ x ≤ y) c → BddBelow c) :
    ∃ m : α, IsMin m := by
  have hz : ∃ m : αᵒᵈ, IsMax m := by
    apply zorn_le
    intro c hc
    rw [bddAbove_def]
    let c' : Set α := OrderDual.ofDual '' c
    have hc' : IsChain (fun x y : α ↦ x ≤ y) c' := by
      intro x hx y hy hxy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      have hxy' : x' ≠ y' := by
        intro h
        exact hxy (by simp [h])
      rcases hc hx' hy' hxy' with h | h
      · exact Or.inr (OrderDual.ofDual_le_ofDual.mpr h)
      · exact Or.inl (OrderDual.ofDual_le_ofDual.mpr h)
    rcases (bddBelow_def.mp (h c' hc')) with ⟨lb, hlb⟩
    refine ⟨OrderDual.toDual lb, ?_⟩
    intro y hy
    rw [OrderDual.le_toDual]
    exact hlb (OrderDual.ofDual y) ⟨y, hy, rfl⟩
  rcases hz with ⟨m, hm⟩
  exact ⟨OrderDual.ofDual m, (isMin_ofDual_iff (a := m)).2 hm⟩
