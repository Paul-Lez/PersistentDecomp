module

public import Mathlib.Order.Disjoint
public import Mathlib.Data.Set.Insert

public section

/-- Symmetric form of `Disjoint.right_lt_sup_of_left_ne_bot`. -/
theorem left_lt_sup_of_right_ne_bot {α : Type*} [SemilatticeSup α] [OrderBot α] {a b : α}
    (h : Disjoint a b) (hb : b ≠ ⊥) : a < a ⊔ b := by
  simpa [sup_comm] using Disjoint.right_lt_sup_of_left_ne_bot h.symm hb

/-- If `a` and `b` are disjoint and `b` is nonzero, then `{a, b}` is not the singleton
`{a ⊔ b}`. -/
theorem pair_ne_singleton_sup_of_disjoint_of_right_ne_bot {α : Type*} [SemilatticeSup α]
    [OrderBot α] {a b : α} (h : Disjoint a b) (hb : b ≠ ⊥) :
    ({a, b} : Set α) ≠ {a ⊔ b} := by
  intro hset
  have ha_mem : a ∈ ({a ⊔ b} : Set α) := by
    rw [← hset]
    simp
  exact (left_lt_sup_of_right_ne_bot h hb).ne (Set.mem_singleton_iff.mp ha_mem)
