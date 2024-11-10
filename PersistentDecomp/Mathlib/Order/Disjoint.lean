import Mathlib.Order.Disjoint

theorem right_lt_sup_of_left_ne_bot {α : Type*} [SemilatticeSup α] [OrderBot α] {a b : α}
    (h : Disjoint a b) (ha : a ≠ ⊥) : b < a ⊔ b :=
  le_sup_right.lt_of_ne fun eq ↦ ha (le_bot_iff.mp <| h le_rfl <| sup_eq_right.mp eq.symm)
