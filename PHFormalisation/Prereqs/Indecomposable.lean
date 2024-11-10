import Mathlib.Order.Disjoint

variable {α : Type*} [Lattice α] [OrderBot α]

/-- An element in a lattice is indecomposable if it cannot be written as the supremum of disjoint
non-bot elements. -/
def Indecomposable (a : α) : Prop := ∀ ⦃b c⦄, Disjoint b c → b ⊔ c = a → b = ⊥ ∨ c = ⊥

lemma Indecomposable.bot : Indecomposable (⊥ : α) := fun _ ↦ by aesop
