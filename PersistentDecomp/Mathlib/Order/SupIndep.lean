import Mathlib.Order.SupIndep

open CompleteLattice

variable {ι κ α : Type*} [CompleteLattice α] {f : ι → κ → α}

lemma Pi.iSupIndepIndep_iff : Independent f ↔ ∀ k, Independent (f · k) := by
  simpa [Independent, Pi.disjoint_iff] using forall_swap
