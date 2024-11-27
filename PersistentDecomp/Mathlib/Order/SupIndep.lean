import Mathlib.Order.SupIndep

open CompleteLattice

variable {ι κ α : Type*} [CompleteLattice α] {f : ι → κ → α}

lemma Pi.iSupIndep_iff : iSupIndep f ↔ ∀ k, iSupIndep (f · k) := by
  simpa [iSupIndep, Pi.disjoint_iff] using forall_swap
