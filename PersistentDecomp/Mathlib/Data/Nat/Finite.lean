module

public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Finite bounded sets of naturals

This file contains small helpers for natural-valued bounded families.
-/

public section

/-- A bounded natural-valued family on a nonempty type attains a maximum value. -/
lemma exists_max_nat_of_bdd {ι : Type*} (hne : Nonempty ι) (f : ι → ℕ) {N : ℕ}
    (hbound : ∀ i, f i ≤ N) : ∃ j : ι, ∀ i : ι, f i ≤ f j := by
  classical
  have hfinite : (Set.range f).Finite := by
    refine (Set.finite_le_nat N).subset ?_
    rintro _ ⟨i, rfl⟩
    exact hbound i
  have hne_range : (Set.range f).Nonempty := hne.elim fun i => ⟨f i, i, rfl⟩
  rcases Set.exists_max_image (Set.range f) id hfinite hne_range with
    ⟨_, ⟨j, rfl⟩, hmax⟩
  exact ⟨j, fun i => hmax (f i) ⟨i, rfl⟩⟩
