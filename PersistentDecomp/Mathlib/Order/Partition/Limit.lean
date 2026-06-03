module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import PersistentDecomp.Mathlib.Order.Partition.RefinementMap

/-!
# Limits of partition refinements

This file contains helpers for constructing elements of limits of the Type-valued diagram
associated to a family of partitions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Partition

variable {α : Type*} [CompleteLattice α] {s : α}

/-- A monotone choice of one part from each partition determines a point in the limit of the
associated Type-valued refinement diagram. -/
noncomputable def limitMkOfMonotone (T : Set (Partition s))
    (f : T → α) (h_le : ∀ I J : T, I ≤ J → f I ≤ f J)
    (h_mem : ∀ I : T, f I ∈ I.val) : limit (toTypeCatOn T) := by
  let f' : (I : T) → (toTypeCatOn T).obj I := by
    intro I
    exact ⟨f I, h_mem I⟩
  have h_compatible : ∀ (I J : T) (g : I ⟶ J), (toTypeCatOn T).map g (f' I) = f' J := by
    intro I J g
    have hIJ := leOfHom g
    have hmap : refinementMap J.val I.val hIJ ⟨f I, h_mem I⟩ = ⟨f J, h_mem J⟩ :=
      refinementMap_eq_of_le J.val I.val hIJ ⟨f I, h_mem I⟩ ⟨f J, h_mem J⟩
        (h_le I J hIJ)
    simpa [toTypeCatOn, f'] using hmap
  exact Types.Limit.mk (toTypeCatOn T) f' h_compatible

@[simp]
lemma limit_π_limitMkOfMonotone (T : Set (Partition s))
    (f : T → α) (h_le : ∀ I J : T, I ≤ J → f I ≤ f J)
    (h_mem : ∀ I : T, f I ∈ I.val) (I : T) :
    limit.π (toTypeCatOn T) I (limitMkOfMonotone T f h_le h_mem) = ⟨f I, h_mem I⟩ := by
  simp [limitMkOfMonotone]

section Unique

variable {T : Set (Partition s)}
variable (p : (P : T) → P.val → Prop)
variable (hp : ∀ P : T, ∃! a : P.val, p P a)

/-- The uniquely chosen part satisfying a predicate in each partition. -/
noncomputable def chosenPart (P : T) : P.val :=
  Classical.choose (hp P)

/-- The chosen part satisfies the predicate. -/
lemma chosenPart_spec (P : T) : p P (chosenPart p hp P) :=
  (Classical.choose_spec (hp P)).1

/-- Any part satisfying the predicate is the chosen part. -/
lemma chosenPart_unique (P : T) {a : P.val} (ha : p P a) :
    a = chosenPart p hp P :=
  (Classical.choose_spec (hp P)).2 a ha

/-- If the predicate is preserved by refinement maps, the chosen parts are monotone along
refinements. -/
lemma chosenPart_mono
    (hmap : ∀ {P Q : T} (hPQ : P ≤ Q) (a : P.val),
      p P a → p Q (refinementMap Q.val P.val hPQ a))
    {P Q : T} (hPQ : P ≤ Q) :
    (chosenPart p hp P).val ≤ (chosenPart p hp Q).val := by
  have hEq : refinementMap Q.val P.val hPQ (chosenPart p hp P) =
      chosenPart p hp Q :=
    chosenPart_unique p hp Q (hmap hPQ (chosenPart p hp P) (chosenPart_spec p hp P))
  simpa [hEq] using refinementMap_le Q.val P.val hPQ (chosenPart p hp P)

/-- A compatible unique choice of parts determines a point in the limit of the refinement
diagram. -/
noncomputable def limitMkOfUnique
    (hmap : ∀ {P Q : T} (hPQ : P ≤ Q) (a : P.val),
      p P a → p Q (refinementMap Q.val P.val hPQ a)) :
    limit (toTypeCatOn T) :=
  limitMkOfMonotone T (fun P => (chosenPart p hp P).val)
    (fun _ _ hPQ => chosenPart_mono p hp hmap hPQ)
    (fun P => (chosenPart p hp P).prop)

@[simp]
lemma limit_π_limitMkOfUnique
    (hmap : ∀ {P Q : T} (hPQ : P ≤ Q) (a : P.val),
      p P a → p Q (refinementMap Q.val P.val hPQ a))
    (P : T) :
    limit.π (toTypeCatOn T) P (limitMkOfUnique p hp hmap) =
      chosenPart p hp P := by
  simp [limitMkOfUnique]

/-- The projection of `limitMkOfUnique` satisfies the predicate used to choose it. -/
lemma limitMkOfUnique_spec
    (hmap : ∀ {P Q : T} (hPQ : P ≤ Q) (a : P.val),
      p P a → p Q (refinementMap Q.val P.val hPQ a))
    (P : T) :
    p P (limit.π (toTypeCatOn T) P (limitMkOfUnique p hp hmap)) := by
  rw [limit_π_limitMkOfUnique p hp hmap P]
  exact chosenPart_spec p hp P

end Unique

end Partition
