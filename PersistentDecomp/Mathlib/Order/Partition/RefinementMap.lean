module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Order.Partition.Basic
public import PersistentDecomp.Mathlib.Order.SupIndep

/-!
# Refinement maps for order partitions

This file collects API for the canonical map from a finer partition to a coarser partition.
-/

@[expose] public section

open CategoryTheory

namespace Partition

variable {α : Type*} [CompleteLattice α] {s : α}

/-- A part in a refinement lies below some part of the coarser partition. -/
lemma exists_le_of_refinement (P Q : Partition s) (h : P ≤ Q) :
    ∀ a : P, ∃ b : Q, a.val ≤ b.val := by
  intro a
  rcases exists_le_of_mem_le h a.prop with ⟨b, hb, hab⟩
  exact ⟨⟨b, hb⟩, hab⟩

/-- If `P ≤ Q`, send each part of `P` to the unique part of `Q` containing it. -/
noncomputable def refinementMap (Q P : Partition s) (h : P ≤ Q) : P → Q :=
  fun a ↦
    ⟨Classical.choose (existsUnique_of_mem_le h a.prop),
      (Classical.choose_spec (existsUnique_of_mem_le h a.prop)).1.1⟩

/-- `refinementMap` sends each part to a part containing it. -/
lemma refinementMap_le (Q P : Partition s) (h : P ≤ Q) (a : P) :
    a.val ≤ (refinementMap Q P h a).val :=
  (Classical.choose_spec (existsUnique_of_mem_le h a.prop)).1.2

/-- Two parts of `Q` that both contain the same nonzero part of `P` are equal. -/
lemma eq_of_le_of_le (Q P : Partition s) (a : P) (b c : Q)
    (h : a.val ≤ b.val ∧ a.val ≤ c.val) : b = c :=
  Subtype.ext <| Q.sSupIndep.eq_of_le_of_le
    (fun hbot ↦ P.bot_notMem (hbot ▸ a.prop)) b.prop c.prop h.1 h.2

/-- A nonzero element with supremum `B` can lie below only a part that occurs in `B`. -/
lemma mem_of_sSup_eq_of_le_of_ne_bot (P : Partition s) {a b : α} {B : Set α}
    (hB : B ⊆ P) (ha : a = sSup B) (hab : a ≤ b) (hb : b ∈ P) (ha_ne : a ≠ ⊥) :
    b ∈ B :=
  P.sSupIndep.mem_of_sSup_eq_of_le_of_ne_bot hB ha hab hb ha_ne

/-- If `a ≤ b` for some part `b : Q`, then `refinementMap a = b`. -/
lemma refinementMap_eq_of_le (Q P : Partition s) (h : P ≤ Q) (a : P) (b : Q)
    (hab : a.val ≤ b.val) : refinementMap Q P h a = b :=
  Subtype.ext <| ((Classical.choose_spec (existsUnique_of_mem_le h a.prop)).2
    b.val ⟨b.prop, hab⟩).symm

@[simp]
lemma refinementMap_self (P : Partition s) (h : P ≤ P) (a : P) :
    refinementMap P P h a = a :=
  refinementMap_eq_of_le P P h a a le_rfl

/-- A lower part is sent to the same containing part as any part above it. -/
lemma refinementMap_eq_refinementMap_of_le (Q P : Partition s) (h : P ≤ Q)
    (a b : P) (hb_le : b.val ≤ (refinementMap Q P h a).val) :
    refinementMap Q P h b = refinementMap Q P h a :=
  (eq_of_le_of_le Q P b (refinementMap Q P h a) (refinementMap Q P h b)
    ⟨hb_le, refinementMap_le Q P h b⟩).symm

/-- Refinement maps compose. -/
lemma refinementMap_refinementMap (P Q R : Partition s)
    (hPQ : Q ≤ P) (hQR : R ≤ Q) (hPR : R ≤ P) (a : R) :
    refinementMap P R hPR a = refinementMap P Q hPQ (refinementMap Q R hQR a) :=
  refinementMap_eq_of_le P R hPR a (refinementMap P Q hPQ (refinementMap Q R hQR a)) <|
    (refinementMap_le Q R hQR a).trans
      (refinementMap_le P Q hPQ (refinementMap Q R hQR a))

/-- Two mutually refining partitions have the same parts. -/
lemma mem_of_mutual_refinement (P Q : Partition s) (hQP : Q ≤ P) (hPQ : P ≤ Q) {a : α}
    (ha : a ∈ Q) : a ∈ P := by
  simpa [le_antisymm hPQ hQP] using ha

/-- The functor sending a partition to its type of parts, with maps induced by refinement. -/
noncomputable def toTypeCat : Partition s ⥤ Type _ where
  obj P := P
  map {P Q} f := refinementMap Q P (leOfHom f)
  map_comp {P Q R} f g := by
    ext a : 2
    simpa using refinementMap_refinementMap R Q P (leOfHom g) (leOfHom f)
      (leOfHom (f ≫ g)) a

/-- The restriction of `Partition.toTypeCat` to a set of partitions. -/
noncomputable def toTypeCatOn (T : Set (Partition s)) : T ⥤ Type _ where
  obj P := P.val
  map {P Q} f := refinementMap Q.val P.val (leOfHom f)
  map_comp {P Q R} f g := by
    ext a : 2
    simpa using refinementMap_refinementMap R.val Q.val P.val (leOfHom g) (leOfHom f)
      (leOfHom (f ≫ g)) a

end Partition
