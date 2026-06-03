module

public import Mathlib.Order.Atoms
public import Mathlib.Order.Max
public import Mathlib.Order.ModularLattice
public import Mathlib.Order.Partition.Basic
public import PersistentDecomp.Mathlib.Order.Disjoint
public import PersistentDecomp.Mathlib.Order.Partition.RefinementMap
public import PersistentDecomp.Mathlib.Order.SupIndep
public import PersistentDecomp.Prereqs.Indecomposable

/-!
# Extra API for order partitions

This file provides a generic order-theoretic version of the refinement construction used for
direct-sum decompositions. The main consequence is that each member of a minimal partition is
indecomposable; in a complemented modular lattice, this strengthens to being an atom.
-/

@[expose] public section

namespace Partition

variable {α : Type*} [CompleteLattice α] [IsModularLattice α] {s : α}

section Refinement

variable (P : Partition s)

/-- Replace each part of a partition by a supremum-independent family with the same supremum. -/
@[nolint unusedArguments]
def refinement (B : ∀ a ∈ P, Set α) (hB : ∀ a ha, a = sSup (B a ha))
    (hB' : ∀ a ha, _root_.sSupIndep (B a ha)) (hB'' : ∀ a ha, ⊥ ∉ B a ha) :
    Partition s where
  parts := ⋃ a, ⋃ ha, B a ha
  sSupIndep' := P.sSupIndep.iUnion₂ hB hB'
  bot_notMem' := bot_notMem_iUnion₂ hB''
  sSup_eq' := by
    simpa using (sSup_iUnion₂_eq_sSup (S := (P : Set α)) (B := B) hB).trans P.sSup_eq

/-- A local part is a member of the global refinement. -/
lemma mem_refinement (B : ∀ a ∈ P, Set α) (hB : ∀ a ha, a = sSup (B a ha))
    (hB' : ∀ a ha, _root_.sSupIndep (B a ha)) (hB'' : ∀ a ha, ⊥ ∉ B a ha)
    {a : α} (ha : a ∈ P) {x : α} (hx : x ∈ B a ha) :
    x ∈ P.refinement B hB hB' hB'' := by
  change x ∈ (⋃ a, ⋃ (ha : a ∈ P), B a ha : Set α)
  simp only [Set.mem_iUnion]
  exact ⟨a, ha, hx⟩

/-- The global refinement refines the original partition. -/
lemma refinement_le (B : ∀ a ∈ P, Set α) (hB : ∀ a ha, a = sSup (B a ha))
    (hB' : ∀ a ha, _root_.sSupIndep (B a ha)) (hB'' : ∀ a ha, ⊥ ∉ B a ha) :
    P.refinement B hB hB' hB'' ≤ P := by
  intro x hx
  change x ∈ (⋃ a, ⋃ (ha : a ∈ P), B a ha : Set α) at hx
  simp only [Set.mem_iUnion] at hx
  rcases hx with ⟨a, ha, hxB⟩
  exact ⟨a, ha, by rw [hB a ha]; exact le_sSup hxB⟩

/-- If a refinement has the same parts as `P`, every local refinement block is a singleton. -/
lemma eq_singleton_of_refinement_eq (B : ∀ a ∈ P, Set α)
    (hB : ∀ a ha, a = sSup (B a ha)) (hB' : ∀ a ha, _root_.sSupIndep (B a ha))
    (hB'' : ∀ a ha, ⊥ ∉ B a ha) (hEq : P.refinement B hB hB' hB'' = P)
    (a : α) (ha : a ∈ P) : B a ha = {a} := by
  have eq_of_mem {x : α} (hx : x ∈ B a ha) : x = a := by
    have hxP : x ∈ P := by
      simpa [hEq] using P.mem_refinement B hB hB' hB'' ha hx
    have hx_le_a : x ≤ a := by
      rw [hB a ha]
      exact le_sSup hx
    exact P.sSupIndep.eq_of_le_of_le (fun hx_bot ↦ P.bot_notMem (hx_bot ▸ hxP)) hxP ha
      le_rfl hx_le_a
  ext x
  refine ⟨?_, ?_⟩
  · intro hx
    rw [Set.mem_singleton_iff]
    exact eq_of_mem hx
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    by_contra ha_not
    have hB_empty : B a ha = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hy
      exact ha_not ((eq_of_mem hy).symm ▸ hy)
    have ha_bot : a = (⊥ : α) := by
      rw [hB a ha, hB_empty]
      exact sSup_empty
    exact P.bot_notMem (ha_bot ▸ ha)

/-- A genuinely nontrivial local refinement is a strict refinement of `P`. -/
lemma refinement_lt_of_exists_ne_singleton (B : ∀ a ∈ P, Set α)
    (hB : ∀ a ha, a = sSup (B a ha)) (hB' : ∀ a ha, _root_.sSupIndep (B a ha))
    (hB'' : ∀ a ha, ⊥ ∉ B a ha) (H : ∃ (a : α) (ha : a ∈ P), B a ha ≠ {a}) :
    P.refinement B hB hB' hB'' < P := by
  refine lt_of_le_of_ne (P.refinement_le B hB hB' hB'') ?_
  intro hEq
  rcases H with ⟨a, ha, hne⟩
  exact hne (P.eq_singleton_of_refinement_eq B hB hB' hB'' hEq a ha)

end Refinement

/-- A member of a minimal partition is indecomposable. -/
lemma indecomposable_of_mem_of_isMin (P : Partition s) {a : α} (ha : a ∈ P)
    (hmin : IsMin P) : Indecomposable a := by
  classical
  by_contra hNotIndecomp
  simp only [_root_.Indecomposable, not_forall, not_or] at hNotIndecomp
  obtain ⟨x, y, hxy, rfl, hx, hy⟩ := hNotIndecomp
  let B (a) (_ha : a ∈ P) : Set α := if a = x ⊔ y then {x, y} else {a}
  set Q : Partition s := P.refinement
    B
    (by
      intro a ha
      by_cases h : a = x ⊔ y
      · simp only [B, h, if_true, sSup_pair]
      · simp only [B, h, if_false, sSup_singleton])
    (by
      intro a ha
      by_cases h : a = x ⊔ y
      · simp only [B, if_pos h]
        have hxy_ne : x ≠ y := by
          intro h_eq
          exact hx (le_antisymm (hxy le_rfl (by rw [h_eq])) bot_le)
        exact (sSupIndep_pair hxy_ne).2 hxy
      · simpa only [B, if_neg h] using sSupIndep_singleton a)
    (by
      intro a ha
      by_cases h : a = x ⊔ y
      · simp only [B, if_pos h, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun hbot ↦ hx hbot.symm, fun hbot ↦ hy hbot.symm⟩
      · simp only [B, if_neg h, Set.mem_singleton_iff]
        intro hbot
        exact P.bot_notMem (hbot.symm ▸ ha))
  have contra : ¬ IsMin P := by
    rw [not_isMin_iff]
    refine ⟨Q, ?_⟩
    apply P.refinement_lt_of_exists_ne_singleton
    refine ⟨x ⊔ y, ha, ?_⟩
    simp only [B, if_true]
    exact pair_ne_singleton_sup_of_disjoint_of_right_ne_bot hxy hy
  exact contra hmin

/-- In a complemented modular lattice, a member of a minimal partition is an atom. -/
lemma isAtom_of_mem_of_isMin [ComplementedLattice α] (P : Partition s) {a : α} (ha : a ∈ P)
    (hmin : IsMin P) : IsAtom a := by
  rw [isAtom_iff_le_of_ge]
  refine ⟨P.ne_bot_of_mem ha, ?_⟩
  intro b hb hba
  obtain ⟨c, hc⟩ := exists_isCompl (⟨b, hba⟩ : Set.Iic a)
  obtain ⟨hbc, hsup⟩ := Set.Iic.isCompl_iff.mp hc
  rcases P.indecomposable_of_mem_of_isMin ha hmin hbc hsup with hb_bot | hc_bot
  · exact (hb hb_bot).elim
  · simpa [hc_bot] using hsup.symm.le

/- The order-dual convention, where larger partitions are finer refinements. -/
namespace MaxOrder

variable (α) in
/-- A partition ordered by reverse refinement. -/
abbrev Partition (s : α) :=
  (_root_.Partition s)ᵒᵈ

namespace Partition

/-- Forget the max-order convention. -/
abbrev toPartition (P : MaxOrder.Partition α s) : _root_.Partition s :=
  OrderDual.ofDual P

/-- Put a partition in the max-order convention. -/
abbrev ofPartition (P : _root_.Partition s) : MaxOrder.Partition α s :=
  OrderDual.toDual P

omit [IsModularLattice α] in
instance : SetLike (MaxOrder.Partition α s) α where
  coe P := (P.toPartition : Set α)
  coe_injective' _ _ h := OrderDual.ofDual_inj.mp (SetLike.coe_injective h)

omit [IsModularLattice α] in
@[ext]
lemma ext {P Q : MaxOrder.Partition α s} (h : ∀ a : α, a ∈ P ↔ a ∈ Q) : P = Q :=
  OrderDual.ofDual_inj.mp (SetLike.ext h)

omit [IsModularLattice α] in
lemma le_iff_toPartition_ge (P Q : MaxOrder.Partition α s) :
    P ≤ Q ↔ Q.toPartition ≤ P.toPartition :=
  Iff.rfl

omit [IsModularLattice α] in
lemma sSupIndep (P : MaxOrder.Partition α s) : _root_.sSupIndep (P : Set α) :=
  P.toPartition.sSupIndep

omit [IsModularLattice α] in
lemma sSup_eq (P : MaxOrder.Partition α s) : sSup (P : Set α) = s :=
  P.toPartition.sSup_eq

omit [IsModularLattice α] in
lemma bot_notMem (P : MaxOrder.Partition α s) : (⊥ : α) ∉ P :=
  P.toPartition.bot_notMem

omit [IsModularLattice α] in
lemma ne_bot_of_mem {P : MaxOrder.Partition α s} {a : α} (ha : a ∈ P) : a ≠ ⊥ :=
  P.toPartition.ne_bot_of_mem ha

section Refinement

variable {P : MaxOrder.Partition α s}

/-- The order-dual version of `Partition.refinement`. -/
@[nolint unusedArguments]
def refinement (B : ∀ a ∈ P, Set α) (hB : ∀ a ha, a = sSup (B a ha))
    (hB' : ∀ a ha, _root_.sSupIndep (B a ha)) (hB'' : ∀ a ha, ⊥ ∉ B a ha) :
    MaxOrder.Partition α s :=
  ofPartition <| P.toPartition.refinement B hB hB' hB''

/-- A local part is a member of the order-dual global refinement. -/
lemma mem_refinement (B : ∀ a ∈ P, Set α) (hB : ∀ a ha, a = sSup (B a ha))
    (hB' : ∀ a ha, _root_.sSupIndep (B a ha)) (hB'' : ∀ a ha, ⊥ ∉ B a ha)
    {a : α} (ha : a ∈ P) {x : α} (hx : x ∈ B a ha) :
    x ∈ refinement B hB hB' hB'' :=
  _root_.Partition.mem_refinement P.toPartition B hB hB' hB'' ha hx

/-- In the max-order convention, `P ≤ refinement ...`. -/
lemma refinement_le (B : ∀ a ∈ P, Set α) (hB : ∀ a ha, a = sSup (B a ha))
    (hB' : ∀ a ha, _root_.sSupIndep (B a ha)) (hB'' : ∀ a ha, ⊥ ∉ B a ha) :
    P ≤ refinement B hB hB' hB'' := by
  rw [le_iff_toPartition_ge]
  exact P.toPartition.refinement_le B hB hB' hB''

/-- If an order-dual refinement has the same parts, all local blocks are singletons. -/
lemma eq_singleton_of_refinement_eq (B : ∀ a ∈ P, Set α)
    (hB : ∀ a ha, a = sSup (B a ha)) (hB' : ∀ a ha, _root_.sSupIndep (B a ha))
    (hB'' : ∀ a ha, ⊥ ∉ B a ha) (hEq : refinement B hB hB' hB'' = P)
    (a : α) (ha : a ∈ P) : B a ha = {a} :=
  _root_.Partition.eq_singleton_of_refinement_eq P.toPartition B hB hB' hB''
    (by simpa [refinement, ofPartition] using congrArg OrderDual.ofDual hEq) a ha

/-- A genuinely nontrivial local refinement is strictly larger in the max-order convention. -/
lemma refinement_lt_of_exists_ne_singleton (B : ∀ a ∈ P, Set α)
    (hB : ∀ a ha, a = sSup (B a ha)) (hB' : ∀ a ha, _root_.sSupIndep (B a ha))
    (hB'' : ∀ a ha, ⊥ ∉ B a ha) (H : ∃ (a : α) (ha : a ∈ P), B a ha ≠ {a}) :
    P < refinement B hB hB' hB'' := by
  refine lt_of_le_of_ne (refinement_le B hB hB' hB'') ?_
  intro hEq
  rcases H with ⟨a, ha, hne⟩
  exact hne (eq_singleton_of_refinement_eq B hB hB' hB'' hEq.symm a ha)

/-- A member of a maximal partition in the max-order convention is indecomposable. -/
lemma indecomposable_of_mem_of_isMax (P : MaxOrder.Partition α s) {a : α} (ha : a ∈ P)
    (hmax : IsMax P) : Indecomposable a :=
  P.toPartition.indecomposable_of_mem_of_isMin ha ((isMin_ofDual_iff (a := P)).2 hmax)

/-- In a complemented modular lattice, a member of a max-order maximal partition is an atom. -/
lemma isAtom_of_mem_of_isMax [ComplementedLattice α] (P : MaxOrder.Partition α s) {a : α}
    (ha : a ∈ P) (hmax : IsMax P) : IsAtom a :=
  P.toPartition.isAtom_of_mem_of_isMin ha ((isMin_ofDual_iff (a := P)).2 hmax)

end Refinement

end Partition

end MaxOrder

end Partition
