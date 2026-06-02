module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Order.Max
public import PersistentDecomp.Mathlib.Order.Disjoint
public import PersistentDecomp.Mathlib.Order.Partition.Basic
public import PersistentDecomp.Mathlib.Order.SupIndep
public import PersistentDecomp.Prereqs.Indecomposable
public import PersistentDecomp.Prereqs.PersistenceSubmodule

/-!
# Direct sum decompositions as partitions

This file gives the direct-sum-decomposition API used throughout the project. It defines the
underlying object as a `Partition` of the top persistence submodule. The refinement order is the
order from
`Partition`: `D₁ ≤ D₂` means every summand of `D₁` lies below a unique summand of `D₂`.

The namespace `MaxOrder` provides the order-dual version, matching the convention where a
decomposition is larger when it is a strict refinement.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum

variable {C : Type} [Category.{0, 0} C] {K : Type} [DivisionRing K]
variable {M : C ⥤ ModuleCat K}

variable (M) in
/-- A direct sum decomposition of `M` is a partition of the top persistence submodule. -/
abbrev DirectSumDecomposition :=
  Partition (⊤ : PersistenceSubmodule M)

namespace DirectSumDecomposition

lemma parts_sSupIndep (D : DirectSumDecomposition M) :
    sSupIndep (SetLike.coe D : Set (PersistenceSubmodule M)) :=
  Partition.sSupIndep D

lemma sSup_eq_top (D : DirectSumDecomposition M) :
    sSup (SetLike.coe D : Set (PersistenceSubmodule M)) = ⊤ :=
  Partition.sSup_eq D

lemma bot_notMem (D : DirectSumDecomposition M) :
    (⊥ : PersistenceSubmodule M) ∉ D :=
  Partition.bot_notMem D

lemma ne_bot_of_mem {D : DirectSumDecomposition M} {N : PersistenceSubmodule M}
    (hN : N ∈ D) : N ≠ ⊥ :=
  Partition.ne_bot_of_mem hN

lemma pointwise_iSup_eq_top (D : DirectSumDecomposition M) (x : C) :
    ⨆ p ∈ D, p x = ⊤ := by
  change ⨆ p ∈ (SetLike.coe D : Set (PersistenceSubmodule M)), p x = ⊤
  rw [← PersistenceSubmodule.sSup_apply (SetLike.coe D) x, D.sSup_eq_top]
  rfl

lemma pointwise_sSup_eq_top (D : DirectSumDecomposition M) (x : C) :
    ⨆ p ∈ D, p x = ⊤ :=
  pointwise_iSup_eq_top D x

lemma isInternal (D : DirectSumDecomposition M) [DecidableEq D] (c : C) :
    IsInternal (M := M.obj c) (S := Submodule K (M.obj c)) fun p : D ↦ p.val c := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_def]
    intro p
    have hglobal : Disjoint p.val (sSup (SetLike.coe D \ {p.val})) :=
      D.parts_sSupIndep p.prop
    have hpoint : Disjoint (p.val c) ((sSup (SetLike.coe D \ {p.val})) c) := by
      rw [disjoint_iff_inf_le] at hglobal ⊢
      exact hglobal c
    apply hpoint.mono_right
    rw [PersistenceSubmodule.sSup_apply]
    apply iSup_le
    intro q
    apply iSup_le
    intro hq
    refine le_iSup_of_le q.val (le_iSup_of_le ⟨q.prop, fun hqp => ?_⟩ le_rfl)
    exact hq (Subtype.ext (by simpa using hqp))
  · simpa [iSup_subtype] using pointwise_iSup_eq_top D c

/-- `D₁` is a refinement of `D₂` if every summand of `D₁` lies in a summand of `D₂`. -/
def IsRefinement (D₁ D₂ : DirectSumDecomposition M) : Prop :=
  D₁ ≤ D₂

lemma isRefinement_iff_le {D₁ D₂ : DirectSumDecomposition M} :
    IsRefinement D₁ D₂ ↔ D₁ ≤ D₂ :=
  Iff.rfl

/-- A summand in a refinement lies below some summand of the coarser decomposition. -/
lemma exists_le_of_isRefinement (I J : DirectSumDecomposition M) (h : IsRefinement J I) :
    ∀ N : J, ∃ A : I, N.val ≤ A.val :=
  Partition.exists_le_of_refinement J I h

/-- If `J ≤ I`, a summand of `J` lies below a unique summand of `I`. -/
noncomputable def refinementMap (I J : DirectSumDecomposition M)
    (h : IsRefinement J I) : J → I :=
  Partition.refinementMap I J h

/-- `refinementMap` sends each summand to a summand containing it. -/
lemma refinementMap_le (I J : DirectSumDecomposition M) (h : IsRefinement J I) (N : J) :
    N.val ≤ (refinementMap I J h N).val :=
  Partition.refinementMap_le I J h N

/-- Two summands of `I` that both contain the same nonzero summand of `J` are equal. -/
lemma eq_of_le_of_le (I J : DirectSumDecomposition M) (N : J) (A B : I)
    (h : N.val ≤ A.val ∧ N.val ≤ B.val) : A = B :=
  Partition.eq_of_le_of_le I J N A B h

/-- A nonzero element with supremum `B` can lie below only a summand that occurs in `B`. -/
lemma mem_of_sSup_eq_of_le_of_ne_bot (D : DirectSumDecomposition M)
    {N A : PersistenceSubmodule M} {B : Set (PersistenceSubmodule M)}
    (hB : B ⊆ D) (hN : N = sSup B) (hNA : N ≤ A) (hA : A ∈ D) (hN_ne : N ≠ ⊥) :
    A ∈ B :=
  Partition.mem_of_sSup_eq_of_le_of_ne_bot D hB hN hNA hA hN_ne

/-- If `N ≤ A` for some summand `A : I`, then `refinementMap N = A`. -/
lemma refinementMap_eq_of_le (I J : DirectSumDecomposition M) (h : IsRefinement J I) (N : J)
    (A : I) (h_le : N.val ≤ A.val) : refinementMap I J h N = A :=
  Partition.refinementMap_eq_of_le I J h N A h_le

@[simp]
lemma refinementMap_self (I : DirectSumDecomposition M) (h : IsRefinement I I) (N : I) :
    refinementMap I I h N = N :=
  Partition.refinementMap_self I h N

/-- A lower summand is sent to the same containing summand as any summand above it. -/
lemma refinementMap_eq_refinementMap_of_le (I J : DirectSumDecomposition M) (h : IsRefinement J I)
    (N₁ N₂ : J) (h_le₁ : N₂.val ≤ (refinementMap I J h N₁).val) :
    refinementMap I J h N₂ = refinementMap I J h N₁ :=
  Partition.refinementMap_eq_refinementMap_of_le I J h N₁ N₂ h_le₁

/-- refinement maps compose. -/
lemma refinementMap_refinementMap (I J L : DirectSumDecomposition M)
    (hij : IsRefinement J I) (hjl : IsRefinement L J) (hil : IsRefinement L I) (N : L) :
    refinementMap I L hil N = refinementMap I J hij (refinementMap J L hjl N) :=
  Partition.refinementMap_refinementMap I J L hij hjl hil N

/-- Two mutually refining decompositions have the same summands. -/
lemma mem_of_mutual_refinement (I J : DirectSumDecomposition M)
    (hJI : IsRefinement J I) (hIJ : IsRefinement I J) {N : PersistenceSubmodule M}
    (hN : N ∈ J) : N ∈ I :=
  Partition.mem_of_mutual_refinement I J hJI hIJ hN

section Indecomposable

variable {D : DirectSumDecomposition M}

/-- Replace each summand of `D` by a supremum-independent family with the same supremum. -/
@[nolint unusedArguments]
def refinement (B : ∀ N ∈ D, Set (PersistenceSubmodule M))
    (hB : ∀ N hN, N = sSup (B N hN)) (hB' : ∀ N hN, sSupIndep (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) : DirectSumDecomposition M :=
  Partition.refinement D B hB hB' hB''

/-- A local summand is a member of the global refinement. -/
lemma mem_refinement (B : ∀ N ∈ D, Set (PersistenceSubmodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, sSupIndep (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) {N : PersistenceSubmodule M} (hN : N ∈ D)
    {x : PersistenceSubmodule M} (hx : x ∈ B N hN) : x ∈ refinement B hB hB' hB'' :=
  Partition.mem_refinement D B hB hB' hB'' hN hx

/-- The global refinement refines `D` in the `Partition` order. -/
lemma refinement_le (B : ∀ N ∈ D, Set (PersistenceSubmodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, sSupIndep (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) :
    refinement B hB hB' hB'' ≤ D :=
  Partition.refinement_le D B hB hB' hB''

/-- If a refinement has the same summands as `D`, every local refinement block is a singleton. -/
lemma eq_singleton_of_refinement_eq (B : ∀ N ∈ D, Set (PersistenceSubmodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, sSupIndep (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) (hEq : refinement B hB hB' hB'' = D)
    (N : PersistenceSubmodule M) (hN : N ∈ D) : B N hN = {N} :=
  Partition.eq_singleton_of_refinement_eq D B hB hB' hB'' hEq N hN

/-- A genuinely nontrivial local refinement is a strict refinement of `D`. -/
lemma refinement_lt_of_exists_ne_singleton (B : ∀ N ∈ D, Set (PersistenceSubmodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, sSupIndep (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN)
    (H : ∃ (N : PersistenceSubmodule M) (hN : N ∈ D), B N hN ≠ {N}) :
    refinement B hB hB' hB'' < D :=
  Partition.refinement_lt_of_exists_ne_singleton D B hB hB' hB'' H

/-- A summand of a minimal direct sum decomposition is indecomposable. -/
lemma indecomposable_of_mem_of_isMin (D : DirectSumDecomposition M)
    (N : PersistenceSubmodule M) (hN : N ∈ D) (hmin : IsMin D) :
    Indecomposable N :=
  Partition.indecomposable_of_mem_of_isMin D hN hmin

/-- In a complemented lattice of persistence submodules, a summand of a minimal direct sum
decomposition is an atom. -/
lemma isAtom_of_mem_of_isMin [ComplementedLattice (PersistenceSubmodule M)]
    (D : DirectSumDecomposition M) (N : PersistenceSubmodule M) (hN : N ∈ D)
    (hmin : IsMin D) : IsAtom N :=
  Partition.isAtom_of_mem_of_isMin D hN hmin

end Indecomposable

end DirectSumDecomposition

/- The order-dual convention, where larger decompositions are finer refinements. -/
namespace MaxOrder

variable (M) in
abbrev DirectSumDecomposition :=
  (_root_.DirectSumDecomposition M)ᵒᵈ

namespace DirectSumDecomposition

abbrev toPartition (D : DirectSumDecomposition M) :
    _root_.DirectSumDecomposition M :=
  OrderDual.ofDual D

abbrev ofPartition (D : _root_.DirectSumDecomposition M) :
    DirectSumDecomposition M :=
  OrderDual.toDual D

instance : SetLike (DirectSumDecomposition M) (PersistenceSubmodule M) where
  coe D := (D.toPartition : Set (PersistenceSubmodule M))
  coe_injective' _ _ h := OrderDual.ofDual_inj.mp (SetLike.coe_injective h)

@[ext]
lemma ext {D E : DirectSumDecomposition M}
    (h : ∀ N : PersistenceSubmodule M, N ∈ D ↔ N ∈ E) : D = E :=
  OrderDual.ofDual_inj.mp (SetLike.ext h)

lemma le_iff_toPartition_ge (D E : DirectSumDecomposition M) :
    D ≤ E ↔ E.toPartition ≤ D.toPartition :=
  Iff.rfl

lemma parts_sSupIndep (D : DirectSumDecomposition M) :
    sSupIndep (SetLike.coe D : Set (PersistenceSubmodule M)) :=
  D.toPartition.parts_sSupIndep

lemma sSup_eq_top (D : DirectSumDecomposition M) :
    sSup (SetLike.coe D : Set (PersistenceSubmodule M)) = ⊤ :=
  D.toPartition.sSup_eq_top

lemma bot_notMem (D : DirectSumDecomposition M) :
    (⊥ : PersistenceSubmodule M) ∉ D :=
  D.toPartition.bot_notMem

lemma pointwise_iSup_eq_top (D : DirectSumDecomposition M) (x : C) :
    ⨆ p ∈ D, p x = ⊤ :=
  D.toPartition.pointwise_iSup_eq_top x

lemma pointwise_sSup_eq_top (D : DirectSumDecomposition M) (x : C) :
    ⨆ p ∈ D, p x = ⊤ :=
  pointwise_iSup_eq_top D x

open scoped Classical in
lemma isInternal (D : DirectSumDecomposition M) (c : C) :
    IsInternal (M := M.obj c) (S := Submodule K (M.obj c)) fun p : D ↦ p.val c := by
  change IsInternal (M := M.obj c) (S := Submodule K (M.obj c))
    fun p : D.toPartition ↦ p.val c
  exact D.toPartition.isInternal c

section Indecomposable

variable {D : DirectSumDecomposition M}

/-- The order-dual version of `DirectSumDecomposition.refinement`. -/
@[nolint unusedArguments]
def refinement (B : ∀ N ∈ D, Set (PersistenceSubmodule M))
    (hB : ∀ N hN, N = sSup (B N hN)) (hB' : ∀ N hN, sSupIndep (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) : DirectSumDecomposition M :=
  Partition.MaxOrder.Partition.refinement (P := D) B hB hB' hB''

/-- A local summand is a member of the order-dual global refinement. -/
lemma mem_refinement (B : ∀ N ∈ D, Set (PersistenceSubmodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, sSupIndep (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) {N : PersistenceSubmodule M} (hN : N ∈ D)
    {x : PersistenceSubmodule M} (hx : x ∈ B N hN) : x ∈ refinement B hB hB' hB'' :=
  Partition.MaxOrder.Partition.mem_refinement (P := D) B hB hB' hB'' hN hx

/-- In the max-order convention, `D ≤ refinement ...`. -/
lemma refinement_le (B : ∀ N ∈ D, Set (PersistenceSubmodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, sSupIndep (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) :
    D ≤ refinement B hB hB' hB'' :=
  Partition.MaxOrder.Partition.refinement_le (P := D) B hB hB' hB''

/-- If an order-dual refinement has the same summands, all local blocks are singletons. -/
lemma eq_singleton_of_refinement_eq (B : ∀ N ∈ D, Set (PersistenceSubmodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, sSupIndep (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) (hEq : refinement B hB hB' hB'' = D)
    (N : PersistenceSubmodule M) (hN : N ∈ D) : B N hN = {N} :=
  Partition.MaxOrder.Partition.eq_singleton_of_refinement_eq
    (P := D) B hB hB' hB'' hEq N hN

/-- A genuinely nontrivial local refinement is strictly larger in the max-order convention. -/
lemma refinement_lt_of_exists_ne_singleton (B : ∀ N ∈ D, Set (PersistenceSubmodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, sSupIndep (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN)
    (H : ∃ (N : PersistenceSubmodule M) (hN : N ∈ D), B N hN ≠ {N}) :
    D < refinement B hB hB' hB'' :=
  Partition.MaxOrder.Partition.refinement_lt_of_exists_ne_singleton
    (P := D) B hB hB' hB'' H

/-- A summand of a maximal direct sum decomposition is indecomposable. -/
lemma indecomposable_of_mem_of_isMax (D : DirectSumDecomposition M)
    (N : PersistenceSubmodule M) (hN : N ∈ D) (hmax : IsMax D) :
    Indecomposable N :=
  Partition.MaxOrder.Partition.indecomposable_of_mem_of_isMax D hN hmax

/-- In a complemented lattice of persistence submodules, a summand of a maximal direct sum
decomposition is an atom. -/
lemma isAtom_of_mem_of_isMax [ComplementedLattice (PersistenceSubmodule M)]
    (D : DirectSumDecomposition M) (N : PersistenceSubmodule M) (hN : N ∈ D)
    (hmax : IsMax D) : IsAtom N :=
  Partition.MaxOrder.Partition.isAtom_of_mem_of_isMax D hN hmax

end Indecomposable

end DirectSumDecomposition

end MaxOrder
