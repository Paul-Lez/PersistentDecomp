module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import PersistentDecomp.DirectSumDecomposition.Basic
public import PersistentDecomp.Mathlib.Algebra.DirectSum.Basic

/-!
# Coordinates in a direct-sum decomposition

This file contains the fibrewise coordinate API for direct-sum decompositions.
The underlying direct-sum facts live in `PersistentDecomp.Mathlib.Algebra.DirectSum.Basic`.
-/

@[expose] public section

open CategoryTheory DirectSum

namespace DirectSumDecomposition

variable {C : Type} [Category.{0, 0} C] {K : Type} [DivisionRing K]
variable {M : C ⥤ ModuleCat K}

variable (D I J : DirectSumDecomposition M) [DecidableEq D] [DecidableEq I] [DecidableEq J]


/-- The coordinates of a vector in the direct sum decomposition `D`, at the object `c`. -/
noncomputable def fiberDecomp (c : C)
    (b : M.obj c) : ⨁ p : D, p.val c :=
  (D.isInternal c).decomposition b


lemma coeLinearMap_fiberDecomp (c : C)
    (b : M.obj c) :
    DirectSum.coeLinearMap (fun p : D => p.val c) (fiberDecomp D c b) = b :=
  (D.isInternal c).coeLinearMap_decomposition b

lemma fiberDecomp_sum (c : C)
    [DecidableEq (M.obj c)] (b : M.obj c) :
    DFinsupp.sum (fiberDecomp D c b) (fun _i x ↦ (x : M.obj c)) = b :=
  (D.isInternal c).decomposition_sum b

lemma fiberDecomp_support_linearIndependent (c : C)
    [DecidableEq (M.obj c)] (b : M.obj c) :
    LinearIndependent K
      (fun p : {p : D // p ∈ (fiberDecomp D c b).support} =>
        ((fiberDecomp D c b) p.val : M.obj c)) :=
  (D.isInternal c).decomposition_support_linearIndependent b

lemma fiberDecomp_support_card_le_finrank (c : C)
    [Module.Finite K (M.obj c)] [DecidableEq (M.obj c)] (b : M.obj c) :
    (fiberDecomp D c b).support.card ≤ Module.finrank K (M.obj c) :=
  (D.isInternal c).decomposition_support_card_le_finrank b

lemma fiberDecomp_ne_zero_of_mem_support (c : C)
    [DecidableEq (M.obj c)] (b : M.obj c) {p : D}
    (hp : p ∈ (fiberDecomp D c b).support) :
    ((fiberDecomp D c b) p : M.obj c) ≠ 0 := by
  intro hx
  have hpzero : (fiberDecomp D c b) p = 0 := by
    ext
    exact hx
  exact ((DFinsupp.mem_support_toFun (fiberDecomp D c b) p).mp hp) hpzero

open scoped Classical in
lemma existsUnique_summand_contains_fiberDecomp (D : DirectSumDecomposition M) (c : C)
    [DecidableEq (M.obj c)] (b : M.obj c) {p : D}
    (hp : p ∈ (fiberDecomp D c b).support) :
    ∃! q : D, ((fiberDecomp D c b) p : M.obj c) ∈ q.val c := by
  have hx_ne := fiberDecomp_ne_zero_of_mem_support D c b hp
  refine ⟨p, (fiberDecomp D c b p).prop, ?_⟩
  intro q hq
  exact (DirectSum.IsInternal.eq_of_mem_of_mem_of_ne_zero (D.isInternal c)
    (fiberDecomp D c b p).prop hq hx_ne).symm

open scoped Classical in
lemma existsUnique_summand_contains_fiberDecomp_of_refinement
    (I J : DirectSumDecomposition M) (h : J ≤ I) (c : C)
    [DecidableEq (M.obj c)] (b : M.obj c) {p : J}
    (hp : p ∈ (fiberDecomp J c b).support) :
    ∃! q : I, ((fiberDecomp J c b) p : M.obj c) ∈ q.val c := by
  have hx_ne := fiberDecomp_ne_zero_of_mem_support J c b hp
  let q : I := refinementMap I J h p
  have hxq : ((fiberDecomp J c b) p : M.obj c) ∈ q.val c :=
    (refinementMap_le I J h p c) (fiberDecomp J c b p).prop
  refine ⟨q, hxq, ?_⟩
  intro r hr
  exact (DirectSum.IsInternal.eq_of_mem_of_mem_of_ne_zero (I.isInternal c) hxq hr hx_ne).symm

lemma exists_support_preimage_of_refinement
    (h : J ≤ I) (c : C) [DecidableEq (M.obj c)] (b : M.obj c) {A : I}
    (hA : A ∈ (fiberDecomp I c b).support) :
    ∃ N : J, N ∈ (fiberDecomp J c b).support ∧ refinementMap I J h N = A := by
  let hle : ∀ N : J, N.val c ≤ (refinementMap I J h N).val c :=
    fun N => (refinementMap_le I J h N) c
  have hcoarsen :
      DirectSum.coarsen (A := fun A : I => A.val c) (B := fun N : J => N.val c)
          (refinementMap I J h) hle (fiberDecomp J c b) = fiberDecomp I c b :=
    DirectSum.coarsen_eq_of_coeLinearMap_eq
      (A := fun A : I => A.val c) (B := fun N : J => N.val c)
      (I.isInternal c) (refinementMap I J h) hle
      (x := fiberDecomp J c b) (y := fiberDecomp I c b)
      (by rw [coeLinearMap_fiberDecomp J c b, coeLinearMap_fiberDecomp I c b])
  exact DirectSum.exists_support_preimage_of_coarsen_apply_ne_zero
    (A := fun A : I => A.val c) (B := fun N : J => N.val c)
    (refinementMap I J h) hle (fiberDecomp J c b) (by
      rw [hcoarsen]
      exact (DFinsupp.mem_support_toFun (fiberDecomp I c b) A).mp hA)

lemma support_mapsTo_of_refinement (h : J ≤ I)
    (c : C) [DecidableEq (M.obj c)] (b : M.obj c) :
    Set.MapsTo (refinementMap I J h)
      ((fiberDecomp J c b).support : Set J) ((fiberDecomp I c b).support : Set I) := by
  let hle : ∀ N : J, N.val c ≤ (refinementMap I J h N).val c :=
    fun N => (refinementMap_le I J h N) c
  have hcoarsen :
      DirectSum.coarsen (A := fun A : I => A.val c) (B := fun N : J => N.val c)
          (refinementMap I J h) hle (fiberDecomp J c b) = fiberDecomp I c b :=
    DirectSum.coarsen_eq_of_coeLinearMap_eq
      (A := fun A : I => A.val c) (B := fun N : J => N.val c)
      (I.isInternal c) (refinementMap I J h) hle
      (x := fiberDecomp J c b) (y := fiberDecomp I c b)
      (by rw [coeLinearMap_fiberDecomp J c b, coeLinearMap_fiberDecomp I c b])
  have hmaps := DirectSum.IsInternal.support_mapsTo_coarsen
    (A := fun A : I => A.val c) (B := fun N : J => N.val c)
    (J.isInternal c) (refinementMap I J h) hle (fiberDecomp J c b)
  intro N hN
  simpa [hcoarsen] using hmaps hN

lemma support_injOn_of_refinement_of_card_le
    (h : I ≤ J) (c : C) [DecidableEq (M.obj c)] (b : M.obj c)
    (hcard : (fiberDecomp I c b).support.card ≤ (fiberDecomp J c b).support.card) :
    Set.InjOn (refinementMap J I h) ((fiberDecomp I c b).support : Set I) := by
  exact Finset.injOn_of_surjOn_of_card_le (refinementMap J I h)
    (support_mapsTo_of_refinement J I h c b)
    (fun A hA => exists_support_preimage_of_refinement J I h c b hA)
    hcard

lemma existsUnique_summand_contains_fiberDecomp_of_refinement_of_card_le
    (h : I ≤ J) (c : C)
    [DecidableEq (M.obj c)] (b : M.obj c)
    (hcard : (fiberDecomp I c b).support.card ≤ (fiberDecomp J c b).support.card)
    {p : J} (hp : p ∈ (fiberDecomp J c b).support) :
    ∃! q : I, ((fiberDecomp J c b) p : M.obj c) ∈ q.val c := by
  have hx_ne := fiberDecomp_ne_zero_of_mem_support J c b hp
  have huniq {q r : I}
      (hq : ((fiberDecomp J c b) p : M.obj c) ∈ q.val c)
      (hr : ((fiberDecomp J c b) p : M.obj c) ∈ r.val c) : q = r :=
    DirectSum.IsInternal.eq_of_mem_of_mem_of_ne_zero (I.isInternal c) hq hr hx_ne
  have hinj := support_injOn_of_refinement_of_card_le I J h c b hcard
  rcases exists_support_preimage_of_refinement J I h c b hp with
    ⟨q, hq_support, hq_map⟩
  have hfilter_eq : (fiberDecomp I c b).support.filter
      (fun Q ↦ refinementMap J I h Q = p) = {q} := by
    ext Q
    refine ⟨?_, ?_⟩
    · intro hQ
      have hQ_support : Q ∈ (fiberDecomp I c b).support :=
        (Finset.mem_filter.mp hQ).1
      have hQ_map : refinementMap J I h Q = p :=
        (Finset.mem_filter.mp hQ).2
      have : Q = q := hinj hQ_support hq_support (by rw [hQ_map, hq_map])
      simp [this]
    · intro hQ
      rw [Finset.mem_singleton] at hQ
      subst Q
      exact Finset.mem_filter.mpr ⟨hq_support, hq_map⟩
  let hle : ∀ Q : I, Q.val c ≤ (refinementMap J I h Q).val c :=
    fun Q => (refinementMap_le J I h Q) c
  have hcoarsen :
      DirectSum.coarsen
          (A := fun A : J => A.val c) (B := fun Q : I => Q.val c)
          (refinementMap J I h) hle (fiberDecomp I c b) =
        fiberDecomp J c b :=
    DirectSum.coarsen_eq_of_coeLinearMap_eq
      (A := fun A : J => A.val c) (B := fun Q : I => Q.val c)
      (J.isInternal c) (refinementMap J I h) hle
      (x := fiberDecomp I c b) (y := fiberDecomp J c b)
      (by rw [coeLinearMap_fiberDecomp I c b, coeLinearMap_fiberDecomp J c b])
  have hsum :=
    DirectSum.coarsen_apply_coe
      (A := fun A : J => A.val c) (B := fun Q : I => Q.val c)
      (refinementMap J I h) hle (fiberDecomp I c b) p
  simp only [hcoarsen, hfilter_eq, Finset.sum_singleton] at hsum
  have hxq : ((fiberDecomp J c b) p : M.obj c) ∈ q.val c :=
    hsum.symm ▸ (fiberDecomp I c b q).prop
  refine ⟨q, hxq, ?_⟩
  intro r hr
  exact (huniq (q := q) (r := r) hxq hr).symm

end DirectSumDecomposition
