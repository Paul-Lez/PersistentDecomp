module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace DirectSum
variable {ι M S : Type*} [DecidableEq ι] [AddCommGroup M] [SetLike S M] [AddSubgroupClass S M]
  {A : ι → S}

lemma isInternal_iff [DecidableEq M] :
    IsInternal A ↔
      (∀ x : ⨁ i, A i, x.sum (fun _i y ↦ (y : M)) = 0 → x = 0) ∧
        ∀ b : M, ∃ a : ⨁ i, A i, (DFinsupp.sum a fun _i x ↦ x) = b := by
  rw [DirectSum.IsInternal, Function.Bijective, Function.Surjective,
    ← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  simp [AddMonoidHom.mem_ker, DirectSum.coeAddMonoidHom_eq_dfinsuppSum]

set_option backward.isDefEq.respectTransparency false in
lemma IsInternal.eq_zero_of_subsingleton_preimage (hA : IsInternal A) {κ : Type*} (g : κ → ι)
    (f : κ → M) (s : Finset κ) (hg : (s : Set κ).InjOn g) (hfg : ∀ k, f k ∈ A (g k))
    (hf₀ : ∑ k ∈ s, f k = 0) {k : κ} (hk : k ∈ s) : f k = 0 := by
  classical
  letI := hA.chooseDecomposition
  have (k : κ) : decompose A (f k) = DirectSum.of (fun i ↦ A i) (g k) ⟨f k, hfg k⟩ :=
    (decompose A).symm.injective (by simp)
  have hf₀ := congr((decomposeAddEquiv A $hf₀ (g k)).1)
  simp only [map_sum, decomposeAddEquiv_apply,
    decompose_zero, zero_apply, ZeroMemClass.coe_zero] at hf₀
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single k] at hf₀
  · simpa [this] using hf₀
  · intros b hb hbk
    simp_rw [this, DirectSum.of_apply, dif_neg (hg.ne hb hk hbk)]
  · simp [hk]

end DirectSum

namespace DirectSum

variable {ι R M : Type*} [DecidableEq ι] [DivisionRing R] [AddCommGroup M] [Module R M]
  {A : ι → Submodule R M}

/-- In an internal direct sum, a nonzero vector belongs to at most one summand. -/
lemma IsInternal.eq_of_mem_of_mem_of_ne_zero (hA : IsInternal A) {i j : ι} {x : M}
    (hxi : x ∈ A i) (hxj : x ∈ A j) (hx : x ≠ 0) : i = j := by
  by_contra hne
  have hdisj : Disjoint (A i) (A j) := hA.submodule_iSupIndep.pairwiseDisjoint hne
  rw [disjoint_iff_inf_le] at hdisj
  exact hx (by simpa using hdisj ⟨hxi, hxj⟩)

/-- The coordinates of a vector with respect to an internal direct-sum decomposition. -/
noncomputable def IsInternal.decomposition (hA : IsInternal A) (b : M) : ⨁ i, A i :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i : ι => A i) hA).symm b

lemma IsInternal.coeLinearMap_decomposition (hA : IsInternal A) (b : M) :
    DirectSum.coeLinearMap (fun i : ι => A i) (hA.decomposition b) = b := by
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i : ι => A i) hA).apply_symm_apply b

lemma IsInternal.decomposition_sum (hA : IsInternal A) [DecidableEq M] (b : M) :
    DFinsupp.sum (hA.decomposition b) (fun _i x ↦ (x : M)) = b := by
  rw [← DirectSum.coeLinearMap_eq_dfinsuppSum]
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i : ι => A i) hA).apply_symm_apply b

lemma IsInternal.decomposition_support_linearIndependent (hA : IsInternal A) [DecidableEq M]
    (b : M) :
    LinearIndependent R
      (fun i : {i : ι // i ∈ (hA.decomposition b).support} =>
        ((hA.decomposition b) i.val : M)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hsum : DirectSum.coeLinearMap (fun i : ι => A i)
    (∑ j : {i : ι // i ∈ (hA.decomposition b).support}, DirectSum.of (fun i : ι => A i) j.val
      (g j • (hA.decomposition b j.val))) = 0 := by
    simpa [map_sum, hg]
  have hdsum : (∑ j : {i : ι // i ∈ (hA.decomposition b).support},
     DirectSum.of (fun i : ι => A i) j.val (g j • (hA.decomposition b j.val))) = 0 :=
    hA.injective hsum
  have hcoord := congrArg (fun x : ⨁ i, A i => x i.val) hdsum
  change ((∑ j : {i : ι // i ∈ (hA.decomposition b).support},
          DirectSum.of (fun i : ι => A i) j.val
            (g j • (hA.decomposition b j.val))) : Π₀ i, A i) i.val = 0 at hcoord
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single i, of_eq_same, smul_eq_zero] at hcoord
  · apply hcoord.resolve_right
    exact (DFinsupp.mem_support_toFun (hA.decomposition b) i.val).mp i.prop
  · intro j _ hji
    rw [DirectSum.of_eq_of_ne]
    exact fun h ↦ hji (Subtype.ext h.symm)
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

lemma IsInternal.decomposition_support_card_le_finrank [Module.Finite R M] (hA : IsInternal A)
    [DecidableEq M] (b : M) :
    (hA.decomposition b).support.card ≤ Module.finrank R M := by
  simpa using (hA.decomposition_support_linearIndependent b).fintype_card_le_finrank

end DirectSum

namespace DirectSum

variable {ι κ R V : Type*} [DecidableEq ι] [DecidableEq κ] [Ring R]
variable [AddCommMonoid V] [Module R V]
variable {A : ι → Submodule R V} {B : κ → Submodule R V}

/-- Coarsen a direct sum indexed by submodules `B k` into one indexed by submodules `A i`, along
a map `f : κ → ι` and inclusions `B k ≤ A (f k)`. -/
noncomputable def coarsen (f : κ → ι) (h : ∀ k, B k ≤ A (f k)) :
    (⨁ k, B k) →ₗ[R] ⨁ i, A i :=
  DirectSum.toModule R κ (⨁ i, A i) fun k =>
    (DirectSum.lof R ι (fun i : ι => A i) (f k)).comp (Submodule.inclusion (h k))

@[simp]
lemma coarsen_lof (f : κ → ι) (h : ∀ k, B k ≤ A (f k)) (k : κ) (x : B k) :
    coarsen (A := A) (B := B) f h
        (DirectSum.lof R κ (fun k : κ => B k) k x) =
      DirectSum.lof R ι (fun i : ι => A i) (f k) (Submodule.inclusion (h k) x) := by
  simp [coarsen]

lemma coeLinearMap_coarsen (f : κ → ι) (h : ∀ k, B k ≤ A (f k)) :
    (DirectSum.coeLinearMap A).comp (coarsen (A := A) (B := B) f h) =
      DirectSum.coeLinearMap B := by
  apply DirectSum.linearMap_ext
  intro k
  ext x
  simp [coarsen]

lemma coarsen_eq_of_coeLinearMap_eq (hA : IsInternal A) (f : κ → ι)
    (h : ∀ k, B k ≤ A (f k)) {x : ⨁ k, B k} {y : ⨁ i, A i}
    (hxy : DirectSum.coeLinearMap B x = DirectSum.coeLinearMap A y) :
    coarsen (A := A) (B := B) f h x = y := by
  apply hA.injective
  calc
    DirectSum.coeLinearMap A (coarsen (A := A) (B := B) f h x)
        = DirectSum.coeLinearMap B x := by
          simpa using congrFun
            (congrArg DFunLike.coe (coeLinearMap_coarsen f h)) x
    _ = DirectSum.coeLinearMap A y := hxy

lemma coarsen_apply_eq_zero_of_forall_support_ne [∀ k (x : B k), Decidable (x ≠ 0)]
    (f : κ → ι) (h : ∀ k, B k ≤ A (f k))
    (x : ⨁ k, B k) (i : ι) (hne : ∀ k ∈ x.support, f k ≠ i) :
    coarsen f h x i = 0 := by
  rw [← DirectSum.sum_support_of x, map_sum]
  change ((∑ k ∈ x.support,
    coarsen f h (DirectSum.of (fun k : κ => B k) k (x k))) : Π₀ i : ι, A i) i = 0
  rw [DFinsupp.finsetSum_apply]
  refine Finset.sum_eq_zero ?_
  intro k hk
  rw [← DirectSum.lof_eq_of (R := R), coarsen_lof, DirectSum.lof_eq_of (R := R),
    DirectSum.of_eq_of_ne]
  exact (hne k hk).symm

lemma exists_support_preimage_of_coarsen_apply_ne_zero
    [∀ k (x : B k), Decidable (x ≠ 0)]
    (f : κ → ι) (h : ∀ k, B k ≤ A (f k)) (x : ⨁ k, B k) {i : ι}
    (hi : coarsen (A := A) (B := B) f h x i ≠ 0) :
    ∃ k : κ, k ∈ x.support ∧ f k = i := by
  by_contra hnone
  push Not at hnone
  exact hi <| coarsen_apply_eq_zero_of_forall_support_ne
    (A := A) (B := B) f h x i hnone

lemma coarsen_of_apply_coe (f : κ → ι) (h : ∀ k, B k ≤ A (f k))
    (k : κ) (x : B k) (i : ι) :
    ((coarsen (A := A) (B := B) f h (DirectSum.of (fun k : κ => B k) k x) i :
      A i) : V) = if f k = i then (x : V) else 0 := by
  split_ifs with hki
  · subst i
    simp [← DirectSum.lof_eq_of (R := R), coarsen]
  · have hik : i ≠ f k := fun h' ↦ hki h'.symm
    have hzero : ((DirectSum.of (fun i : ι => A i) (f k)
        (Submodule.inclusion (h k) x)) i) = 0 :=
      DirectSum.of_eq_of_ne (β := fun i : ι => A i) (f k) i (Submodule.inclusion (h k) x) hik
    simpa [← DirectSum.lof_eq_of (R := R), coarsen, hki, hzero]

lemma coarsen_apply_coe [∀ k (x : B k), Decidable (x ≠ 0)]
    (f : κ → ι) (h : ∀ k, B k ≤ A (f k))
    (x : ⨁ k, B k) (i : ι) :
    ((coarsen (A := A) (B := B) f h x i : A i) : V) =
      ∑ k ∈ x.support.filter (fun k => f k = i), (x k : V) := by
  conv_lhs => rw [← DirectSum.sum_support_of x, map_sum]
  change (((∑ k ∈ x.support,
      coarsen (A := A) (B := B) f h
        (DirectSum.of (fun k : κ => B k) k (x k))) : Π₀ i : ι, A i) i : V) = _
  rw [DFinsupp.finsetSum_apply]
  change ((A i).subtype
      (∑ k ∈ x.support, ((coarsen (A := A) (B := B) f h)
        ((DirectSum.of (fun k : κ => B k) k) (x k))) i)) = _
  rw [map_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun k _hk => coarsen_of_apply_coe f h k (x k) i

end DirectSum

namespace DirectSum

variable {ι κ R V : Type*} [DecidableEq ι] [DecidableEq κ] [Ring R]
variable [AddCommGroup V] [Module R V]
variable {A : ι → Submodule R V} {B : κ → Submodule R V}

lemma IsInternal.support_mapsTo_coarsen [∀ i (x : A i), Decidable (x ≠ 0)]
    [∀ k (x : B k), Decidable (x ≠ 0)]
    (hB : IsInternal B) (f : κ → ι) (h : ∀ k, B k ≤ A (f k))
    (x : ⨁ k, B k) :
    Set.MapsTo f (x.support : Set κ)
      (((coarsen (ι := ι) (κ := κ) (R := R) (V := V) (A := A) (B := B) f h x :
          ⨁ i, A i).support : Finset ι) : Set ι) := by
  intro k hk
  by_contra hfk
  have hzero :  coarsen f h x (f k) = 0 := by
    by_contra hne
    exact hfk ((DFinsupp.mem_support_toFun (coarsen f h x) (f k)).mpr hne)
  have hsum := coarsen_apply_coe f h x (f k)
  simp [hzero] at hsum
  have hkfilter : k ∈ x.support.filter (fun j => f j = f k) :=
    Finset.mem_filter.mpr ⟨hk, rfl⟩
  have hkzeroM : ((x k : B k) : V) = 0 :=
    hB.eq_zero_of_subsingleton_preimage (fun j : κ => j)
      (fun j => (x j)) (x.support.filter (fun j => f j = f k)) (by simp)
      (fun j => (x j).prop) hsum.symm hkfilter
  have hkzero : x k = 0 := by
    ext
    exact hkzeroM
  exact ((DFinsupp.mem_support_toFun x k).mp hk) hkzero

end DirectSum
