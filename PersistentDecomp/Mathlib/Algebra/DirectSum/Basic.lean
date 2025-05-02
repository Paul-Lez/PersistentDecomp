import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Group.Subgroup.Basic

namespace DirectSum
variable {ι M S : Type*} [DecidableEq ι] [AddCommGroup M] [SetLike S M] [AddSubgroupClass S M]
  {A : ι → S}

lemma isInternal_iff [DecidableEq M] :
    IsInternal A ↔
      (∀ x : ⨁ i, A i, x.sum (fun _i y ↦ (y : M)) = 0 → x = 0) ∧
        ∀ b : M, ∃ a : ⨁ i, A i, (DFinsupp.sum a fun _i x ↦ x) = b := by
  rw [DirectSum.IsInternal]
  rw [Function.Bijective, Function.Surjective]
  rw [← AddMonoidHom.ker_eq_bot_iff]
  rw [AddSubgroup.eq_bot_iff_forall]
  simp [AddMonoidHom.mem_ker, DirectSum.coeAddMonoidHom_eq_dfinsuppSum]

lemma IsInternal.eq_zero_of_subsingleton_preimage (hA : IsInternal A) {κ : Type*} (g : κ → ι)
    (f : κ → M) (s : Finset κ) (hg : (s : Set κ).InjOn g) (hfg : ∀ k, f k ∈ A (g k))
    (hf₀ : ∑ k ∈ s, f k = 0) {k : κ} (hk : k ∈ s) : f k = 0 := by
  classical
  letI := hA.chooseDecomposition
  have (k) : decompose A (f k) = DirectSum.of (fun i ↦ A i) (g k) ⟨f k, hfg k⟩ :=
    (decompose A).symm.injective (by simp)
  have hf₀ := congr((decomposeAddEquiv A $hf₀ (g k)).1)
  simp only [map_sum, decomposeAddEquiv_apply,
    decompose_zero, zero_apply, ZeroMemClass.coe_zero] at hf₀
  rw [DFinsupp.finset_sum_apply, Finset.sum_eq_single k] at hf₀
  · simpa [this] using hf₀
  · intros b hb hbk
    simp_rw [this, DirectSum.of_apply, dif_neg (hg.ne hb hk hbk)]
  · simp [hk]

end DirectSum
