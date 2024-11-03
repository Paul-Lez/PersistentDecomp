import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

open scoped DirectSum

variable {M S : Type*} [DecidableEq ι] [AddCommGroup M] [SetLike S M]
  [AddSubgroupClass S M] (A : ι → S) [DecidableEq M]


lemma DirectSum.isInternal_iff : DirectSum.IsInternal A ↔
  (∀ (x : ⨁ (i : ι), A i), (DFinsupp.sum x fun i x ↦ ↑x) = (0 : M) → x = 0) ∧
    ∀ (b : M), ∃ a : ⨁ (i : ι), A i, (DFinsupp.sum a fun i x ↦ x) = b := by
  rw[DirectSum.IsInternal]
  rw[Function.Bijective, Function.Surjective]
  rw[←AddMonoidHom.ker_eq_bot_iff]
  rw[AddSubgroup.eq_bot_iff_forall]
  simp [AddMonoidHom.mem_ker, DirectSum.coeAddMonoidHom_eq_dfinsupp_sum]
