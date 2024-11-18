import Mathlib.Algebra.Module.Submodule.Map

variable {R : Type*} {R₂ : Type*}
variable {M : Type*} {M₂ : Type*}
variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable {σ₁₂ : R →+* R₂}
variable [RingHomSurjective σ₁₂] {F : Type*} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]

lemma Submodule.map_sSup (f : F) (S : Set (Submodule R M)) :
    (sSup S).map f = sSup (map f '' S) := by
  rw [(gc_map_comap f : GaloisConnection (map f) (comap f)).l_sSup, sSup_eq_iSup', iSup_subtype, iSup_image]

lemma Submodule.map_sInf_le (f : F) (S : Set (Submodule R M)) :
    (sInf S).map f ≤ sInf (map f '' S) := by
  rw [(gc_map_comap f).le_iff_le, (gc_map_comap f).u_sInf, iInf_image, sInf_eq_iInf, iInf_subtype',  iInf_subtype']
  apply iInf_mono (fun i => (gc_map_comap f).le_u_l _)
