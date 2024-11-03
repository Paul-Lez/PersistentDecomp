import Mathlib.Algebra.Module.Submodule.Pointwise

section

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (p p' : Submodule R M) (q q' : Submodule R₂ M₂)
variable {x : M}
variable [RingHomSurjective σ₁₂] {F : Type*} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]
variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]

lemma Submodule.map_sSup (f : F) (S : Set (Submodule R M)) :
    (sSup S).map f = sSup (map f '' S) := by
  rw [(gc_map_comap f : GaloisConnection (map f) (comap f)).l_sSup, sSup_eq_iSup', iSup_subtype, iSup_image]

lemma Submodule.map_sInf (f : F) (S : Set (Submodule R M)) :
    (sInf S).map f ≤ sInf (map f '' S) := by
  rw [(gc_map_comap f).le_iff_le, (gc_map_comap f).u_sInf, iInf_image, sInf_eq_iInf, iInf_subtype',  iInf_subtype']
  apply iInf_mono (fun i => (gc_map_comap f).le_u_l _)

end
