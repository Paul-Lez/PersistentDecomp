module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Noetherian.Orzech
public import PersistentDecomp.Prereqs.PersistenceSubmodule

/-!
# Stable kernels and ranges of natural endomorphisms

This file contains the functorial Fitting-decomposition API for endomorphisms of
module-valued functors.
-/

public section

open CategoryTheory

variable (C : Type) [Category C]
variable (R : Type) [DivisionRing R]
variable (F : C ⥤ ModuleCat R)

/-- If one fibre of `F` is nontrivial, then the endomorphism ring of `F` is nontrivial. -/
theorem endRing_nontrivial_of_nontrivial_fiber (X : C) [Nontrivial (F.obj X)] :
    Nontrivial (End F) := by
  refine ⟨⟨(1 : End F), 0, ?_⟩⟩
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : F.obj X)
  exact hx <| congrArg (fun f : F.obj X →ₗ[R] F.obj X => f x) <|
    congrArg (fun f : F.obj X ⟶ F.obj X => f.hom) <|
      congrArg (fun η : End F => η.app X) h

@[simp]
lemma pow_succ_eq_comp (θ : End F) (n : ℕ) : θ^(n+1) = θ ≫ (θ^n) := by
  change θ ^ (n + 1) = θ ^ n * θ
  rfl

@[simp]
lemma comp_pow_eq_pow_comp (θ : End F) (n : ℕ) : θ ≫ (θ^n) = (θ^n) ≫ θ := by
  rw [← pow_succ_eq_comp]
  change θ ^ (n + 1) = θ * θ ^ n
  simpa using (mul_pow_sub_one (show n + 1 ≠ 0 by simp) θ).symm

lemma endRing_pow_app_hom (η : End F) (n : ℕ) (X : C) :
    ((η ^ n).app X).hom = (η.app X).hom ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ', ← ih]
      rfl

/-- The pointwise kernel of the `n`-th power of a natural endomorphism. -/
@[expose]
def endomorphismPowerKernel (η : End F) (n : ℕ) : PersistenceSubmodule F where
  toFun X := LinearMap.ker ((η ^ n).app X).hom
  map_le' := by
    intro X Y f
    rintro _ ⟨x, hx, rfl⟩
    change ((η ^ n).app X).hom x = 0 at hx
    change ((η ^ n).app Y).hom ((F.map f).hom x) = 0
    have h := congrArg (fun g : F.obj X ⟶ F.obj Y => g.hom x) ((η ^ n).naturality f)
    simp [hx] at h ⊢

@[simp]
lemma endomorphismPowerKernel_apply (η : End F) (n : ℕ) (X : C) :
    endomorphismPowerKernel C R F η n X = LinearMap.ker ((η ^ n).app X).hom :=
  rfl

/-- The pointwise range of the `n`-th power of a natural endomorphism. -/
@[expose]
def endomorphismPowerRange (η : End F) (n : ℕ) : PersistenceSubmodule F where
  toFun X := LinearMap.range ((η ^ n).app X).hom
  map_le' := by
    intro X Y f
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨z, hz⟩
    use (F.map f).hom z
    have h := congrArg (fun g : F.obj X ⟶ F.obj Y => g.hom z) ((η ^ n).naturality f)
    simp [hz] at h ⊢

@[simp]
lemma endomorphismPowerRange_apply (η : End F) (n : ℕ) (X : C) :
    endomorphismPowerRange C R F η n X = LinearMap.range ((η ^ n).app X).hom :=
  rfl

/-- The stable kernel of a natural endomorphism, pointwise `⨆ n, ker η^n`. -/
@[expose]
def endomorphismStableKernel (η : End F) : PersistenceSubmodule F :=
  ⨆ n, endomorphismPowerKernel C R F η n

/-- The stable range of a natural endomorphism, pointwise `⨅ n, range η^n`. -/
@[expose]
def endomorphismStableRange (η : End F) : PersistenceSubmodule F :=
  ⨅ n, endomorphismPowerRange C R F η n

@[simp]
lemma endomorphismStableKernel_apply (η : End F) (X : C) :
    endomorphismStableKernel C R F η X =
      ⨆ n, LinearMap.ker ((η ^ n).app X).hom := by
  simp [endomorphismStableKernel, PersistenceSubmodule.iSup_apply]

@[simp]
lemma endomorphismStableRange_apply (η : End F) (X : C) :
    endomorphismStableRange C R F η X =
      ⨅ n, LinearMap.range ((η ^ n).app X).hom := by
  simp [endomorphismStableRange, PersistenceSubmodule.iInf_apply]

/-- Fitting's decomposition for a pointwise Artinian and Noetherian module-valued functor, as a
decomposition into the stable kernel and stable range of a natural endomorphism. -/
theorem isSubmoduleDecomposition_stableKernel_stableRange (F : C ⥤ ModuleCat R)
    [∀ X : C, IsArtinian R (F.obj X)] [∀ X : C, IsNoetherian R (F.obj X)]
    (η : End F) :
    IsSubmoduleDecomposition R C F (endomorphismStableKernel C R F η)
      (endomorphismStableRange C R F η) := by
  refine ⟨?_, ?_⟩
  · apply PersistenceSubmodule.ext
    intro X
    simpa [IsSubmoduleDecomposition, PersistenceSubmodule.sup_apply,
      PersistenceSubmodule.top_apply, endRing_pow_app_hom] using
      (LinearMap.isCompl_iSup_ker_pow_iInf_range_pow ((η.app X).hom)).sup_eq_top
  · apply PersistenceSubmodule.ext
    intro X
    simpa [IsSubmoduleDecomposition, PersistenceSubmodule.inf_apply,
      PersistenceSubmodule.bot_apply, endRing_pow_app_hom] using
      (LinearMap.isCompl_iSup_ker_pow_iInf_range_pow ((η.app X).hom)).inf_eq_bot
