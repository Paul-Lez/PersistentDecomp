module

public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import PersistentDecomp.Mathlib.CategoryTheory.EndRing.Fitting

/-!
# Locality of endomorphism rings

This file proves that the endomorphism ring of an indecomposable pointwise finite
module-valued functor is local.
-/

public section

open CategoryTheory Filter

/-- Pointwise finite persistence modules over the indexing category `C`. -/
structure PointwiseFinitePersistenceModule (C : Type*) [Category C] (K : Type*)
    [DivisionRing K] extends C ⥤ ModuleCat.{0} K where
  finite_obj (X : C) : Module.Finite K (toFunctor.obj X)

variable (C : Type) [Category C]
variable (R : Type) [DivisionRing R]
variable (F : C ⥤ ModuleCat R)

/-- A natural endomorphism of a module-valued functor whose components are all units is a unit. -/
theorem endRing_isUnit_of_forall_isUnit_app (F : C ⥤ ModuleCat R) (η : End F)
    (hrange : ∀ X : C, IsUnit (η.app X).hom) : IsUnit η :=
  (CategoryTheory.isUnit_iff_isIso η).2 <| (NatTrans.isIso_iff_isIso_app η).2 fun X => by
    rw [← CategoryTheory.isUnit_iff_isIso]
    exact (hrange X).map ((ModuleCat.endRingEquiv (F.obj X)).symm.toRingHom)

/-- On an indecomposable pointwise Artinian and Noetherian persistence module, every endomorphism is
either pointwise invertible or has pointwise invertible `1 - η`. -/
theorem endRing_forall_isUnit_app_or_forall_isUnit_one_sub_app (F : C ⥤ ModuleCat R)
    [∀ X : C, IsArtinian R (F.obj X)] [∀ X : C, IsNoetherian R (F.obj X)]
    (hindec : IsIndecomposable R C F) (η : End F) :
    (∀ X : C, IsUnit (η.app X).hom) ∨ (∀ X : C, IsUnit ((1 - η).app X).hom) := by
  let K := endomorphismStableKernel C R F η
  let I := endomorphismStableRange C R F η
  have hdec : IsSubmoduleDecomposition R C F K I :=
    isSubmoduleDecomposition_stableKernel_stableRange C R F η
  rcases hindec K I hdec with hK | hI
  · right
    have hIbot : I = ⊥ := eq_bot_of_isSubmoduleDecomposition_of_eq_top R C F K I hdec hK
    intro X
    let f : Module.End R (F.obj X) := (η.app X).hom
    obtain ⟨n, hn⟩ := eventually_atTop.mp (f.eventually_iInf_range_pow_eq)
    have hrange : LinearMap.range (f ^ n) = ⊥ := by
      rw [← hn n le_rfl]
      simpa [I, endomorphismStableRange_apply, endRing_pow_app_hom] using
        (show I X = ⊥ by simp [hIbot])
    simpa using IsNilpotent.isUnit_one_sub ⟨n, LinearMap.range_eq_bot.mp hrange⟩
  · left
    intro X
    let f : Module.End R (F.obj X) := (η.app X).hom
    have htop_le : ⊤ ≤ LinearMap.range (f ^ 1) := by
      rw [← show (⨅ n, LinearMap.range (f ^ n)) = ⊤ by
        simpa [I, endomorphismStableRange_apply, endRing_pow_app_hom, f] using
          (show I X = ⊤ by simp [hI])]
      exact iInf_le (fun n => LinearMap.range (f ^ n)) 1
    have hsurj : Function.Surjective f := by
      apply LinearMap.range_eq_top.mp
      simpa using eq_top_iff.mpr htop_le
    exact ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv
      (LinearEquiv.ofBijective f (IsNoetherian.bijective_of_surjective_endomorphism f hsurj)),
      rfl⟩

/-- A pointwise unit alternative proves that the endomorphism ring is local. -/
theorem endRing_isLocalRing_of_forall_isUnit_or_isUnit_one_sub (F : C ⥤ ModuleCat R)
    [Nontrivial (End F)]
    (h : ∀ η : End F,
      (∀ X : C, IsUnit (η.app X).hom) ∨ (∀ X : C, IsUnit ((1 - η).app X).hom)) :
    IsLocalRing (End F) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun η =>
    (h η).imp (endRing_isUnit_of_forall_isUnit_app C R F η)
      (endRing_isUnit_of_forall_isUnit_app C R F (1 - η))

/-- The endomorphism ring of an indecomposable pointwise Artinian and Noetherian persistence
module is local. -/
theorem endRing_isLocalRing_of_isIndecomposableFunctor (F : C ⥤ ModuleCat R)
    [∀ X : C, IsArtinian R (F.obj X)] [∀ X : C, IsNoetherian R (F.obj X)]
    (X : C) [Nontrivial (F.obj X)] (hindec : IsIndecomposable R C F) :
    IsLocalRing (End F) := by
  let := endRing_nontrivial_of_nontrivial_fiber C R F X
  exact endRing_isLocalRing_of_forall_isUnit_or_isUnit_one_sub C R F
    (endRing_forall_isUnit_app_or_forall_isUnit_one_sub_app C R F hindec)

/-- A convenience version when the indexing category is inhabited and all fibres are nontrivial. -/
theorem endRing_isLocalRing_of_isIndecomposableFunctor_of_nonempty (F : C ⥤ ModuleCat R)
    [Nonempty C] [∀ X : C, Nontrivial (F.obj X)]
    [∀ X : C, IsArtinian R (F.obj X)] [∀ X : C, IsNoetherian R (F.obj X)]
    (hindec : IsIndecomposable R C F) : IsLocalRing (End F) :=
  endRing_isLocalRing_of_isIndecomposableFunctor C R F Classical.ofNonempty hindec

/-- The endomorphism ring of an indecomposable pointwise finite persistence module is local. -/
theorem endRing_isLocalRing_of_isIndecomposable (M : PointwiseFinitePersistenceModule C R)
    (X : C) [Nontrivial (M.toFunctor.obj X)] (hindec : IsIndecomposable R C M.toFunctor) :
    IsLocalRing (End M.toFunctor) := by
  have : ∀ X : C, Module.Finite R (M.toFunctor.obj X) := fun X => M.finite_obj X
  exact endRing_isLocalRing_of_isIndecomposableFunctor C R M.toFunctor X hindec

/-- A pointwise finite corollary when the indexing category is inhabited and all fibres are
nontrivial. -/
theorem endRing_isLocalRing_of_isIndecomposable_of_nonempty
    (M : PointwiseFinitePersistenceModule C R)
    [Nonempty C] [∀ X : C, Nontrivial (M.toFunctor.obj X)]
    (hindec : IsIndecomposable R C M.toFunctor) :
    IsLocalRing (End M.toFunctor) := by
  have : ∀ X : C, Module.Finite R (M.toFunctor.obj X) := fun X => M.finite_obj X
  exact endRing_isLocalRing_of_isIndecomposableFunctor_of_nonempty C R M.toFunctor hindec
