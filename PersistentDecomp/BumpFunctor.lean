import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Real.Basic
import PersistentDecomp.Mathlib.Order.Interval.Basic

/-!
# Bump Functors and Interval Modules

In this file we the notion of a "bump functor", i.e. a functor `C ⥤ D` that
sends a subset `I` of `C` to some constant `d : D` and the complement of `I` to zero.
We then use this to construct interval modules.
-/

open CategoryTheory Classical CategoryTheory.Limits

universe u v
variable {A : Type u} [Category.{v} A]
variable {C : Type*} [Category C] (e : A) {S : Set C} {z : A} (hz : IsZero z)

/--A subset `S ⊆ C` is good if for any pairs of morphisms `(u ⟶ v)` and `(v ⟶ w)` such that
`u, w ∈ S`, we must have `v ∈ S`. -/
def good (S : Set C) : Prop := ∀ u v w : C, u ∈ S → w ∈ S → (u ⟶ v) → (v ⟶ w) → v ∈ S

section Interval

/-- All intervals are good subsets in the categorical sense. -/
lemma Interval.isGood {α : Type*} [PartialOrder α] (I : Interval α) : good (C := α) I :=
  fun _u _v _w hu hw f g ↦ I.ordConnected.out hu hw ⟨leOfHom f, leOfHom g⟩

end Interval

variable (hS : good S)

/-- Let `C` be an abelian category and `D` some arbitrary category. Say `S` is a subset of
`D`, and `e` some arbitrary element of `C`. The **bump functor on `S` with value `e`** is the
functor that sends elements of `S` to `e` and elements outside `s` to the zero element of `C`. -/
@[simps]
noncomputable def Bump : C ⥤ A where
  obj x := if x ∈ S then e else z
  map {x y} _ :=
    if hx : x ∈ S then
      -- here we have to be a bit careful: we want the morphism to be the zero map, but this goes
      -- from `Bump x` to `z` so we need to compose with the "identity map" `z ⟶ Bump y`, i.e. we
      -- need to use `eqToHom`, which converts equalities of objects to morphisms
      if hy : y ∈ S then eqToHom (by simp only [hx, ↓reduceIte, hy]) else
        hz.from_ _ ≫ eqToHom (by simp only [hx, ↓reduceIte, hy])
      else eqToHom (by simp only [hx, ↓reduceIte]) ≫ hz.to_ _
  map_comp {u v w} f g := by
    --The proof is a case bash. We start with the case that u lies in S
    by_cases hu : u ∈ S
    · simp only [hu, ↓reduceDIte]
      by_cases hv : v ∈ S
      · --Assume v also lies in S
        simp only [hv, ↓reduceDIte]
        by_cases hw : w ∈ S
        -- If w lies in S then were are done since this ends up being the composition of identity
        -- morphisms
        · simp only [hw, ↓reduceDIte, eqToHom_trans]
        -- If w isn't in S then we're mapping into the zero element of the target category and
        -- there's only one such map
        · simp only [hw, ↓reduceDIte, comp_eqToHom_iff]
          apply hz.from_eq
      · --Next assume v doesn't lie in S
        by_cases hw : w ∈ S
        · --The case w ∈ S is empty since S is a "good" subset
          exfalso
          apply hv (hS u v w hu hw f g)
        · -- If w ∈ S then again we're mapping into the zero element of the target category and
          -- there's only one such map
          simp only [hw, ↓reduceDIte, comp_eqToHom_iff]
          apply hz.from_eq
    · -- Finally, assume u is not in S. Then we're mapping from the zero element, and there can only
      -- be one such map.
      simp only [hu, ↓reduceDIte, eqToHom_comp_iff]
      apply hz.to_eq
  map_id x := by
    --Again we can argue by cases, but here things are less tedious
    by_cases hx : x ∈ S
    · simp only [hx, ↓reduceDIte, eqToHom_refl]
    · simp only [eqToHom_refl, hx, ↓reduceDIte]
      rw [eqToHom_comp_iff]
      apply hz.to_eq

/-TODO: add functoriality of this construction: should send inclusion of set to
"inclusion" of functors.
Maybe we will need to show that `Bump` defines a functor from the category of subsets of
`D` (wrt inclusion) to the category of functors `D ⥤ C` ?
We can also show functoriality in the choice of the element `e`.-/

section API

@[simp]
lemma Bump_apply_of_mem {x : C} (hx : x ∈ S) :
  (Bump e hz hS).obj x = e := by
  simp only [Bump_obj, hx, ↓reduceIte]

@[simp]
lemma Bump_apply_of_not_mem {x : C} (hx : x ∉ S) :
  (Bump e hz hS).obj x = z := by
  simp only [Bump_obj, hx, ↓reduceIte]

lemma IsZero_Bump_apply_of_not_mem {x : C} (hx : x ∉ S) :
  IsZero ((Bump e hz hS).obj x) := by
  simpa only [Bump_obj, hx, ↓reduceIte]

end API

section IntervalModule

variable (F : Type) [DivisionRing F]

/--Definition of the action of an interval module on objects of `(ℝ, ≤)`. For an interval
`I = [a,b]`, `x` is mapped to the `F`-module F if `x` is in `I`, and to `{0}` otherwise. -/
noncomputable def IntervalModuleObject (I : Interval ℝ) : ℝ ⥤ ModuleCat F :=
  Bump (ModuleCat.of F F) (isZero_zero _) I.isGood

-- Set up custom notation so we can write the `F`-persistent module of an interval `I` as `F[I]`
notation3:max F"["I"]" => IntervalModuleObject F I

/--The interval module of the empty interval is the zero object in the category of persistent
modules. -/
lemma IsZero_IntervalModuleObject'_zero : IsZero (IntervalModuleObject F (⊥ : Interval ℝ)) := by
  sorry


/--The map of interval modules induced by an inclusion of intervals. To construct this we
should first construct the analogous version for bump functors-/
noncomputable def IntervalModuleMorphism {I J : Interval ℝ} (hIJ : I ≤ J) : F[I] ⟶ F[J] := by
  sorry

/--The construction above preserves compositions-/
noncomputable def IntervalModuleMorphism_comp {I J K : Interval ℝ} (hIJ : I ≤ J)
  (hJK : J ≤ K) : IntervalModuleMorphism F hIJ ≫ IntervalModuleMorphism F hJK =
    IntervalModuleMorphism F (le_trans hIJ hJK) := by
  sorry

/--The construction above sends the "identity" inclusion to the identity morphism-/
lemma IntervalModuleMorphism_identity (I : Interval ℝ) :
  IntervalModuleMorphism F (le_refl I) = 𝟙 _ := by
  sorry

end IntervalModule
