import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Order.Interval.Basic
import PHFormalisation.PHFormalisation.Basic_variants
  --change this to import the file with the `PersistentModule` definition

open CategoryTheory Classical CategoryTheory.Limits

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {C : Type*} [Category C] (e : A) {S : Set C} {z : A} (hz : IsZero z)


/--This property should be the categorical version of being an interval (or some form of connectedness/convexity) but
I'm not sure if it is common in the literature. The name isn't great, probably `IntervalLike` or
something of the sort would be better! -/
def good (S : Set C) : Prop := ∀ u v w : C, u ∈ S → w ∈ S → (u ⟶ v) → (v ⟶ w) → v ∈ S

variable (hS : good S)

/-- Let `C` be an abelian category and `D` some arbitrary category. Say `S` is a subset of
`D`, and `e` some arbitrary element of `C`. The **bump functor on `S` with value `e`** is the
functor that sends elements of `S` to `e` and elements outside `s` to the zero element of `C`. -/
@[simps]
noncomputable def Bump : C ⥤ A where
  obj x := if x ∈ S then e else z
  map {x y} _ :=
    if hx : x ∈ S then
      --here we have to be a bit careful: we want the morphism to be the zero map, but this goes from
      -- `Bump x` to `z` so we need to compose with the "identity map" `z ⟶ Bump y`, i.e. we need
      -- to use `eqToHom`, which converts equalities of objects to morphisms
      if hy : y ∈ S then eqToHom (by simp only [hx, ↓reduceIte, hy]) else
        hz.from_ _ ≫ eqToHom (by simp only [hx, ↓reduceIte, hy])
      else eqToHom (by simp only [hx, ↓reduceIte]) ≫ hz.to_ _
  map_comp {u v w} f g := by
    --The proof is a case bash. We start with the case that u lies in S
    by_cases hu : u ∈ S
    · simp only [hu, ↓reduceDite]
      by_cases hv : v ∈ S
      · --Assume v also lies in S
        simp only [hv, ↓reduceDite]
        by_cases hw : w ∈ S
        --If w lies in S then were are done since this ends up being the composition of identity morphisms
        · simp only [hw, ↓reduceDite, eqToHom_trans]
        --If w isn't in S then we're mapping into the zero element of the target category and there's only one such map
        · simp only [hw, ↓reduceDite, comp_eqToHom_iff]
          apply hz.from_eq
      · --Next assume v doesn't lie in S
        by_cases hw : w ∈ S
        · --The case w ∈ S is empty since S is a "good" subset
          exfalso
          apply hv (hS u v w hu hw f g)
        · --If w ∈ S then again we're mapping into the zero element of the target category and there's only one such map
          simp only [hw, ↓reduceDite, comp_eqToHom_iff]
          apply hz.from_eq
    · --Finally, assume u is not in S. Then we're mapping from the zero element, and there can only be one such map.
      simp only [hu, ↓reduceDite, eqToHom_comp_iff]
      apply hz.to_eq
  map_id x := by
    --Again we can argue by cases, but here things are less tedious
    by_cases hx : x ∈ S
    · simp only [hx, ↓reduceDite, eqToHom_refl]
    · simp only [eqToHom_refl, hx, ↓reduceDite]
      rw [eqToHom_comp_iff]
      apply hz.to_eq

/-TODO: add functoriality of this construction: should send inclusion of set to
"inclusion" of functors.
Maybe we will need to show that `Bump` defines a functor from the category of subsets of
`D` (wrt inclusion) to the category of functors `D ⥤ C` ?
We can also show functoriality in the choice of the element `e`.-/

section API

--In this section we write a bit of API for the Bump functor so it's easier to use

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

--TODO: write more API e.g for the morphisms (one lemma for each of the possible cases...)

end API

namespace BumpPersistence

/- In this section we construct persistent modules using the Bump functor. I've
put all this in the `BumpPersistance` namespace to avoid clashes with the original
definition -/

variable (F : Type) [DivisionRing F]

/-- `ZeroSubMod F` is the zero object in the category of `F`-modules-/
lemma IsZero_ZeroSubmod : IsZero (ZeroSubmod F) where
  unique_to Y := sorry
  unique_from Y := sorry

section Interval

/-A few preliminary results on intervals (there are various approaches to doing intervals in mathlib, and
the version I'm using here is relatively recent so still is missing some rather basic results - it is
however hopefully better suited to what we're doing)-/

lemma Interval.mem_iff_mem_coe_set (I : Interval ℝ) (x : ℝ) :
  x ∈ I ↔ x ∈ (I : Set ℝ) := by simp

lemma NonemptyInterval.mem_of_le_of_le_of_mem_of_mem {I : NonemptyInterval ℝ}
  {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) (hx : x ∈ I) (hz : z ∈ I) : y ∈ I := by
  rw [NonemptyInterval.mem_def] at *
  exact ⟨le_trans hx.left hxy, le_trans hyz hz.right⟩

/--All intervals are good subsets in the categorical sense-/
lemma Interval.IsGood (I : Interval ℝ) : good (C:= ℝ) I := by
  -- This proof could actually be one (long) line but that's a bit unreadable
  apply Interval.recBotCoe (C := fun J => good (J : Set ℝ)) (n := I)
  · intro u ; aesop
  · intro J u v w hu hw f g
    apply NonemptyInterval.mem_of_le_of_le_of_mem_of_mem (leOfHom f) (leOfHom g) hu hw

end Interval

/--Definition of the action of an interval module on objects of `(ℝ, ≤)`. For an interval
`I = [a,b]`, `x` is mapped to the `F`-module F if `x` is in `I`, and to `{0}` otherwise. -/
noncomputable def IntervalModuleObject' (I : Interval ℝ) : PersistenceModule ℝ F :=
  Bump (ModuleCat.of F F) (IsZero_ZeroSubmod F) (Interval.IsGood I)

-- Set up custom notation so we can write the `F`-persistent module of an interval `I` as `F[I]`
notation3:max F"["I"]" => IntervalModuleObject' F I

/--The interval module of the empty interval is the zero object in the category of persistent modules-/
lemma IsZero_IntervalModuleObject'_zero : IsZero (IntervalModuleObject' F (⊥ : Interval ℝ)) := by
  sorry

/-Bunch of API to do here, e.g. the Interval module of a disjoint union is a sum, the interval module
of ℝ is just the constant functor sending objects to `F` and morphisms to the identity, etc-/


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

namespace BumpPersistence
