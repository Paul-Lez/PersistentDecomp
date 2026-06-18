module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Data.Real.Basic
public import PersistentDecomp.Mathlib.Order.Interval.Basic

/-!
# Bump Functors and Interval Modules

In this file we define the notion of a "bump functor", i.e. a functor `C ⥤ D` that
sends a subset `I` of `C` to some constant `d : D` and the complement of `I` to zero.
We then use this to construct interval modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v
variable {A : Type u} [Category.{v} A]
variable {C : Type*} [Category C] (e : A) {S : Set C} {z : A} (hz : IsZero z)

/-- A subset `S ⊆ C` is convex if for any pairs of morphisms `(u ⟶ v)` and `(v ⟶ w)` such that
`u, w ∈ S`, we must have `v ∈ S`. -/
def IsConvex (S : Set C) : Prop :=
  ∀ u v w : C, u ∈ S → w ∈ S → (u ⟶ v) → (v ⟶ w) → v ∈ S

section Interval

/-- All intervals are convex subsets in the categorical sense. -/
lemma Interval.isConvex {α : Type*} [PartialOrder α] (I : Interval α) : IsConvex (C := α) I :=
  fun _u _v _w hu hw f g ↦ I.ordConnected.out hu hw ⟨leOfHom f, leOfHom g⟩

end Interval

variable (hS : IsConvex S)

open scoped Classical in
/-- Let `C` be an abelian category and `D` some arbitrary category. Say `S` is a subset of
`D`, and `e` some arbitrary element of `C`. The **bump functor on `S` with value `e`** is the
functor that sends elements of `S` to `e` and elements outside `s` to the zero element of `C`. -/
@[simps]
noncomputable def bump : C ⥤ A where
  obj x := if x ∈ S then e else z
  map {x y} _ :=
    if hx : x ∈ S then
      -- here we have to be a bit careful: we want the morphism to be the zero map, but this goes
      -- from `bump x` to `z` so we need to compose with the "identity map" `z ⟶ bump y`, i.e. we
      -- need to use `eqToHom`, which converts equalities of objects to morphisms
      if hy : y ∈ S then eqToHom (by simp only [hx, ↓reduceIte, hy]) else
        hz.from_ _ ≫ eqToHom (by simp only [↓reduceIte, hy])
      else eqToHom (by simp only [hx, ↓reduceIte]) ≫ hz.to_ _
  map_comp {u v w} f g := by
    -- TODO: golf using split_ifs.
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
        · -- The case `w ∈ S` is empty by convexity.
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
    · simp only [hx, ↓reduceDIte]
      rw [eqToHom_comp_iff]
      apply hz.to_eq

section API

lemma bump_obj_of_mem {x : C} (hx : x ∈ S) : (bump e hz hS).obj x = e := by
  simp [bump_obj, hx, ↓reduceIte]

lemma bump_obj_of_notMem {x : C} (hx : x ∉ S) :(bump e hz hS).obj x = z := by
  simp [bump_obj, hx, ↓reduceIte]

lemma isZero_bump_obj_of_notMem {x : C} (hx : x ∉ S) : IsZero ((bump e hz hS).obj x) := by
  simpa [bump_obj, hx, ↓reduceIte]

noncomputable def zeroThrough (hz : IsZero z) (X Y : A) : X ⟶ Y :=
  hz.from_ X ≫ hz.to_ Y

lemma comp_zeroThrough (hz : IsZero z) {X X' Y : A} (f : X ⟶ X') :
    f ≫ zeroThrough hz X' Y = zeroThrough hz X Y := by
  simp [zeroThrough, ← Category.assoc, hz.eq_of_tgt (f ≫ hz.from_ X') (hz.from_ X)]

lemma zeroThrough_comp (hz : IsZero z) {X Y Y' : A} (f : Y ⟶ Y') :
    zeroThrough hz X Y ≫ f = zeroThrough hz X Y' := by
  simp [zeroThrough, Category.assoc, hz.eq_of_src (hz.to_ Y ≫ f) (hz.to_ Y')]

variable {T : Set C} (hT : IsConvex T)

/-- The natural transformation between two bump functors whose components factor through the
chosen zero object. -/
noncomputable def bumpZero : bump e hz hS ⟶ bump e hz hT where
  app x := zeroThrough hz _ _
  naturality {x y} f := by
    rw [comp_zeroThrough, zeroThrough_comp]

@[simp]
lemma bumpZero_app (x : C) :
    (bumpZero e hz hS hT).app x =
      zeroThrough hz ((bump e hz hS).obj x) ((bump e hz hT).obj x) :=
  rfl

lemma bumpZero_comp {U : Set C} (hU : IsConvex U) :
    bumpZero e hz hS hT ≫ bumpZero e hz hT hU = bumpZero e hz hS hU := by
  ext x
  simp only [NatTrans.comp_app, bumpZero_app]
  rw [zeroThrough_comp]

end API

section IntervalModule

variable (F : Type) [DivisionRing F]

/-- Definition of the action of an interval module on objects of `(ℝ, ≤)`. For an interval
`I = [a,b]`, `x` is mapped to the `F`-module F if `x` is in `I`, and to `{0}` otherwise. -/
noncomputable def intervalModuleObject (I : Interval ℝ) : ℝ ⥤ ModuleCat F :=
  bump (ModuleCat.of F F) (isZero_zero _) I.isConvex

-- Set up custom notation so we can write the `F`-persistent module of an interval `I` as `F[I]`
notation3:max F"["I"]" => intervalModuleObject F I

/-- The interval module of the empty interval is the zero object in the category of persistent
modules. -/
lemma isZero_intervalModuleObject_bot : IsZero (intervalModuleObject F (⊥ : Interval ℝ)) := by
  apply Functor.isZero
  intro x
  apply isZero_bump_obj_of_notMem
  simp


/-- The identity map for equal intervals, and the zero-through-zero-object map otherwise. -/
noncomputable def intervalModuleMorphism {I J : Interval ℝ} (hIJ : I ≤ J) : F[I] ⟶ F[J] := by
  by_cases h : I = J
  · subst h
    exact 𝟙 _
  · exact bumpZero (ModuleCat.of F F) (isZero_zero _) I.isConvex J.isConvex

/-- The construction above preserves compositions. -/
lemma intervalModuleMorphism_comp {I J K : Interval ℝ} (hIJ : I ≤ J)
  (hJK : J ≤ K) : intervalModuleMorphism F hIJ ≫ intervalModuleMorphism F hJK =
    intervalModuleMorphism F (le_trans hIJ hJK) := by
  -- TODO: gold using split_ifs
  by_cases hIK : I = K
  · subst hIK
    have hIJ_eq : I = J := le_antisymm hIJ hJK
    subst hIJ_eq
    simp [intervalModuleMorphism]
  · by_cases hIJ_eq : I = J
    · subst hIJ_eq
      simp [intervalModuleMorphism, hIK]
    · by_cases hJK_eq : J = K
      · subst hJK_eq
        simp [intervalModuleMorphism, hIK]
      · simpa [intervalModuleMorphism, hIK, hIJ_eq, hJK_eq] using
          (bumpZero_comp (ModuleCat.of F F) (isZero_zero _) I.isConvex J.isConvex K.isConvex)

/-- The construction above sends the "identity" inclusion to the identity morphism. -/
lemma intervalModuleMorphism_id (I : Interval ℝ) :
    intervalModuleMorphism F (le_refl I) = 𝟙 _ := by
  simp [intervalModuleMorphism]

end IntervalModule
