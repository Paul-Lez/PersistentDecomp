import Mathlib.Data.Real.Basic --required for R to be viewed as a partial order
import Mathlib.Algebra.Category.ModuleCat.Abelian --ModuleCat is an abelian category
import Mathlib.Algebra.Module.LinearMap.Basic

open CategoryTheory

/-- Persistence modules are defined as an alias for the category of functors from
a partial order to a category of vector spaces. -/
abbrev PersistenceModule (C F : Type*) [PartialOrder C] [DivisionRing F]
  := (C ⥤ (ModuleCat F))

/--Definition of the zero module associated to a ring F, {0}. PUnit is the name of the
trivial additive group. Just using "PUnit" everywhere doesn't work, as it
is not seen as an element of ModuleCat F.
In precise words, this is "the element in ModuleCat F, the category of modules over F, with as underlying
subset the trivial group" -/
def ZeroSubmod (F : Type u) [DivisionRing F] : ModuleCat.{u} F where
  carrier := PUnit.{u+1}

--Definition of the `F`-module `F`.
def SelfSubmod (F : Type u) [DivisionRing F] : ModuleCat.{u} F where
  carrier := F

/--Definition of the zero persistence module, the zero-object in the category of persistence
modules. It maps every element in the partial order `C` to the `F`-module `{0}`. -/
def ZeroModule (C F : Type*) [PartialOrder C] [DivisionRing F] : (PersistenceModule C F) where
  obj := fun _ ↦ (ZeroSubmod F)
  map _ :=  𝟙 (ZeroSubmod F)

--Some Tests

variable {C K : Type} [PartialOrder C] [DivisionRing K]
variable {P Q : PersistenceModule C K}

--This line shows that the coproduct of persistence modules is well-defined. The theorem that this
--implies that the category of persistence modules is abelian itself is thankfully already
--implemented into Mathlib.
#check (ZeroModule C K) ⨿ (ZeroModule C K)
#check P ⨿ Q


/--
Definition of the action of an interval module on objects of `(ℝ, ≤)`. For an interval
`I = [a,b]`, `x` is mapped to the `F`-module F if `x` is in `I`, and to `{0}` otherwise. -/
noncomputable def IntervalModuleObject (a b x : ℝ) (F : Type) [DivisionRing F] : (ModuleCat F) :=
  if (a ≤ x ∧ x ≤ b) then (SelfSubmod F) else (ZeroSubmod F)

/-The next lemmas are a bit of "API", i.e. easy results that
allow us to use `IntervalModuleObject` without actually ever unfolding the definition -/

@[simp]
lemma IntervalModuleObject_apply_of_le_and_le {a b x : ℝ} (F : Type) [DivisionRing F] (habx : a ≤ x ∧ x ≤ b) : IntervalModuleObject a b x F = SelfSubmod F := by
  rwa [IntervalModuleObject, if_pos]

@[simp]
lemma IntervalModuleObject_apply_of_not_le_and_le (a b x : ℝ) (F : Type) [DivisionRing F] (habx : ¬ (a ≤ x ∧ x ≤ b)) :
  IntervalModuleObject a b x F = ZeroSubmod F := by
  rwa [IntervalModuleObject, if_neg]

@[simp]
lemma IntervalModuleObject_apply_of_lt_left (a b x : ℝ) (F : Type) [DivisionRing F] (hax : x < a) : IntervalModuleObject a b x F = ZeroSubmod F := by
  rw [IntervalModuleObject_apply_of_not_le_and_le]
  rw [not_and_or, not_le]
  apply Or.intro_left _ hax

@[simp]
lemma IntervalModuleObject_apply_of_lt_right (a b x : ℝ) (F : Type) [DivisionRing F] (hax : b < x) : IntervalModuleObject a b x F = ZeroSubmod F := by
  rw [IntervalModuleObject_apply_of_not_le_and_le]
  rw [not_and_or, not_le, not_le]
  apply Or.intro_right _ hax


/--Definition of the action of an interval module on morphisms of `(ℝ, ≤)`, that is to say, on
relations `x ≤ y` for real numbers x and y. For an interval
`I = [a,b]`, `(x ≤ y)` is mapped `Id F` if `x` and `y` are in `I`, and to the `0`-map otherwise. -/
noncomputable def IntervalModuleMorphism (a b : ℝ)
    /-using `{ }` instead of `( )` makes the variables *implicit*: Lean can guess what `x` and `y` are from
    `h` so we don't need to specify them.-/
    {x y : ℝ} (h : x ≤ y) (F : Type)
    [DivisionRing F] : IntervalModuleObject a b x F ⟶ IntervalModuleObject a b y F :=
  if h₁ : (a ≤ x ∧ y ≤ b) then by
    /-Here, the "canonical" way of doing this would be to use
    `eqToHom` (see definition of the `Bump` functor). The two approaches are essentially the same (both are essentially rewritting the equality and the using `𝟙`), but `eqToHom` has a lot API designed to make its usage less painful. -/
    rw [IntervalModuleObject_apply_of_le_and_le F ⟨h₁.left, le_trans h h₁.right⟩, IntervalModuleObject_apply_of_le_and_le F  ⟨le_trans h₁.left h, h₁.right⟩]
    apply 𝟙
  /-The trick here is that the 0 map is always defined to we don't even need to know what our objects are
    i.e. we don't need to do a case analysis to figure out which one of the objects is 0.-/
  else by
    exact 0

/-The full definition of an interval module, now that we know how it acts both on objects
  and on morphisms. -/
noncomputable def IntervalModule (a b : ℝ) (F : Type) [DivisionRing F] : (PersistenceModule ℝ F) where
  obj x := IntervalModuleObject a b x F
  map {x y} h := (IntervalModuleMorphism a b (leOfHom h) F)
  /- The proof for these two should be really close to the functoriality proof
    of the `Bump` functor construction-/
  map_id := by sorry
  map_comp := by sorry

--The last two "sorry's" correspond to proving that this functor takes identity maps
--to identity maps, and that it is functorial with respect to the composition of morphisms.
--Still working on this...


--Proof that identity maps are taken to identity maps by interval modules.
theorem IdIsId (a b x : ℝ) (F : Type)
  [DivisionRing F] : (IntervalModuleMorphism a b (le_refl x) F) = 𝟙 (IntervalModuleObject a b x F) :=
  if h₁ : (a ≤ x ∧ x ≤ b) then by
    sorry
  else
    sorry


--Definition of decomposability of interval modules.
def IsDecomposable (I : PersistenceModule C K) : Prop :=
  ∀ (P Q : PersistenceModule C K), I = (P ⨿ Q) → (P = ZeroModule C K) ∨ (Q = ZeroModule C K)

------Testing

variable {H : ModuleCat ℝ}

--An example functor.
def ExampleFunctor : (ℝ ⥤ ModuleCat ℝ) where
  obj := fun (_ : ℝ) ↦ H
  map := by
    dsimp
    intro x y
    use fun (_ : x ⟶ y) ↦ 𝟙 H

--The same functor, this time viewed as a persistence module. This needs the keyword noncomputable,
--since it relies on the division ring structure of ℝ, and computers cannot decide if any real number
--is 0 or not in finite time.
noncomputable def ExampleFunctor2 : (PersistenceModule ℝ ℝ) where
  obj := fun (_ : ℝ) ↦ H
  map := by
    dsimp
    intro x y
    use fun (_ : x ⟶ y) ↦ 𝟙 H

--Alternate definitions for {0} and F modules that are restricted to division rings of type Type
def ZeroSubmod2 (F : Type) [DivisionRing F] : ModuleCat F where
  carrier := Unit

def SelfSubmod2 (F : Type) [DivisionRing F] : ModuleCat F where
  carrier := F

--Another syntax for the F module F
def SelfSubmod3 (F : Type) [DivisionRing F] : ModuleCat F := ModuleCat.of F F

variable {C K : Type*} [PartialOrder C] [DivisionRing K]

--This code is the proof that Punit is indeed a module on any ring. It's not necessary to
--have here since it's in the imports anyway.
instance : Module K PUnit where
  __ := PUnit.distribMulAction
  add_smul _ _ _ := Subsingleton.elim _ _
  zero_smul _ := Subsingleton.elim _ _

-----Deprecated code

--Another approach to defining persistence modules, without going through the
--definition using functors. This was the first approach I tried, but I think the
--current one is much better, since it gives us access to every result on functor
--categories.


--this defines PersMod C K as a structure which contains two fields:
--1) a functor between the category obtained from C's partial order and the category of vector spaces on K
--2) the base field
@[ext]
structure PersMod (C : Type u) (K : Type v) [PartialOrder C] [DivisionRing K] where
  toFunctor : CategoryTheory.Functor C (ModuleCat K)
  baseField : K


--this establishes that persistence modules form a category
instance PersModCategory (C : Type u) (K : Type v) [PartialOrder C]
  [DivisionRing K] : CategoryTheory.Category  (PersMod C K) where
  Hom P Q := CategoryTheory.NatTrans P.toFunctor Q.toFunctor
  id F := CategoryTheory.NatTrans.id F.toFunctor
  comp η₁ η₂ := CategoryTheory.NatTrans.vcomp η₁ η₂

-------------------------------------------------------------------------
