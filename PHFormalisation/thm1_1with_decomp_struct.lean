import Mathlib.Algebra.Category.ModuleCat.Abelian --ModuleCat is an abelian category
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Algebra.Module.Prod
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Artinian
import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.SetLike.Fintype
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

open CategoryTheory Classical CategoryTheory.Limits
open Filter


/-
Work left to do

Step 1:
  -complete the final few sorry'd parts
  -prove the final step of the proof (showing θ is a unit in the setting of the
theorem)

Step 2:
  a -Start by defining arbitrary products of persistence modules (not just the product of 2)
  b -define the set of all decompositions of a persistence module
  c -equip that set with the appropriate partial order
  d -prove that every chain has an upper bound by constructing the upper bound from the paper

a : actually defining a generic product for persistence modules sounds very complicated.
Say we have M a persistence module and a large number of submodules indexed by some set
S: N_s for all s ∈ S.
Then we would need to construct:
  -> the (potentially very large) product of the objects N_s.obj x
  -> the (potentially very large) product of the morphisms N_s.map α

Alternatively, we could create a structure Decomposition M which is simply an alias for
a set of submodules of M, without forcing any additional properties on it.
This would let us temporarily move forward with the proof without fussing about the
exact definition of large products of persistence modules. However, we will need to
look into this at some point - it's required to finish the proof of step 2.

-/

--More general definition of persistence modules over some (small) category C.
abbrev FunctCat (C : Type*) [Category C] (K : Type*) [DivisionRing K]
   := (C ⥤ ModuleCat K)

def ZeroSubmod (K : Type u) [DivisionRing K] : ModuleCat.{u} K where
  carrier := PUnit.{u+1}

def ZeroModule (C K : Type*) [Category C] [DivisionRing K] : (FunctCat C K) where
  obj := fun _ ↦ (ZeroSubmod K)
  map _ :=  𝟙 (ZeroSubmod K)

--Pointwise finite persistence modules over some small category C.
structure PtwiseFinitePersMod (C : Type*) [Category C] (K : Type*)
  [DivisionRing K] where
  to_functor : FunctCat C K
  finite_cond (X : C) : Module.Finite K (to_functor.obj X)


--Below : product of persistence modules
--Given R a field, C a category, X ∈ Obj(C) and F, G two functors
--C ⥤ Modules over R, this defines the product F(X) × G(X).
@[simp]
def ProductModule (R : Type) [DivisionRing R] (C : Type) [Category C]
  (F : FunctCat C R) (G : FunctCat C R) (X : C): ModuleCat R :=
  ModuleCat.of R ((F.obj X) × (G.obj X))

--Given R a field, C a category, X, Y ∈ Obj(C), f : X ⟶ Y a linear map
--and F, G two functors C ⥤ Modules over R, this defines the product map
--(F f, G f) : (F X × G X) ⟶ (F Y × G Y)
@[simp]
def ProductMapFunc (R : Type) [DivisionRing R] (C : Type) [Category C]
  {X Y : C} (f : (X ⟶ Y)) (F : FunctCat C R) (G : FunctCat C R)
  : ((F.obj X × G.obj X) →ₗ[R] (F.obj Y × G.obj Y)) where
  toFun x := by
    let x₁ := x.1
    let x₂ := x.2
    exact ⟨F.map f x₁, G.map f x₂⟩
  map_add' x y := by
    dsimp
    rw[LinearMap.map_add (F.map f) _ _, LinearMap.map_add (G.map f) _ _]
  map_smul' c x := by
    dsimp
    rw[LinearMap.map_smul (F.map f) _ _, LinearMap.map_smul (G.map f) _ _]

--Same as above, but written with the ProductModule objects for simplicity
@[simp]
def ProductModuleMap (R : Type) [DivisionRing R] (C : Type) [Category C]
  {X Y : C} (f : (X ⟶ Y)) (F : FunctCat C R) (G : FunctCat C R) :
  ((ProductModule R C F G X) ⟶ (ProductModule R C F G Y)) :=
  ProductMapFunc R C f F G

--The direct sum of the functors F and G.
@[simp]
noncomputable def FunctorDirSum (R : Type) [DivisionRing R] (C : Type) [Category C]
  (F : FunctCat C R) (G : FunctCat C R) : FunctCat C R where
  obj X := ProductModule R C F G X
  map f := ProductModuleMap R C f F G
  map_id := by
    intro X
    simp
    rfl
  map_comp := by
    intro X Y Z f g
    simp
    rfl

--The above-defined direct sum of persistence modules corresponds to the
--coproduct inherited from the fact that ModuleCat is abelian.
--TODO : prove this without sorry
theorem DirSumIsCoprod (R : Type) [DivisionRing R] (C : Type) [Category C]
  (F : FunctCat C R) (G : FunctCat C R) : (FunctorDirSum R C F G) = (F ⨿ G) := by
  sorry


--I wanted to try and turn the statement above into a more precise one with this theorem, but
--it is a lot more annoying than it should be.
--Expressing it as ∃ n, (LinearMap.ker (f ^ n)) × (range (f ^ n)) ≃ₗ[R] M makes lean mad,
--and what's below doesn't really feel any easier to use than the theorem just above.
--Left aside for now.

/-
theorem ExistsFittingfit (R : Type) [DivisionRing R] (M : ModuleCat R)
  [Module.Finite R M] (f : M →ₗ[R] M)
  : ∃ n, IsIsomorphic ((LinearMap.ker (f ^ n)) × (range (f ^ n))) M := by
  have h : ∃ n, (IsCompl (LinearMap.ker (f ^ n)) (range (f ^ n))) := ExistsFittingn R M f
  rcases h with ⟨n, h_n⟩
  use n
  have h₁ : ((LinearMap.ker (f ^ n) × range (f ^ n)) ≃ₗ[R] M) := by
    apply Submodule.prodEquivOfIsCompl (ker (f ^ n)) (range (f ^ n)) (h_n)
  rw[IsIsomorphic]
  exact h₁
-/





--Submodules
--This defines submodules of persistence modules.
structure Subfunctor (R : Type) [DivisionRing R] (C : Type) [Category C]
  (F : FunctCat C R) where
  baseFunctor : FunctCat C R
  targetFunctor := F
  injection (X : C) : (baseFunctor.obj X →ₗ[R] F.obj X)
  inj_cond (X : C) : Function.Injective (injection X)
  restriction (f : X ⟶ Y) : ∀ (x : baseFunctor.obj X),
    ((baseFunctor.map f) ≫ (injection Y)) x = ((asHom (injection X)) ≫ (F.map f)) x
    --careful with asHom! This breaks if you use asHom injection Y instead.
--I've also been told there are alternatives way to do this definition on Zulip,
--to look into.

--Should this be a def?
def SubmodDecomp (R : Type) [DivisionRing R] (C : Type) [Category C]
  (M : FunctCat C R) (N₁ : Subfunctor R C M) (N₂ : Subfunctor R C M)
  := (M = (FunctorDirSum R C N₁.baseFunctor N₂.baseFunctor))


def IsIndecomposable (R : Type) [DivisionRing R] (C : Type) [Category C]
  (M : FunctCat C R) :=
  ∀ (N₁ : Subfunctor R C M) (N₂ : Subfunctor R C M),
  SubmodDecomp R C M N₁ N₂ → (M = N₁.baseFunctor) ∨ (M = N₂.baseFunctor)


theorem IndecAndDecImpliesEq  (R : Type) [DivisionRing R] (C : Type) [Category C]
  (M : FunctCat C R) (N₁ : Subfunctor R C M) (N₂ : Subfunctor R C M)
  (hdec : SubmodDecomp R C M N₁ N₂) (hindec : IsIndecomposable R C M)
  : (M = N₁.baseFunctor) ∨ (M = N₂.baseFunctor) := by
  apply hindec
  exact hdec


--If we have a decomposition, and M is equal to one of the 2 factors, then the other
--factor is necessarily the 0 module.
theorem DecImpliesTrivial (R : Type) [DivisionRing R] (C : Type) [Category C]
  (M : FunctCat C R) (N₁ : Subfunctor R C M) (N₂ : Subfunctor R C M)
  (hdec : SubmodDecomp R C M N₁ N₂) (heq : M = N₁.baseFunctor) :
  N₂.baseFunctor = (ZeroModule C R) := by
  sorry




variable (C : Type) [Category C]
variable (R : Type) [DivisionRing R]

--A decomposition of M is, for now, just a set of subfunctors of M. Of course, it needs
--to fulfill certain conditions, but for now I am just trying to get the partial order to
--work on the class.
--Written as a structure, and not a class, so that all decompositions of M share one
--type. This will be useful for Zorn's lemma applications.

structure Decomposition (M : FunctCat C R) where
  SubmodSet : Set (FunctCat C R)

--This is the property that "S₁ is smaller or equal to S₂" for 2 decompositions S₁
--and S₂.
def Refines (S₁ : Decomposition C R M) (S₂ : Decomposition C R M) : Prop :=
  ∀ N ∈ S₁.SubmodSet, (N ∈ S₂.SubmodSet ∨ (∃ S₃ : Decomposition C R N, S₃.SubmodSet ⊆
  S₂.SubmodSet))

lemma RefinesRfl (S₁ : Decomposition C R M) : Refines C R S₁ S₁ := by
  sorry

lemma RefinesAntisymm (S₁ : Decomposition C R M) (S₂ : Decomposition C R M) (h₁ : Refines C R S₁ S₂)
  (h₂ : Refines C R S₂ S₁) : S₁ = S₂ := by
  sorry

lemma RefinesTrans (S₁ : Decomposition C R M) (S₂ : Decomposition C R M) (S₃ : Decomposition C R M)
  (h₁ : Refines C R S₁ S₂) (h₂ : Refines C R S₂ S₃) : Refines C R S₁ S₃ := by
  sorry

instance RefinesIsOrder (M : FunctCat C R) : PartialOrder (Decomposition C R M) where
  le S₁ S₂ := Refines C R S₁ S₂
  lt S₁ S₂ := (Refines C R S₁ S₂) ∧ (S₁ ≠ S₂)
  le_refl := by
    intro S
    exact (RefinesRfl C R S)
  le_antisymm := by
    intro S₁ S₂
    apply RefinesAntisymm C R S₁ S₂
  le_trans := by
    intro S₁ S₂ S₃
    apply RefinesTrans C R S₁ S₂ S₃
  lt_iff_le_not_le := by
    intro S₁ S₂
    sorry








--Below: endomorphism rings of persistence modules.


--The endomorphism ring of some persistence module F.
abbrev EndRing (C : Type) [Category C] (R : Type) [DivisionRing R]
  (F : FunctCat C R) := (F ⟶ F)


variable (F : FunctCat C R)

--The 0 natural transformation from F to itself.
@[simp]
def ZeroEndomorphism : EndRing C R F where
  app X := 0

--Some instances on the way to proving this ring is a ring.
instance : One (EndRing C R F) where
  one := 𝟙 F

instance : Zero (EndRing C R F) where
  zero := ZeroEndomorphism C R F

instance : Add (EndRing C R F) where
  add θ η := θ + η

instance : Mul (EndRing C R F) where
  mul f g := g ≫ f --careful: f ⬝ g = f ∘ g here


def OppEndo (θ : EndRing C R F) : (EndRing C R F) where
  app X := - (θ.app X)

instance : Neg (EndRing C R F) where
  neg θ := OppEndo C R F θ

--API lemmas to simplify working with these endomorphisms.

variable (X : C)

@[simp]
lemma ZeroDef : (0 : EndRing C R F) = (ZeroEndomorphism C R F) := by
  rfl

@[simp]
lemma OneDef : (1 : EndRing C R F) = (𝟙 F) := by
  rfl

@[simp]
lemma ZeroEndAppIsZero : (ZeroEndomorphism C R F).app = 0 := by
  rfl

@[simp]
lemma ZeroEndAppIsZeroAtX (X : C) : (ZeroEndomorphism C R F).app X = 0 := by
  rfl

@[simp]
lemma ZeroEndAppIsZeroAtXatx (X : C) (x : F.obj X) : (ZeroEndomorphism C R F).app X x = 0 := by
  rfl

@[simp]
lemma SumIsSum (e : EndRing C R F) (f : EndRing C R F) (X : C) :
  (e + f).app X = e.app X + f.app X := by
  rfl

@[simp]
lemma SumIsSumModule (e : EndRing C R F) (f : EndRing C R F) (X : C) (x : F.obj X) :
  ((e + f).app X) x = (e.app X) x + (f.app X) x := by
  rfl

@[simp]
lemma NegDef (θ : EndRing C R F) : -θ = OppEndo C R F θ := by
  rfl

@[simp]
lemma NegApp (θ : EndRing C R F) (X : C) : (-θ).app X = - (θ.app X) := by
  rfl

@[simp]
lemma NegAppModule (θ : EndRing C R F) (X : C) (x : F.obj X) : ((-θ).app X) x = - (θ.app X x) := by
  rfl

@[simp]
lemma MulDef (e : EndRing C R F) (f : EndRing C R F) :
  (e * f) = f ≫ e := by
  rfl

@[simp]
lemma CompIsComp (e : EndRing C R F) (f : EndRing C R F) (X : C) :
  (e * f).app X = f.app X ≫ e.app X := rfl

@[simp]
lemma EndAddAssoc : ∀ (θ η ε : EndRing C R F), θ + η + ε = θ + (η + ε) := by
  intro θ η ε
  ext
  simp only [SumIsSum, SumIsSumModule, add_assoc]

@[simp]
lemma EndAddComm : ∀ (θ η : EndRing C R F), θ + η = η + θ := by
  intro η θ
  ext
  simp only [SumIsSumModule, add_comm]

@[simp]
lemma ZeroAdd : ∀ (a : EndRing C R F), 0 + a = a := by
  intro θ
  ext
  simp only [ZeroDef, ZeroEndomorphism, EndAddComm, NatTrans.app_add, add_zero]

@[simp]
lemma AddZero : ∀ (a : EndRing C R F), a + 0 = a := by
  intro θ
  ext
  simp only [ZeroDef, ZeroEndomorphism, NatTrans.app_add, add_zero]

@[simp]
lemma ZeroMul : ∀ (a : EndRing C R F), 0 * a = 0 := by
  intro θ
  ext
  simp only [ZeroDef, ZeroEndomorphism, MulDef, NatTrans.comp_app, Limits.comp_zero]

@[simp]
lemma MulZero : ∀ (a : EndRing C R F), (a * 0 = 0) := by
  intro θ
  ext X x
  simp only [ZeroDef, ZeroEndomorphism, MulDef, NatTrans.comp_app, Limits.zero_comp]

@[simp]
lemma OneMul : ∀ (a : EndRing C R F), (a * 1 = a) := by
  intro θ
  ext X x
  simp only [OneDef, MulDef, Category.id_comp]

@[simp]
lemma MulOne : ∀ (a : EndRing C R F), (1 * a = a) := by
  intro θ
  ext X x
  simp only [OneDef, MulDef, Category.comp_id]

@[simp]
lemma MulAssoc : ∀ (a b c : EndRing C R F), a * b * c = a * (b * c) := by
  intro θ η ε
  ext X x
  simp only [MulDef, NatTrans.comp_app, ModuleCat.coe_comp, Function.comp_apply, Category.assoc]

@[simp]
lemma RightDistrib : ∀ (a b c : EndRing C R F), (a + b) * c = a * c + b * c := by
  intro θ η ε
  ext X x
  simp only [MulDef, Preadditive.comp_add, NatTrans.app_add, NatTrans.comp_app]

@[simp]
lemma LeftDistrib : ∀ (a b c : EndRing C R F), a * (b + c) = a * b + a * c := by
  intro θ η ε
  ext X x
  simp only [MulDef, Preadditive.add_comp, NatTrans.app_add, NatTrans.comp_app]

@[simp]
lemma AddLeftNeg : ∀ (a : EndRing C R F), -a + a = 0 := by
  intro θ
  ext X x
  simp only [ZeroDef, ZeroEndAppIsZeroAtXatx, SumIsSumModule, NegAppModule, neg_add_cancel]



--The endomorphism ring is a ring.
--TODO: understand why the rfl tactic fails and fix it

instance EndRingIsRing (R : Type) [DivisionRing R] (C : Type) [Category C]
  (F : FunctCat C R) : Ring (EndRing C R F) where
    zero_mul := ZeroMul C R F
    mul_zero := MulZero C R F
    one_mul := OneMul C R F
    mul_one := MulOne C R F
    zero_add := ZeroAdd C R F
    add_assoc := EndAddAssoc C R F
    add_zero := AddZero C R F
    add_comm := EndAddComm C R F
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := AddLeftNeg C R F
    left_distrib := LeftDistrib C R F
    right_distrib := RightDistrib C R F
    mul_assoc := MulAssoc C R F
    nsmul_zero θ := rfl
    nsmul_succ n θ := rfl
    natCast n := nsmulRec n 1
    natCast_zero := rfl
    natCast_succ n := rfl
    npow := npowRec
    npow_zero θ := rfl
    npow_succ n θ := rfl
    sub θ η := θ + (-η)
    sub_eq_add_neg θ η := rfl
    zsmul_zero' θ := rfl
    zsmul_succ' n θ := rfl
    zsmul_neg' n θ := rfl

@[simp]
lemma PowEqCompLeft (θ : EndRing C R F) (n : ℕ) : θ^(n+1) = θ ≫ (θ^n) := by
  rw[←MulDef]
  rfl

@[simp]
lemma PowEqCompRight (θ : EndRing C R F) (n : ℕ) : θ^(n+1) = (θ^n) ≫ θ := by
  rw[←MulDef]
  have h : n = (n+1)-1 := by simp
  nth_rewrite 2 [h]
  rw[mul_pow_sub_one]
  simp

variable (θ : EndRing C R F) (n : ℕ)
variable (Y : C)
#check (θ^n).app X
#check LinearMap.range ((θ^n).app X)
#check IsUnit θ


--Below: Fitting's lemma. Step 1.
open LinearMap

--Restate Fitting's Lemma with ∃ as opposed to using the language of filters.
--This is definitely the stupidest way of doing this. Improve later.
theorem ExistsFittingn (R : Type) [DivisionRing R] (M : ModuleCat R)
  [Module.Finite R M] (f : M →ₗ[R] M)
  : ∃ n, (IsCompl (LinearMap.ker (f ^ n)) (range (f ^ n))) := by
  have h : ∀ᶠ n in atTop, IsCompl (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := LinearMap.eventually_isCompl_ker_pow_range_pow f
  have hh : ∃ v ∈ atTop, ∀ y ∈ v, IsCompl (LinearMap.ker (f ^ y)) (range (f ^ y)) := by
    apply Eventually.exists_mem h
  rcases hh with ⟨N, h_N, hhh⟩
  have hhhh : N.Nonempty := by
    apply nonempty_of_mem h_N
  rcases hhhh with ⟨n, h_n⟩
  use n
  apply hhh
  exact h_n


--substep 2
theorem Step2 (α : X ⟶ Y) (M : PtwiseFinitePersMod C R) (η : EndRing C R M.to_functor) :
  (M.to_functor.map α) ≫ (η.app Y) = (η.app X) ≫ (M.to_functor.map α) := by
  apply η.naturality


--Can't make heads or tails of this one yet.
theorem Step2_2 (α : X ⟶ Y) (M : PtwiseFinitePersMod C R) (η : EndRing C R M.to_functor)
  : M.to_functor.map α ≫ ((η^n).app Y) = ((η^n).app X) ≫ M.to_functor.map α := by
  induction' n with n hn
  have hnat : (M.to_functor.map α) ≫ (η.app Y) = (η.app X) ≫ (M.to_functor.map α) := Step2 C R X Y α M η
  have hpow : M.to_functor.map α ≫ (η ^ (n + 1)).app Y = M.to_functor.map α ≫ (((η ^ n) ≫ η).app Y) := by
    simp
    sorry
  sorry
  sorry

--I would really prefer for ηx and ηy to be unified under a single (η : EndRing C R M.to_functor)
--argument here. The issue this creates is that then η.app X and η.app Y are intepreted as
--morphisms and not as linear maps which prevents the use of the ^ notation. For now,
--ηx and ηy are separated and a naturality hypothesis replaces the naturality from η.

--Only a single parameter n is taken for both decompositions. In practice there would be
--2, one at X and one at Y, but we can just pick the maximum.
theorem Step3_1 (M : PtwiseFinitePersMod C R) (α : X ⟶ Y) (n : ℕ)
  (ηx : M.to_functor.obj X →ₗ[R] M.to_functor.obj X) (ηy : M.to_functor.obj Y →ₗ[R] M.to_functor.obj Y)
  (hnat : M.to_functor.map α ≫ (ηy^n) = (ηx^n) ≫ M.to_functor.map α)
  : ∀ (x : (LinearMap.ker (ηx ^ n))), (M.to_functor.map (α) ≫ (ηy ^ n)) x = 0 := by
  intro x
  rw[hnat]
  dsimp
  rw[LinearMap.map_coe_ker]
  simp


theorem Step3_2 (M : PtwiseFinitePersMod C R) (α : X ⟶ Y) (n : ℕ)
  (ηx : M.to_functor.obj X →ₗ[R] M.to_functor.obj X) (ηy : M.to_functor.obj Y →ₗ[R] M.to_functor.obj Y)
  (hnat : M.to_functor.map α ≫ (ηy^n) = (ηx^n) ≫ M.to_functor.map α)
  : ∀ (x : M.to_functor.obj X), x ∈ (LinearMap.range (ηx ^ n)) → ∃ y : (M.to_functor.obj Y),
  (M.to_functor.map α x = y) ∧ (y ∈ (LinearMap.range (ηy ^ n))) := by
  intro x hrange
  have hmem : (∃ z, (ηx^n) z = x):= by
    apply LinearMap.mem_range.mp at hrange
    exact hrange
  let z := Exists.choose hmem
  have hz : (ηx^n) z = x := by
    apply Exists.choose_spec hmem
  use (M.to_functor.map α ≫ (ηy^n)) z
  constructor
  · rw[hnat]
    dsimp
    rw[hz]
  · dsimp
    apply LinearMap.mem_range.mpr
    use ((M.to_functor.map α) z)


-- theorem EndRingLocal (M : PtwiseFinitePersMod C R) (N₁ : Subfunctor R C M.to_functor)
--   (N₂ : Subfunctor R C M.to_functor) (hdec : SubmodDecomp R C M.to_functor N₁ N₂)
--   (hindec : IsIndecomposable R C M.to_functor) (η : EndRing C R M.to_functor)
--   (heq : M.to_functor = N₁.baseFunctor) (hrange : ∀ X : C, IsUnit (η.app X))
--   : (IsUnit η) := by
--   sorry
