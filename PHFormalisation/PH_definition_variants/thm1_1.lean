import Mathlib.Algebra.Category.ModuleCat.Abelian --ModuleCat is an abelian category
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Algebra.Module.Prod
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.Artinian
import Mathlib.LinearAlgebra.Projection


open CategoryTheory

--More general definition of persistence modules over some (small) category C.
abbrev FunctCat (C : Type*) [Category C] (K : Type*) [DivisionRing K]
   := (C ⥤ ModuleCat K)

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
theorem DirSumIsCoprod (R : Type) [DivisionRing R] (C : Type) [Category C]
  (F : FunctCat C R) (G : FunctCat C R) : (FunctorDirSum R C F G) = (F ⨿ G) := by
  sorry









--Below: Ftting's lemma
open LinearMap


--A slight bit of API for the Fitting Lemma. Here we suppose that we are given
--a hypothesis h that for some n, ker(f^n) and im(f^n) are complements.
--This won't be a hypothesis in the actual Fitting Lemma...
noncomputable def FittingLemmaAPI (R : Type) [DivisionRing R] (M : ModuleCat R)
  [Module.Finite R M] (f : M →ₗ[R] M) {n : ℕ} (h : (IsCompl (ker (f ^ n)) (range (f ^ n))))
  : ((ker (f ^ n) × range (f ^ n)) ≃ₗ[R] M) := by
  apply Submodule.prodEquivOfIsCompl (ker (f ^ n)) (range (f ^ n)) h


noncomputable def ExistsFittingn (R : Type) [DivisionRing R] (M : ModuleCat R)
  [Module.Finite R M] (f : M →ₗ[R] M) {n : ℕ}
  : ∃ n, (IsCompl (ker (f ^ n)) (range (f ^ n))) := by
  sorry
  --LinearMap.eventually_isCompl_ker_pow_range_pow f is very close! Just has a
  --weird kink to figure out with ∀ᶠ

--The version of the Fitting Lemma that we want.
--We assume M is finite (i.e, finitely-generated, or finite-dimensional as
--a vector space). Then it is automatically Artinian and Noetherian.
--This is the same as above, but we drop the hypothesis h and instead obtain
--it from the prior implementation of the Fitting lemma
noncomputable def FittingLemma (R : Type) [DivisionRing R] (M : ModuleCat R)
  [Module.Finite R M] (f : M →ₗ[R] M)
  : ((ker (f ^ n) × range (f ^ n)) ≃ₗ[R] M) := by
  have h : (IsCompl (ker (f ^ n)) (range (f ^ n))) := by
    sorry
  apply Submodule.prodEquivOfIsCompl (ker (f ^ n)) (range (f ^ n)) h








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









--Below: endomorphism rings of persistence modules.


--The endomorphism ring of some persistence module F.
abbrev EndRing (C : Type) [Category C](R : Type) [DivisionRing R]
  (F : FunctCat C R) := (F ⟶ F)

variable (C : Type) [Category C]
variable (R : Type) [DivisionRing R]
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
lemma NegAppModule (θ : EndRing C R F) (X : C) (x : F.obj X) :((-θ).app X) x = - (θ.app X x) := by
  rfl

@[simp]
lemma MulDef (e : EndRing C R F) (f : EndRing C R F):
  (e * f) = f ≫ e := by
  rfl

@[simp]
lemma CompIsComp (e : EndRing C R F) (f : EndRing C R F) (X : C) :
  (e * f).app X = f.app X ≫ e.app X := by
  rfl

@[simp]
lemma EndAddAssoc : ∀ (θ η ε : EndRing C R F), θ + η + ε = θ + (η + ε) := by
  intro θ η ε
  ext (X : C) (x : F.obj X)
  simp only [SumIsSum, SumIsSumModule, add_assoc]

@[simp]
lemma EndAddComm : ∀ (θ η : EndRing C R F), θ + η = η + θ := by
  intro η θ
  ext (X : C) x
  simp only [SumIsSumModule, add_comm]

@[simp]
lemma ZeroAdd : ∀ (a : EndRing C R F), 0 + a = a := by
  intro θ
  ext (X : C) x
  simp

@[simp]
lemma AddZero : ∀ (a : EndRing C R F), a + 0 = a := by
  intro θ
  ext (X : C) x
  simp

@[simp]
lemma ZeroMul : ∀ (a : EndRing C R F), 0 * a = 0 := by
  intro θ
  ext (X : C) x
  simp

@[simp]
lemma MulZero : ∀ (a : EndRing C R F), (a * 0 = 0) := by
  intro θ
  ext (X : C) x
  simp

@[simp]
lemma OneMul : ∀ (a : EndRing C R F), (a * 1 = a) := by
  intro θ
  ext (X : C) x
  simp

@[simp]
lemma MulOne : ∀ (a : EndRing C R F), (1 * a = a) := by
  intro θ
  ext (X : C) x
  simp

@[simp]
lemma MulAssoc : ∀ (a b c : EndRing C R F), a * b * c = a * (b * c) := by
  intro θ η ε
  ext (X : C) x
  simp

@[simp]
lemma RightDistrib : ∀ (a b c : EndRing C R F), (a + b) * c = a * c + b * c := by
  intro θ η ε
  ext (X : C) x
  simp

@[simp]
lemma LeftDistrib : ∀ (a b c : EndRing C R F), a * (b + c) = a * b + a * c := by
  intro θ η ε
  ext (X : C) x
  simp

@[simp]
lemma AddLeftNeg : ∀ (a : EndRing C R F), -a + a = 0 := by
  intro θ
  ext (X : C) x
  simp only [ZeroDef, ZeroEndAppIsZeroAtXatx, SumIsSumModule, NegAppModule, add_left_neg]


--The endomorphism ring is a ring. Everything should be good, but "the rfl tactic failed"??
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
  add_left_neg := AddLeftNeg C R F
  left_distrib := LeftDistrib C R F
  right_distrib := RightDistrib C R F
  mul_assoc := MulAssoc C R F



--This is the first step of theorem 1.1.
instance EndRingIsLocal (R : Type) [DivisionRing R] (C : Type) [Category C]
  (F : FunctCat C R) : LocalRing (EndRing C R F) := by
  sorry
