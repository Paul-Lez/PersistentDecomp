module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Span.Basic
public import PersistentDecomp.Mathlib.Algebra.Module.Submodule.Map
public import PersistentDecomp.Prereqs.Indecomposable

public section

/-!
# Persistence Submodules

In this file we define persistence submodules and we equip them with a complete lattice structure.
-/

open CategoryTheory

variable {C : Type} [Category C] {K : Type} [DivisionRing K] {M : C ⥤ ModuleCat K} {c d : C}

variable (M) in
/-- A persistence submodule of a persistence module `M` is a family of submodules `N_c ≤ M_c`
indexed by `c : C` that is compatible with the transition maps of `M`, in the sense that for
all morphisms `c ⟶ d` in `C`, the induced morphism `M_c ⟶ M_d` sends `N_c` into `N_d`. -/
structure PersistenceSubmodule where
  toFun (c : C) : Submodule K (M.obj c)
  map_le' {c d : C} (f : c ⟶ d) : (toFun c).map (ModuleCat.Hom.hom <| M.map f) ≤ toFun d

namespace PersistenceSubmodule

instance : DFunLike (PersistenceSubmodule M) C fun c ↦ Submodule K (M.obj c) where
  coe := toFun
  coe_injective' N₁ N₂ := by cases N₁; cases N₂; congr!

/-- The inclusion of the submodules `N c` and `N d` is compatible with the "transition" maps of the
functor `M`, i.e if we have `f : c ⟶ d` then the image of `N c` by `M f` lies in the submodule
`N d`. -/
lemma map_le (N : PersistenceSubmodule M) (f : c ⟶ d) :
    (N c).map (ModuleCat.Hom.hom <| M.map f) ≤ N d := N.map_le' _

/-- A persistence submodule, bundled as a module-valued functor. -/
@[expose]
def toFunctor (N : PersistenceSubmodule M) : C ⥤ ModuleCat K where
  obj c := ModuleCat.of K (N c)
  map {c d} f := ModuleCat.ofHom {
    toFun x := ⟨(M.map f).hom x, N.map_le f (Submodule.mem_map_of_mem x.2)⟩
    map_add' x y := by
      ext
      simp
    map_smul' r x := by
      ext
      simp }
  map_id c := by
    ext x
    simp
  map_comp f g := by
    ext x
    simp

@[ext]
lemma ext {N₁ N₂ : PersistenceSubmodule M} (h : ∀ c, N₁ c = N₂ c) : N₁ = N₂ :=
  DFunLike.ext _ _ h

instance : PartialOrder (PersistenceSubmodule M) := PartialOrder.lift (⇑) DFunLike.coe_injective

instance : Max (PersistenceSubmodule M) where
  max N₁ N₂ := {
    toFun := fun c ↦ N₁ c ⊔ N₂ c
    map_le' := by
      intro c d f
      rw [Submodule.map_sup]
      apply sup_le_sup (N₁.map_le f) (N₂.map_le f) }

instance : Min (PersistenceSubmodule M) where
  min N₁ N₂ := {
    toFun := fun c ↦ N₁ c ⊓ N₂ c
    map_le' := by
      intro c d f
      apply le_trans (Submodule.map_inf_le _)
        (inf_le_inf (N₁.map_le f) (N₂.map_le f)) }

@[simp, norm_cast] lemma coe_sup (N₁ N₂ : PersistenceSubmodule M) :
    ⇑(N₁ ⊔ N₂) = ⇑N₁ ⊔ ⇑N₂ := rfl
@[simp, norm_cast] lemma coe_inf (N₁ N₂ : PersistenceSubmodule M) :
    ⇑(N₁ ⊓ N₂) = ⇑N₁ ⊓ ⇑N₂ := rfl

lemma sup_apply (N₁ N₂ : PersistenceSubmodule M) (c : C) :
    (N₁ ⊔ N₂) c = N₁ c ⊔ N₂ c := rfl
lemma inf_apply (N₁ N₂ : PersistenceSubmodule M) (c : C) :
    (N₁ ⊓ N₂) c = N₁ c ⊓ N₂ c := rfl

/-- There's a notion of the supremum of two submodules, given by `+`,
and a notion of an infimum, given by `∩`. -/
instance : Lattice (PersistenceSubmodule M) :=
  DFunLike.coe_injective.lattice _ .rfl .rfl coe_sup coe_inf

instance : IsModularLattice (PersistenceSubmodule M) where
  sup_inf_le_assoc_of_le := by
    intro x y z hxz c
    exact sup_inf_le_assoc_of_le (y c) (hxz c)

/-- There's a notion of a minimal persistence submodule, namely `0`. -/
instance : OrderBot (PersistenceSubmodule M) where
  bot := {
    toFun := ⊥
    map_le' := by simp }
  bot_le N c := bot_le

/-- There's a notion of a maximal persistence submodule, namely `M`. -/
instance : OrderTop (PersistenceSubmodule M) where
  top := {
    toFun := ⊤
    map_le' := by simp }
  le_top N c := le_top

@[simp, norm_cast] lemma coe_top : ⇑(⊤ : PersistenceSubmodule M) = ⊤ := rfl
@[simp, norm_cast] lemma coe_bot : ⇑(⊥ : PersistenceSubmodule M) = ⊥ := rfl

lemma top_apply (c : C) : (⊤ : PersistenceSubmodule M) c = ⊤ := rfl
lemma bot_apply (c : C) : (⊥ : PersistenceSubmodule M) c = ⊥ := rfl

/-- There's a notion of supremum over arbitrary sets of submodules. -/
instance : SupSet (PersistenceSubmodule M) where
  sSup S := {
    -- The direct sum over arbitrary sets is just the pointwise direct sum
    toFun := ⨆ N ∈ S, N
    map_le' := by
      intro c d f
      simp only [iSup_apply, Submodule.map_iSup, iSup_le_iff]
      intro N hN
      exact le_iSup_of_le N (le_iSup_of_le hN (N.map_le f)) }

/-- There's a notion of infimums over arbitrary sets of submodules. -/
instance : InfSet (PersistenceSubmodule M) where
  sInf S := {
    -- The intersection over arbitrary sets is just the pointwise direct sum
    toFun := ⨅ N ∈ S, N
    map_le' := by
      intro c d f
      rintro _ ⟨x, hx, rfl⟩
      simp only [iInf_apply, SetLike.mem_coe, Submodule.mem_iInf] at hx ⊢
      intro N hN
      exact N.map_le f (Submodule.mem_map_of_mem (hx N hN)) }

@[simp, norm_cast] lemma coe_sSup (S : Set (PersistenceSubmodule M)) :
    sSup S = ⨆ N ∈ S, ⇑N := rfl
@[simp, norm_cast] lemma coe_sInf (S : Set (PersistenceSubmodule M)) :
    sInf S = ⨅ N ∈ S, ⇑N := rfl

@[simp, norm_cast] lemma coe_iSup {ι : Sort*} (f : ι → PersistenceSubmodule M) :
    ⇑(⨆ i, f i) = ⨆ i, ⇑(f i) := by rw [iSup, coe_sSup]; simp [iSup_comm]

@[simp, norm_cast] lemma coe_iInf {ι : Sort*} (f : ι → PersistenceSubmodule M) :
    ⇑(⨅ i, f i) = ⨅ i, ⇑(f i) := by rw [iInf, coe_sInf]; simp [iInf_comm]

lemma sSup_apply (S : Set (PersistenceSubmodule M)) (c : C) : sSup S c = ⨆ N ∈ S, N c := by simp
lemma sInf_apply (S : Set (PersistenceSubmodule M)) (c : C) : sInf S c = ⨅ N ∈ S, N c := by simp

lemma iSup_apply {ι : Sort*} (f : ι → PersistenceSubmodule M) (c : C) :
    (⨆ i, f i) c = ⨆ i, f i c := by simp

lemma iInf_apply {ι : Sort*} (f : ι → PersistenceSubmodule M) (c : C) :
    (⨅ i, f i) c = ⨅ i, f i c := by simp

/-- The sups and infs over possibly infinite sets are compatible with the lattice structure -/
instance : CompleteLattice (PersistenceSubmodule M) :=
  DFunLike.coe_injective.completeLattice _ .rfl .rfl coe_sup coe_inf coe_sSup coe_sInf coe_top
    coe_bot

end PersistenceSubmodule

/-- A decomposition of a persistence module into two persistence submodules. -/
@[expose]
def IsSubmoduleDecomposition (R : Type) [DivisionRing R] (C : Type) [Category C]
    (M : C ⥤ ModuleCat R) (N₁ N₂ : PersistenceSubmodule M) : Prop :=
  N₁ ⊔ N₂ = ⊤ ∧ N₁ ⊓ N₂ = ⊥

/-- A persistence module is indecomposable if every two-piece submodule decomposition is trivial. -/
@[expose]
def IsIndecomposable (R : Type) [DivisionRing R] (C : Type) [Category C]
    (M : C ⥤ ModuleCat R) :=
  ∀ (N₁ N₂ : PersistenceSubmodule M),
  IsSubmoduleDecomposition R C M N₁ N₂ → N₁ = ⊤ ∨ N₂ = ⊤

theorem eq_top_or_eq_top_of_isSubmoduleDecomposition (R : Type) [DivisionRing R]
    (C : Type) [Category C]
    (M : C ⥤ ModuleCat R) (N₁ N₂ : PersistenceSubmodule M)
    (hdec : IsSubmoduleDecomposition R C M N₁ N₂) (hindec : IsIndecomposable R C M) :
    N₁ = ⊤ ∨ N₂ = ⊤ :=
  hindec N₁ N₂ hdec

/-- If one factor in a two-piece decomposition is the whole module, the other is zero. -/
theorem eq_bot_of_isSubmoduleDecomposition_of_eq_top (R : Type) [DivisionRing R]
    (C : Type) [Category C]
    (M : C ⥤ ModuleCat R) (N₁ N₂ : PersistenceSubmodule M)
    (hdec : IsSubmoduleDecomposition R C M N₁ N₂) (heq : N₁ = ⊤) :
    N₂ = ⊥ := by
  simpa [IsSubmoduleDecomposition, heq] using hdec.2

namespace PersistenceSubmodule

/-- A persistence submodule of `N.toFunctor`, viewed as a persistence submodule of the ambient
functor `M`. -/
@[expose]
def mapToAmbient (N : PersistenceSubmodule M) (A : PersistenceSubmodule N.toFunctor) :
    PersistenceSubmodule M where
  toFun c := (A c).map (N c).subtype
  map_le' := by
    intro c d f
    rintro _ ⟨x, hxAamb, rfl⟩
    rcases hxAamb with ⟨xN, hxA, rfl⟩
    refine ⟨(N.toFunctor.map f).hom xN, A.map_le f (Submodule.mem_map_of_mem hxA), ?_⟩
    rfl

@[simp]
lemma mapToAmbient_apply (N : PersistenceSubmodule M) (A : PersistenceSubmodule N.toFunctor)
    (c : C) : mapToAmbient N A c = (A c).map (N c).subtype :=
  rfl

lemma mapToAmbient_le (N : PersistenceSubmodule M) (A : PersistenceSubmodule N.toFunctor) :
    mapToAmbient N A ≤ N := by
  intro c x hx
  rcases hx with ⟨xN, _hxA, rfl⟩
  exact xN.2

@[simp]
lemma mapToAmbient_bot (N : PersistenceSubmodule M) :
    mapToAmbient N (⊥ : PersistenceSubmodule N.toFunctor) = ⊥ := by
  apply PersistenceSubmodule.ext
  intro c
  apply le_antisymm _ bot_le
  intro x hx
  rcases hx with ⟨xN, hxN, rfl⟩
  simpa using hxN

@[simp]
lemma mapToAmbient_top (N : PersistenceSubmodule M) :
    mapToAmbient N (⊤ : PersistenceSubmodule N.toFunctor) = N := by
  refine le_antisymm (mapToAmbient_le N _) ?_
  intro c x hx
  exact ⟨⟨x, hx⟩, trivial, rfl⟩

@[simp]
lemma mapToAmbient_sup (N : PersistenceSubmodule M) (A B : PersistenceSubmodule N.toFunctor) :
    mapToAmbient N (A ⊔ B) = mapToAmbient N A ⊔ mapToAmbient N B :=
  PersistenceSubmodule.ext fun c => by
    change (A c ⊔ B c).map (N c).subtype =
      (A c).map (N c).subtype ⊔ (B c).map (N c).subtype
    exact Submodule.map_sup (A c) (B c) (N c).subtype

lemma mapToAmbient_injective (N : PersistenceSubmodule M) :
    Function.Injective (mapToAmbient N) := by
  intro A B h
  apply PersistenceSubmodule.ext
  intro c
  apply Submodule.map_injective_of_injective (N c).injective_subtype
  simpa [mapToAmbient_apply] using congrArg (fun P : PersistenceSubmodule M => P c) h

lemma mapToAmbient_eq_bot_iff (N : PersistenceSubmodule M)
    (A : PersistenceSubmodule N.toFunctor) :
    mapToAmbient N A = ⊥ ↔ A = ⊥ :=
  ⟨fun h => mapToAmbient_injective N (by simpa using h), fun h => by simp [h]⟩

lemma disjoint_mapToAmbient_of_inf_eq_bot (N : PersistenceSubmodule M)
    {A B : PersistenceSubmodule N.toFunctor} (h : A ⊓ B = ⊥) :
    Disjoint (mapToAmbient N A) (mapToAmbient N B) := by
  rw [disjoint_iff_inf_le]
  intro c x hx
  rcases hx with ⟨hxA, hxB⟩
  rcases hxA with ⟨yA, hyA, rfl⟩
  rcases hxB with ⟨yB, hyB, hyB_eq⟩
  have hy_eq : yA = yB := Subtype.ext hyB_eq.symm
  have hyB' : yA ∈ B c := by simpa [hy_eq] using hyB
  have hyinf : yA ∈ (A ⊓ B) c := ⟨hyA, hyB'⟩
  change (yA : M.obj c) = 0
  exact congrArg Subtype.val <| by
    simpa using
      (show yA ∈ (⊥ : PersistenceSubmodule N.toFunctor) c by simpa [h] using hyinf)

lemma isIndecomposable_toFunctor_of_indecomposable (N : PersistenceSubmodule M)
    (hN : Indecomposable N) : IsIndecomposable K C N.toFunctor := by
  intro A B hdec
  have hsup : mapToAmbient N A ⊔ mapToAmbient N B = N := by
    rw [← mapToAmbient_sup, hdec.1, mapToAmbient_top]
  have hdisj : Disjoint (mapToAmbient N A) (mapToAmbient N B) :=
    disjoint_mapToAmbient_of_inf_eq_bot N hdec.2
  rcases hN hdisj hsup with hA | hB
  · right
    simpa [(mapToAmbient_eq_bot_iff N A).mp hA] using hdec.1
  · left
    simpa [(mapToAmbient_eq_bot_iff N B).mp hB] using hdec.1

lemma exists_nontrivial_toFunctor_obj_of_ne_bot (N : PersistenceSubmodule M) (hN : N ≠ ⊥) :
    ∃ c : C, Nontrivial (N.toFunctor.obj c) := by
  have h_exists : ∃ c : C, N c ≠ ⊥ := by
    by_contra hnone
    push Not at hnone
    exact hN (PersistenceSubmodule.ext hnone)
  rcases h_exists with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  change Nontrivial (N c)
  exact Submodule.nontrivial_iff_ne_bot.mpr hc

end PersistenceSubmodule
