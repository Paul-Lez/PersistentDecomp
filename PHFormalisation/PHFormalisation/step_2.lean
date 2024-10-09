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
import Mathlib.Order.SetNotation
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import PHFormalisation.PHFormalisation.thm1_1with_decomp_struct

open CategoryTheory Classical CategoryTheory.Limits
open Filter

/- In this file we sketch what we'll need to prove to
get Step 2 done. Most of the work is setting the stage so
we can apply Zorn's lemma.-/

/- For now we work with types in the 0-th universe. To make the code universe polymorphic we'll need to
make a few edits below-/
variable {C : Type} [Category.{0, 0} C] {K : Type} [DivisionRing K] (M : FunctCat C K)

section Submodules

@[ext]
structure PH.Submodule where
    (mods (x : C) : Submodule K (M.obj x))
    /- TODO: add condition that the inclusion of the submodules
    is compatible with the "transition" maps of the functor M,
    i.e if we have f : x ⟶ y then the image of `mods x` by `M f` lies
    in the submodule `mods y`. -/
    (h_mods : ∀ {x y : C} (f : x ⟶ y), (mods x).map (M.map f) ≤ mods y)


-- TODO: make this better.
@[ext]
lemma PH.Submodule.ext' (N₁ N₂ : Submodule M) (h :
  ∀ x, N₁.mods x = N₂.mods x) : N₁ = N₂ := by
  aesop

-- Persistence submodules are ordered by pointwise inclusion
instance : PartialOrder (PH.Submodule M) where
  le N₁ N₂ := ∀ x, N₁.mods x ≤ N₂.mods x
  le_refl N := fun x => le_refl _
  le_trans N₁ N₂ N₃ := by
    intro h h' x
    exact le_trans (h x) (h' x)
  le_antisymm N₁ N₂ := by
    intro h h'
    apply PH.Submodule.ext'
    intro x
    exact le_antisymm (h x) (h' x)

/- There's a notion of the supremum of two submodules, given by `⊕`,
and a notion of an infimum, given by `∩`.-/
instance : Lattice (PH.Submodule M) where
  sup N₁ N₂ := {
    mods := fun x => (N₁.mods x) ⊔ (N₂.mods x)
    h_mods := by
      intro x y f
      rw [Submodule.map_sup]
      apply sup_le_sup (N₁.h_mods f) (N₂.h_mods f) }
  le_sup_left := by
    intro a b x
    aesop
  le_sup_right := by
    intro a b x
    aesop
  sup_le := by
    intro a b c h h' x
    aesop
  inf N₁ N₂ := {
    mods := fun x => (N₁.mods x) ⊓ (N₂.mods x)
    h_mods := by
      intro x y f
      apply le_trans (Submodule.map_inf_le _) (inf_le_inf (N₁.h_mods f) (N₂.h_mods f)) }
  inf_le_left a b x := by aesop
  inf_le_right a b x := by aesop
  le_inf := by
    intro a b c h h' x
    aesop

/- There's a notion of a minimal submodule, namely `0`-/
instance : OrderBot (PH.Submodule M) where
  bot := {
    mods := fun x => ⊥
    h_mods := by aesop }
  bot_le N := fun x => bot_le

/- There's a notion of a maximal submodule, namely `M`-/
instance : OrderTop (PH.Submodule M) where
  top := {
    mods := fun x => ⊤
    h_mods := by aesop }
  le_top N := fun x => le_top

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
  (sSup S).map f = sSup (map f '' S) := by sorry

lemma Submodule.map_sInf (f : F) (S : Set (Submodule R M)) :
  (sInf S).map f ≤ sInf (map f '' S) := by sorry

end

-- There's a notion of supremum over arbitrary sets of submodules
instance : SupSet (PH.Submodule M) where
  sSup S := {
    -- The direct sum over arbitrary sets is just the pointwise direct sum
    mods := fun x => sSup {(N.mods x) | (N : PH.Submodule M) (_ : N ∈ S)}
    h_mods := by
      intro x y f
      rw [Submodule.map_sSup]
      sorry }

-- There's a notion of infimums over arbitrary sets of submodules
instance : InfSet (PH.Submodule M) where
  sInf S := {
    -- The intersection over arbitrary sets is just the pointwise direct sum
    mods := fun x => sInf {(N.mods x) | (N : PH.Submodule M) (_ : N ∈ S)}
    h_mods := by
      intro x y f
      apply le_trans (Submodule.map_sInf _ _)
      apply sInf_le
      -- Here we're using the compatibility condition on submodules
      sorry }

-- The sups and infs over possibly infinite sets are compatible with the lattice structure
instance : CompleteLattice (PH.Submodule M) where
  le_sSup := sorry
  sSup_le := sorry
  sInf_le := sorry
  le_sInf := sorry
  le_top := sorry
  bot_le := sorry

end Submodules

section DirectSumDecomposition

structure DirectSumDecomposition where
  (S : Set (PH.Submodule M))
  -- TODO Paul: FIXME
  -- This needs to change a bit since we're saying that we're summing to M and then to N.
  -- But we can take care of that later on.
  (h : ∀ (x : C), DirectSum.IsInternal (fun p : S => (p.val.mods x : Submodule _ _)))

variable {M} in
lemma sSup_eq_top_of_direct_sum_decomposition (D : DirectSumDecomposition M) :
    sSup D.S = ⊤ := by
  sorry

--careful: this means that D₁ refines D₂
variable {M : FunctCat C K} in
def IsRefinement : DirectSumDecomposition M → DirectSumDecomposition M → Prop :=
  fun D₁ D₂ => ∃ d : D₂.S → Set (PH.Submodule M), (∀ (N : D₂.S), N.val = sSup ((d N))) ∧ (∀ N, d N ⊆ D₁.S)

--API
--The goal of these API lemmas is to obtain the proof for the remaining "sorry"
--in ToTypeCat. In other words, need to show that the d function is surjective.
--To do this, assume it isn't surjective, then show it contradicts N being direct sum
variable {M : FunctCat C K} in
lemma NissSupImage (I : DirectSumDecomposition M) (J : DirectSumDecomposition M)
  (h : IsRefinement J I) {d : I.S → Set (PH.Submodule M)}
  {h_eq : ∀ (B : I.S), B = sSup (d B)}
   : ⊤ = ⨆ B, sSup (d B) := by
  have h_aux : ⊤ = sSup I.S := (sSup_eq_top_of_direct_sum_decomposition I).symm
  have h_supI : ⊤ = ⨆ (B: I.S), B.val := by
    rw[sSup_eq_iSup'] at h_aux
    exact h_aux
  have h_equality : ∀ (B : I.S), id B = (sSup ∘ d) B := by
    simp [h_eq]
  have h_auxx : ⨆ (B : I.S), (id B).val = ⨆ B, (sSup ∘ d) B := by
    rw[iSup_congr h_equality]
  --rw is too limited to solve at this point
  simp_rw[h_supI]
  exact h_auxx


--J refines I
variable {M : FunctCat C K} in
lemma RefinementMapSurj -- (N : PH.Submodule M)
(I : DirectSumDecomposition M) (J : DirectSumDecomposition M)
  (h : IsRefinement J I) {d : I.S → Set (PH.Submodule M)}
  {h_eq : ∀ (B : I.S), B = sSup (d B)}
  {h_sub :  ∀ (B : I.S), d B ⊆ J.S}
  : (∀ (A : J.S), ∃ (B : I.S), A.val ∈ d B) := by
  by_contra h_abs
  push_neg at h_abs
  let f_aux : J.S → _ := fun (A : J.S) => if ∃ B : I.S, A.val ∈ d B then A.val else ⊥
  have h_dir_sum_J : ⊤ = sSup J.S := (sSup_eq_top_of_direct_sum_decomposition J).symm
  have h_dir_sum_d : ⊤ = ⨆ (A : J.S), f_aux A := by
    have h_aux : ∀ (B : I.S), sSup (d B) = ⨆ A ∈ d B, A := by
      intro B
      apply sSup_eq_iSup
    --for this next line, trying to write it in a single line withotu tactic mode
    --creates issues with synthesizing implicit arguments.
    have h_ssupI : ⊤ = ⨆ B, sSup (d B) := by
      apply NissSupImage
      exact h
      exact h_eq
    simp_rw [h_ssupI]
    --we prove this equality by using antisymmetry of ≤.
    apply le_antisymm
    apply iSup_le_iff.mpr
    intro B
    rw[sSup_eq_iSup]
    apply iSup_le
    intro α
    by_cases h_memb : α ∈ d B
    simp[h_memb]
    have h_surj : ∃ A : J.S, A.val = α := by
      have h_alphaInJ : α ∈ J.S := by
        apply Set.mem_of_mem_of_subset h_memb (h_sub B)
      simp
      exact h_alphaInJ
    rcases h_surj with ⟨A_alph, h_equal⟩
    have h_alpha_le : α ≤ f_aux A_alph := by
      have h_exists_val : ∃ (B : I.S), A_alph.val ∈ d B := by
        use B
        rwa[h_equal]
      simp only [f_aux, h_exists_val]
      simp
      rw[h_equal]
    apply le_iSup_of_le A_alph h_alpha_le
    --the line above closes the first case of by_cases.
    simp [h_memb]
    --and this one is enough to close the second.
    --Now we prove the other direction of the inequality.
    apply iSup_le
    intro α
    by_cases h_memb : ∃ B₀ : I.S, α.val ∈ d B₀
    simp only [f_aux, h_memb]
    simp --annoying that i have to simp twice...
    rcases h_memb with ⟨B₀, h_in⟩
    have h_aux_le : α.val ≤ sSup (d B₀) := by
      apply le_sSup
      exact h_in
    apply le_iSup_of_le
    exact h_aux_le
    --the first case of by_cases is closed now.
    simp only [f_aux, h_memb]
    simp
    --and the second is trivial. This concludes the proof of h_dir_sum_d.
  rw[sSup_eq_iSup' J.S] at h_dir_sum_J
  simp_rw[h_dir_sum_J] at h_dir_sum_d
  rcases h_abs with ⟨A_contra, h_contra⟩
  --This is not trivial because we have no guarantee (yet) that A_contra.val is not
  --(for instance) equal to one of the f_aux A.
  have h_lt : ⨆ (A : J.S), f_aux A < (⨆ (A : J.S), f_aux A) ⊔ A_contra.val := by
    sorry
  have h_le : (⨆ (A : J.S), f_aux A) ⊔ A_contra.val ≤ ⊤ := by
    rw[←sSup_pair]
    apply sSup_le
    rintro b h_mem
    rcases h_mem with h | h
    · have h_sup : ∀ (A : J.S), f_aux A ≤ ⊤ := by
        intro A
        simp only [f_aux]
        by_cases h_AIsImage : (∃ B, ↑A ∈ d B)
        simp [h_AIsImage]
        simp_rw [h_dir_sum_J]
        --apply le_iSup
        simp [h_AIsImage]
      rw[h]
      exact iSup_le h_sup
    · simp at h
      rw[h]
      simp_rw[h_dir_sum_J]
      apply le_iSup
  have h_aux : ⨆ A, f_aux A < ⊤ := by
    exact lt_of_lt_of_le h_lt h_le
  simp_rw[←h_dir_sum_d] at h_aux
  simp_rw [←h_dir_sum_J] at h_aux
  simp at h_aux

/- The decompositions are ordered by refinement. With the current definition of
refinement, this might be a bit awkward to prove, so let's leave it sorried out for now.-/
instance : Preorder (DirectSumDecomposition M) where
  le D₁ D₂ := IsRefinement D₁ D₂
  --D₁ ≤ D₂ iff D₁ refines D₂. This is not the order from the paper, but its dual.
  le_refl D := by
    simp
    rw[IsRefinement]
    let d : (D.S → Set (PH.Submodule M)) := fun (I : D.S) ↦ {I.val}
    use d
    constructor
    · intro I
      aesop
    · intro I
      aesop
  le_trans I₁ I₂ I₃ := by
    intro h12 h23
    simp at *
    rw [IsRefinement] at *
    rcases h12 with ⟨d₁, h₁eq, h₁sub⟩
    rcases h23 with ⟨d₂, h₂eq, h₂sub⟩
    --for some reason this line does not work if I write the set {C | ...} without parentheses around C.
    let d : (I₃.S → Set (PH.Submodule M)) := fun (A : I₃.S) ↦ {(C) | (C : PH.Submodule M) (_ : ∃ B : I₂.S, C ∈ d₁ B ∧ B.val ∈ d₂ A)}
    use d
    constructor
    · intro A
      have h_chara_dA : ∀ B : I₂.S, (B.val ∈ d₂ A) → (∀ C, C ∈ (d₁ B) → C ∈ d A) := by
        rintro B h_B_im C h_C_im
        simp [d]
        use B
        simp
        constructor
        exact h_C_im
        exact h_B_im
      apply le_antisymm
      · rw [h₂eq A]
        apply sSup_le_iff.mpr
        rintro B h_B_im
        --this situation has come up a few times. Can't apply d₁ to B since
        --B is just a PH_Submodule and not of type I₂.S. To work around this,
        --I introduce B' the corresponding element in I₂.S.
        have h_B_mem_I2 : B ∈ I₂.S := by
          exact Set.mem_of_mem_of_subset h_B_im (h₂sub A)
        set B' : I₂.S := ⟨B, h_B_mem_I2⟩ with h_def_B'
        have h_supdef_B' : B = sSup (d₁ B') := (h₁eq B')
        rw[h_supdef_B']
        apply sSup_le_iff.mpr
        rintro C h_C_im
        have h_C_in_im_d : C ∈ d A := (h_chara_dA B' h_B_im C h_C_im)
        exact (le_sSup h_C_in_im_d)
      · apply sSup_le_iff.mpr
        rintro C h_C_im
        simp [d] at h_C_im
        rcases h_C_im with ⟨B, h_aux, h_B_im⟩
        rcases h_aux with ⟨h_B_in_I2, h_C_im_B⟩
        let B' : I₂.S := ⟨B, h_B_in_I2⟩
        have h_C_le_B : C ≤ B'.val := by
          rw [h₁eq B']
          apply le_sSup
          exact h_C_im_B
        have h_B_le_A : B'.val ≤ A.val := by
          rw[h₂eq A]
          apply le_sSup
          exact h_B_im
        exact le_trans (h_C_le_B) (h_B_le_A)
    · intro A x hmem
      have haux : ∃ B : I₂.S, x ∈ d₁ B := by
        simp only [d] at hmem
        rcases hmem with ⟨a, b, c⟩
        rcases b with ⟨B, d, e⟩
        use B
        rw[c] at d
        exact d
      rcases haux with ⟨B, hb⟩
      have haux2 : d₁ B ⊆ I₁.S := by
        exact h₁sub B
      exact Set.mem_of_mem_of_subset hb haux2

-- -- TODO Paul: Make sure this is not stupid
instance : PartialOrder (DirectSumDecomposition M) where
  le_antisymm := sorry


end DirectSumDecomposition

section Chains

/- In this section we set up what's needed to take an inverse limit of direct sum
decompositions. Since these are defined in terms of sets, we could construct the
inverse limit explicitly but I think this would be really painful and messy...-/

-- Here we write some code to go from chains in directSumDecompositions to diagrams in the category of types
variable {M} in
noncomputable def ToTypeCat : (DirectSumDecomposition M) ⥤ Type where
  obj D := Subtype D.S
  -- Define the maps f_{IJ} induced by "J refines I"
  -- Since we are working with dual order, we write J I to have J ≤ I
  map {J I} f := by
    dsimp
    let h_le := leOfHom f
    simp only [LE.le, IsRefinement] at h_le
    let d := Exists.choose h_le
    let h_aux : (∀ (B : ↑I.S), ↑B = sSup (d B)) ∧ ∀ (B : ↑I.S), d B ⊆ J.S := by
      apply Exists.choose_spec h_le
    rcases h_aux with ⟨hsup, hincl⟩
    --this should just be RefinementMapSurj
    let h_le_bis := leOfHom f
    simp only [LE.le] at h_le_bis
    let h : ∀ (A : J.S), ∃ (B : I.S), A.val ∈ d B := by
      apply (RefinementMapSurj I J h_le_bis)
      exact hsup
      sorry
      --exact hincl - causes an infinite loop?
    let f : J.S → I.S := fun A => (h A).choose
    exact f

/- This is possibly useful to make things a bit cleaner so let's keep it for now but possibly remove it later -/
variable {M} in
def ChainToTypeCat (T : Set (DirectSumDecomposition M)) :
  Subtype T ⥤ Type where
  obj D := sorry
  map f := sorry

/- Construct the element `L` (in the notation of our doc) -/
def ChainToInverseLimit (T : Set (DirectSumDecomposition M)) :
  Type := limit (ChainToTypeCat T)


variable (N : PH.Submodule M) (T : Set (DirectSumDecomposition M)) (L : limit (ChainToTypeCat T))
variable (I : Subtype T)
variable (D : DirectSumDecomposition M)
#check limit.π (ChainToTypeCat T) I -- this is how we access the morphism L ⟶ I


/- Get a direct sum out of a chain (this should be the index set 𝓤 in out doc)-/
variable {M} in
def DirectSumDecomposition_of_chain {T : Set (DirectSumDecomposition M)} (hT : IsChain
  LE.le T) : DirectSumDecomposition M := sorry

/- The set `𝓤` is an upper bound for the chain `T` -/
lemma every_chain_has_an_upper_bound (N : PH.Submodule M)
  {T : Set (DirectSumDecomposition M)} (hT : IsChain LE.le T) :
  ∀ D ∈ T, D ≤ DirectSumDecomposition_of_chain hT := by
  sorry

/-Every chain has an upper bound, hence there is a maximal direct sum decomposition `D`-/
lemma zorny_lemma (N : PH.Submodule M) : ∃ (D : DirectSumDecomposition M), IsMax D := by
  apply zorn_le
  rintro T hT
  rw[bddAbove_def]
  use (DirectSumDecomposition_of_chain hT)
  exact (every_chain_has_an_upper_bound M N hT)

end Chains

section Indecomposable

def TrivialDecomp (N : PH.Submodule M) : DirectSumDecomposition M where
  S := {N}
  h := by
    sorry

/--`M` is indecomposable iff its only non-trivial submodule is the zero submodule `⊥`-/
def Indecomposable : Prop := IsMax (TrivialDecomp M ⊤)

variable {M} in
/--This is the definition of indecomposability we should be using since it's more general
(works at a lattice theoretic level)-/
def Indecomposable' (N : PH.Submodule M) : Prop :=
  ∀ a b : PH.Submodule M, a ≤ N → b ≤ N → a ⊓ b = ⊥ → a ⊔ b = N → a = ⊥ ∨ b = ⊥

-- Maximal direct sum decompositions consist of indecomposable submodules.
lemma Indecomposable_of_mem_Max_Direct_sum_decomposition
  (D : DirectSumDecomposition M) (N : PH.Submodule M) (hN : N ∈ D.S) (hmax : IsMax D) :
  IsMax (TrivialDecomp M N) := by
  by_contra hNotMax
  rw[IsMax] at hNotMax
  push_neg at hNotMax
  rcases hNotMax with ⟨P, hle, hneq⟩
  let S : Set (PH.Submodule M) := (D.S \ {N}) ⊔ P.S
  have h : ∀ (x : C), DirectSum.IsInternal (fun p : S => (p.val.mods x : Submodule _ _)) := by
    sorry
  have h' : ⊤ = sSup S := by
    sorry
  let Cex : DirectSumDecomposition M := ⟨S, h⟩
  have contra : ¬ IsMax D := by
    sorry
  exact contra hmax

/-- If `N` is a submodule of `M` that is part of a minimal direct sum decomposition, then `N` is indecomposable -/
lemma Indecomposable'_of_mem_Min_Direct_sum_decomposition
  (D : DirectSumDecomposition M) (N : PH.Submodule M) (hN : N ∈ D.S) (hmax : IsMin D) : Indecomposable' N := by
  by_contra hNotMax
  rw [Indecomposable'] at hNotMax
  simp only [not_forall, Classical.not_imp, not_or, exists_and_left] at hNotMax
  obtain ⟨x, hx, y, hx', hy', hxy, hxy', hy⟩ := hNotMax
  set S : Set (PH.Submodule M) := (D.S \ {N}) ∪ {x, y} with hS
  have h : ∀ (x : C), DirectSum.IsInternal (fun p : S => (p.val.mods x : Submodule _ _)) := by
    intro x
    constructor
    · --this is going to be a bit of a pain to prove
      intro a b hab
      sorry
    · --same here
      intro b
      obtain ⟨a, ha⟩ := (D.h x).right b
      sorry
  let Cex : DirectSumDecomposition M := ⟨S, h⟩
  have contra : ¬ IsMin D := by
    simp only [not_isMin_iff]
    use Cex
    apply lt_of_le_of_ne
    --this is very golfable
    · set d : D.S → Set (PH.Submodule M) := fun (I : D.S) ↦ if I.val = N then {x, y} else {I.val} with hd
      use d, fun I => ?_, fun I => ?_
      · by_cases hI : I.val = N
        · simp only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton, ← hxy']
        · simp only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton]
      · by_cases hI : I.val = N
        · simpa only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton, hS] using Set.subset_union_right
        · simp only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton, Set.singleton_subset_iff]
          apply Set.mem_union_left _ (Set.mem_diff_of_mem I.prop _)
          rw [Set.mem_singleton_iff]
          exact hI
    · --this can probably be golfed with the right API
      intro h
      have : D.S ≠ Cex.S := by
        simp only [ne_eq]
        intro h'
        have: N ∉ S := by
          intro h''
          rw [hS, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_diff, Set.mem_singleton_iff] at h''
          simp only [not_true_eq_false, and_false, false_or] at h''
          rcases h'' with h'' | h''
          · rw [←h'', inf_eq_right.mpr hy'] at hxy
            exact hy hxy
          · rw [←h'', inf_eq_left.mpr hx'] at hxy
            exact hx hxy
        rw [h'] at hN
        exact this hN
      exact this (congrArg DirectSumDecomposition.S h.symm)
  exact contra hmax

end Indecomposable

section

/- TODO in this section: construct the persistence module associated to a submodule,
and show that submodules that are atoms yield indecomposable persistence modules-/

end
