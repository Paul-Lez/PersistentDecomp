import Mathlib.Algebra.Category.ModuleCat.Abelian
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
lemma PH.Submodule.ext' {N₁ N₂ : Submodule M} (h :
  ∀ x, N₁.mods x = N₂.mods x) : N₁ = N₂ := by
  aesop

-- Persistence submodules are ordered by pointwise inclusion
instance Submod_le : PartialOrder (PH.Submodule M) where
  le N₁ N₂ := ∀ x, N₁.mods x ≤ N₂.mods x
  le_refl N := fun x => le_refl _
  le_trans N₁ N₂ N₃ h h' x := le_trans (h x) (h' x)
  le_antisymm N₁ N₂ h h' := PH.Submodule.ext' _ (fun x => le_antisymm (h x) (h' x))

/- There's a notion of the supremum of two submodules, given by `⊕`,
and a notion of an infimum, given by `∩`.-/
instance : Lattice (PH.Submodule M) where
  sup N₁ N₂ := {
    mods := fun x => (N₁.mods x) ⊔ (N₂.mods x)
    h_mods := by
      intro x y f
      rw [Submodule.map_sup]
      apply sup_le_sup (N₁.h_mods f) (N₂.h_mods f) }
  le_sup_left a b x := by aesop
  le_sup_right a b x := by aesop
  sup_le a b c h h' x := by aesop
  inf N₁ N₂ := {
    mods := fun x => (N₁.mods x) ⊓ (N₂.mods x)
    h_mods := by
      intro x y f
      apply le_trans (Submodule.map_inf_le _) (inf_le_inf (N₁.h_mods f) (N₂.h_mods f)) }
  inf_le_left a b x := by aesop
  inf_le_right a b x := by aesop
  le_inf a b c h h' x := by aesop

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
    (sSup S).map f = sSup (map f '' S) := by
  rw [(gc_map_comap f : GaloisConnection (map f) (comap f)).l_sSup, sSup_eq_iSup', iSup_subtype, iSup_image]

lemma Submodule.map_sInf (f : F) (S : Set (Submodule R M)) :
    (sInf S).map f ≤ sInf (map f '' S) := by
  rw [(gc_map_comap f).le_iff_le, (gc_map_comap f).u_sInf, iInf_image, sInf_eq_iInf, iInf_subtype',  iInf_subtype']
  apply iInf_mono (fun i => (gc_map_comap f).le_u_l _)

end

-- There's a notion of supremum over arbitrary sets of submodules
@[simp]
instance : SupSet (PH.Submodule M) where
  sSup S := {
    -- The direct sum over arbitrary sets is just the pointwise direct sum
    mods := fun x => sSup {(N.mods x) | (N : PH.Submodule M) (_ : N ∈ S)}
    h_mods := by
      intro x y f
      rw [Submodule.map_sSup]
      sorry }

-- There's a notion of infimums over arbitrary sets of submodules
@[simp]
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



-- API to simplify using ≤ on submodules

-- A submodule is less than another if and only if every single submodule is LE
lemma le_PH_submod_implies_le_submod (A B : PH.Submodule M) (h_le : B ≤ A)
  : ∀ X : C, B.mods X ≤ A.mods X := by
  intro X
  simp [LE.le] at *
  exact (h_le X)

-- Reciprocal of the above
lemma le_submod_implies_le_PH_submod (A B : PH.Submodule M) (h_le : ∀ X : C, B.mods X ≤ A.mods X)
  : B ≤ A := by
  simp [LE.le]
  intro X x h_mem
  exact (h_le X h_mem)

-- If S is a set of PH.Submodule, then ⨆ (p : S), (p.val.mods X) = (⨆ (p : S), p.val).mods X
-- In other words, we can take Sup and mods in whichever order we want.
lemma sup_comm_mods (S : Set (PH.Submodule M))
  : ⨆ (p : S), (p.val.mods X) = (⨆ (p : S), p.val).mods X := by
  apply le_antisymm
  · simp [iSup]
    rw [sSup_eq_iSup']
    intro p h_mem
    have h_aux : p.mods X ∈ {x | ∃ N ∈ S, N.mods X = x} := by
      simp; use p
    let p_aux : {x | ∃ N ∈ S, N.mods X = x} := ⟨p.mods X, h_aux⟩
    apply le_iSup_of_le p_aux; simp
  · simp [iSup]
    simp only [sSup_eq_iSup]
    intro p h_mem
    apply le_iSup_iff.mpr
    simp
    intro B h_le
    exact (h_le p h_mem)


-- The sups and infs over possibly infinite sets are compatible with the lattice structure
instance : CompleteLattice (PH.Submodule M) where
  le_sSup := by
    intro S A h_mem
    apply le_submod_implies_le_PH_submod
    intro X
    -- maybe write some API to get rid of these annoying sSups without
    -- resorting to the simp nuke?
    simp
    let A' : {x | ∃ N ∈ S, N.mods X = x} := ⟨A.mods X, by simp; use A⟩
    apply le_sSup_of_le (A'.prop) (by simp)
  sSup_le := by
    intro S A h_le
    apply le_submod_implies_le_PH_submod
    intro X
    simp
    intro a h_mem_a
    exact h_le a h_mem_a X
  sInf_le := by
    intro S A h_mem
    apply le_submod_implies_le_PH_submod
    intro X
    simp
    let A' : {x | ∃ N ∈ S, N.mods X = x} := ⟨A.mods X, by simp; use A⟩
    apply sInf_le_of_le A'.prop
    rfl
  le_sInf := by
    intro S A h_le
    apply le_submod_implies_le_PH_submod
    intro X
    simp
    intro a h_mem_a
    exact h_le a h_mem_a X
  le_top := by
    intro A
    apply le_submod_implies_le_PH_submod
    intro X
    exact le_top
  bot_le := by
    intro A
    apply le_submod_implies_le_PH_submod
    intro X
    exact bot_le

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
  apply le_antisymm; simp
  simp only [LE.le]
  intro X x h_mem
  have h_sum := D.h X
  by_contra h_neq
  apply DirectSum.IsInternal.submodule_iSup_eq_top at h_sum
  rw [sSup_eq_iSup'] at h_neq
  replace h_mem : x ∈ (⊤ : Submodule K _) := by
    exact h_mem
  have h_contra : x ∈ (⨆ (p : D.S), p.val).mods X := by
    rw[←sup_comm_mods]
    /-
    rw [←h_sum] at h_mem; simp [iSup]
    have h_sub : (⨆ (p : D.S), (p.val.mods X)) ≤ sSup {x | ∃ N ∈ D.S, N.mods X = x} := by

      rw [sSup_eq_iSup']
      apply iSup_le; intro p
      have h_aux : p.val.mods X ∈ {x | ∃ N ∈ D.S, N.mods X = x} := by
        simp; use p; simp
      let p_aux : {x | ∃ N ∈ D.S, N.mods X = x} := ⟨p.val.mods X, h_aux⟩
      apply le_iSup_of_le p_aux; simp
      -/
    rwa [h_sum]
  exact (h_neq h_contra)

--careful: this means that D₁ refines D₂
variable {M : FunctCat C K} in
def IsRefinement : DirectSumDecomposition M → DirectSumDecomposition M → Prop :=
  fun D₁ D₂ => ∃ d : D₂.S → Set (PH.Submodule M), (∀ (N : D₂.S), N.val = sSup ((d N))) ∧ (∀ N, d N ⊆ D₁.S)

--API
--The goal of these API lemmas is to obtain the proof for the remaining "sorry"
--in ToTypeCat. In other words, need to show that the d function is surjective.
--To do this, assume it isn't surjective, then show it contradicts N being direct sum
variable {M : FunctCat C K} in
lemma NissSupImage {I : DirectSumDecomposition M}
  {d : I.S → Set (PH.Submodule M)}
  (h_eq : ∀ (B : I.S), B = sSup (d B))
   : ⊤ = ⨆ B, sSup (d B) := by
  have h_aux : ⊤ = sSup I.S := (sSup_eq_top_of_direct_sum_decomposition I).symm
  have h_supI : ⊤ = ⨆ (B: I.S), B.val := by rwa[sSup_eq_iSup'] at h_aux
  have h_equality : ∀ (B : I.S), id B = (sSup ∘ d) B := by
    simp only [id_eq, h_eq, Function.comp_apply, implies_true]
  have h_auxx : ⨆ (B : I.S), (id B).val = ⨆ B, (sSup ∘ d) B := by rw[iSup_congr h_equality]
  --rw is too limited to solve at this point
  simp_rw[h_supI]
  exact h_auxx

--J refines I
variable {M : FunctCat C K} in
lemma RefinementMapSurj (I : DirectSumDecomposition M) (J : DirectSumDecomposition M)
  (h : IsRefinement J I) {d : I.S → Set (PH.Submodule M)} {h_eq : ∀ (B : I.S), B = sSup (d B)}
  {h_sub :  ∀ (B : I.S), d B ⊆ J.S} : (∀ (A : J.S), ∃ (B : I.S), A.val ∈ d B) := by
  by_contra! h_abs
  let f_aux : J.S → _ := fun (A : J.S) => if ∃ B : I.S, A.val ∈ d B then A.val else ⊥
  have h_dir_sum_J : ⊤ = sSup J.S := (sSup_eq_top_of_direct_sum_decomposition J).symm
  have h_dir_sum_d : ⊤ = ⨆ (A : J.S), f_aux A := by
    have h_aux (B : I.S) : sSup (d B) = ⨆ A ∈ d B, A := sSup_eq_iSup
    simp_rw [NissSupImage h_eq]
    --we prove this equality by using antisymmetry of ≤.
    apply le_antisymm
    apply iSup_le_iff.mpr
    intro B
    rw[sSup_eq_iSup]
    apply iSup_le
    intro α
    by_cases h_memb : α ∈ d B
    simp only [h_memb, iSup_pos]
    have h_surj : ∃ A : J.S, A.val = α := by
      simpa only [Subtype.exists, exists_prop, exists_eq_right]
        using Set.mem_of_mem_of_subset h_memb (h_sub B)
    rcases h_surj with ⟨A_alph, h_equal⟩
    have h_alpha_le : α ≤ f_aux A_alph := by
      have h_exists_val : ∃ (B : I.S), A_alph.val ∈ d B := by
        use B
        rwa [h_equal]
      simpa only [f_aux, h_exists_val, ←h_equal,  ↓reduceIte, ge_iff_le] using le_refl α
    apply le_iSup_of_le A_alph h_alpha_le
    --the line above closes the first case of by_cases.
    simp only [h_memb, not_false_eq_true, iSup_neg, bot_le]
    --and this one is enough to close the second.
    --Now we prove the other direction of the inequality.
    apply iSup_le
    intro α
    by_cases h_memb : ∃ B₀ : I.S, α.val ∈ d B₀
    · simp only [f_aux, h_memb, ↓reduceIte]
      rcases h_memb with ⟨B₀, h_in⟩
      have h_aux_le : α.val ≤ sSup (d B₀) := le_sSup h_in
      apply le_iSup_of_le
      exact h_aux_le
    --the first case of by_cases is closed now.
    · simp only [f_aux, h_memb, ↓reduceIte, bot_le]
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
        · simp only [h_AIsImage, ↓reduceIte, le_top]
        · simp only [h_AIsImage, ↓reduceIte, h_dir_sum_J, bot_le]
      exact h ▸ iSup_le h_sup
    · rw [Set.mem_singleton_iff.mp h, h_dir_sum_J]
      apply le_iSup
  have h_aux : ⨆ A, f_aux A < ⊤ := lt_of_lt_of_le h_lt h_le
  simp only [←h_dir_sum_d, ←h_dir_sum_J, lt_self_iff_false] at h_aux

instance : Preorder (DirectSumDecomposition M) where
  le D₁ D₂ := IsRefinement D₁ D₂
  --D₁ ≤ D₂ iff D₁ refines D₂. This is not the order from the paper, but its dual.
  le_refl D := by use fun (I : D.S) ↦ {I.val}, by aesop, by aesop
  le_trans I₁ I₂ I₃ h12 h23 := by
    rcases h12  with ⟨d₁, h₁eq, h₁sub⟩
    rcases h23 with ⟨d₂, h₂eq, h₂sub⟩
    let d := fun (A : I₃.S) ↦ {(C) | (C : PH.Submodule M) (_ : ∃ B : I₂.S, C ∈ d₁ B ∧ B.val ∈ d₂ A)}
    use d, fun A => ?_ , fun A x ⟨a, ⟨B, d, _⟩, c⟩ => Set.mem_of_mem_of_subset (c ▸ d) (h₁sub B)
    have h_chara_dA  (B : I₂.S) (h_B_im : B.val ∈ d₂ A) (C) (h_C_im : C ∈ (d₁ B)) : C ∈ d A:= by
      simp only [Subtype.exists, exists_and_right, exists_prop, exists_eq_right, Set.mem_setOf_eq, d]
      use B
      simpa only [Subtype.coe_eta, Subtype.coe_prop, exists_const] using ⟨h_C_im, h_B_im⟩
    apply le_antisymm
    · apply h₂eq A ▸ sSup_le_iff.mpr (fun B h_B_im => ?_)
      set B' : I₂.S := ⟨B, Set.mem_of_mem_of_subset h_B_im (h₂sub A)⟩
      apply h₁eq B' ▸ sSup_le_iff.mpr (fun C h_C_im => (le_sSup (h_chara_dA B' h_B_im C h_C_im)))
    · apply sSup_le_iff.mpr (fun C h_C_im => ?_)
      simp only [Subtype.exists, exists_and_right, exists_prop, exists_eq_right, Set.mem_setOf_eq,
        d] at h_C_im
      rcases h_C_im with ⟨B, ⟨h_B_in_I2, h_C_im_B⟩, h_B_im⟩
      apply le_trans (h₁eq ⟨B, h_B_in_I2⟩ ▸ le_sSup h_C_im_B) (h₂eq A ▸ le_sSup h_B_im)

instance : PartialOrder (DirectSumDecomposition M) where
  --I suspect this will be painful to prove
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
noncomputable def ChainToTypeCat (T : Set (DirectSumDecomposition M)) :
  Subtype T ⥤ Type where
  obj D := ToTypeCat.obj D.val
  map {J I} f := ToTypeCat.map f
  map_id := by
    dsimp
    intro I
    rw [←ToTypeCat.map_id]
    rfl
  map_comp := by
    dsimp
    intro I J K f g
    rw [←ToTypeCat.map_comp]
    rfl


/- Construct the element `L` (in the notation of our doc) -/
def ChainToInverseLimit (T : Set (DirectSumDecomposition M)) :
  Type := limit (ChainToTypeCat T)


variable (N : PH.Submodule M) (T : Set (DirectSumDecomposition M)) (F := (ChainToTypeCat T)) (l : limit (ChainToTypeCat T))
variable (I : Subtype T)
variable (D : DirectSumDecomposition M)
#check (limit.π (ChainToTypeCat T)) --this is the morphism L ⟶ ChainToTypeCat.obj I
#check ((limit.π (ChainToTypeCat T) I) l) -- apply this morphism to l. This has type (ChainToTypeCat T).obj I - other words, Subtype I.val.S
#check ((limit.π (ChainToTypeCat T) I) l).val --PH.Submodule
#check ((limit.π (ChainToTypeCat T) I) l).prop
#check (ChainToTypeCat T)
#check I.val
#check F
#check F.obj I



/-Construct `M[λ]` in the notation of our doc -/
variable {M} in
noncomputable def Submodule_of_chain {T : Set (DirectSumDecomposition M)} (hT : IsChain
  LE.le T) (l : limit (ChainToTypeCat T)) : PH.Submodule M := by
  let f : Subtype T → PH.Submodule M := fun (I : Subtype T) ↦ ((limit.π (ChainToTypeCat T) I) l).val
  let M_l : (PH.Submodule M) := ⨅ (I : Subtype T), f I
  exact M_l



/-`M` is the direct sum of all the `M[λ]` -/
variable {M} in
lemma M_is_dir_sum_lambdas {T : Set (DirectSumDecomposition M)} (hT : IsChain
  LE.le T) (x : C) :
  DirectSum.IsInternal (fun (l : limit (ChainToTypeCat T)) => ((Submodule_of_chain hT l).mods x : Submodule K (M.obj x))) := by
  apply (DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top _).mpr
  sorry

/- Get a direct sum out of a chain (this should be the index set 𝓤 in out doc)-/
variable {M} in
def DirectSumDecomposition_of_chain {T : Set (DirectSumDecomposition M)} (hT : IsChain
  LE.le T) : DirectSumDecomposition M where
  S := {(Submodule_of_chain hT l) | (l : limit (ChainToTypeCat T)) (_ : ¬ IsBot (Submodule_of_chain hT l))}
  h := sorry

/- The set `𝓤` is an upper bound for the chain `T` -/
lemma every_chain_has_an_upper_bound (N : PH.Submodule M)
  {T : Set (DirectSumDecomposition M)} (hT : IsChain LE.le T) :
  ∀ D ∈ T, D ≤ DirectSumDecomposition_of_chain hT := by
  sorry

/-Every chain has an upper bound, hence there is a maximal direct sum decomposition `D`-/
lemma zorny_lemma (N : PH.Submodule M) : ∃ (D : DirectSumDecomposition M), IsMax D := by
  apply zorn_le
  rintro T hT
  rw [bddAbove_def]
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
    intro x'
    rw [DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top]
    constructor
    · --this is going to be a bit of a pain to prove
      intro a b hab hb'
      by_cases ha : a = x
      · have : b ≤ N.mods x' := le_trans (ha ▸ hab) (hx' x')
        --this should now follow from the independence of the direct sum decomposition `D`
        --have := calc b ≤ (⨆ j, ⨆ (_ : j ≠ a), (fun (p : S) ↦ p.val.mods x') j) := by sorry
        --_ ≤ (⨆ j, ⨆ (_ : j ≠ a), (fun (p : D.S) ↦ p.val.mods x') j)
        sorry
      · by_cases hb : a = y
        · have : b ≤ N.mods x' := le_trans (hb ▸ hab) (hy' x')
          --this should now follow from the independence of the direct sum decomposition `D`
          sorry
          --Since the sum is over j ≠ a, it will include `x ⊔ y = N` so we can rewrite it in a nicer way
        · have : (⨆ j, ⨆ (_ : j ≠ a), (fun (p : S) ↦ p.val.mods x') j) =
            ⨆ j, ⨆ (_ : j.val ≠ a.val), (fun (p : D.S) => p.val.mods x') j := by
            sorry
          --this should now follow from the independence of the direct sum decomposition `D`
          rw [this] at hb'
          sorry
      --The direct sum is indexed over all `j` in `S` so we can rewrite it in a nicer way by using `x ⊔ y = N`.
    · calc (⨆ (p : S), p.val.mods x') = (⨆ (p : D.S), p.val.mods x') := by sorry
      _ = ⊤ := by
        apply ((DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top _).mp <| D.h x').right
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
