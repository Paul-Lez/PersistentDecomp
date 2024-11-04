import PHFormalisation.PersistenceSubmodule
import PHFormalisation.Mathlib.Order.Disjoint
import PHFormalisation.thm1_1with_decomp_struct

open CategoryTheory Classical CategoryTheory.Limits

variable {C : Type} [Category.{0, 0} C] {K : Type} [DivisionRing K] {M : FunctCat C K}

section DirectSumDecomposition

variable (M) in
@[ext]
structure DirectSumDecomposition where
  S : Set (PersistenceSubmodule M)
  h_indep : CompleteLattice.SetIndependent S
  h_top : sSup S = ⊤
  --(h : ∀ (x : C), DirectSum.IsInternal (M := M.obj x) (S := Submodule K (M.obj x))
    --(fun (p : PersistenceSubmodule M) (hp : p ∈ S) => p  x))
  not_bot_mem : ⊥ ∉ S


lemma DirectSumDecomposition.pointwise_iSup_eq_top (D : DirectSumDecomposition M)
  (x : C) : ⨆ (p : PersistenceSubmodule M) (_ : p ∈ D.S), p  x = ⊤ := sorry

lemma DirectSumDecomposition.pointwise_sSup_eq_top (D : DirectSumDecomposition M)
  (x : C) : ⨆ (p : PersistenceSubmodule M) (_ : p ∈ D.S), p  x = ⊤ := sorry


lemma DirectSumDecompositionIsInternal (I : DirectSumDecomposition M) (c : C) :
    DirectSum.IsInternal (M := M.obj c) (S := Submodule K (M.obj c)) fun p : I.S ↦ p.val c := by
  rw [DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top]
  constructor
  sorry
  sorry
  --rw [←iSup_apply, ←sSup_eq_iSup', I.h_top]
  --rfl

-- We should probably go for this definition instead of the one above
variable {M : FunctCat C K} in
def IsRefinement : DirectSumDecomposition M → DirectSumDecomposition M → Prop :=
  fun D₁ D₂ => ∀ N ∈ D₂.S, ∃ B ⊆ D₁.S, N = sSup B



variable {M : FunctCat C K} in
lemma RefinementMapSurj' (I : DirectSumDecomposition M) (J : DirectSumDecomposition M)
  (h : IsRefinement J I) : ∀ N : J.S, ∃ A : I.S, N.val ≤ A.val := by
  by_contra! h_contra
  rcases h_contra with ⟨N₀, h_not_le⟩
  have h_ge : N₀.val ⊔ sSup I.S ≤ sSup J.S := by
    rw [←sSup_pair]
    apply sSup_le_iff.mpr
    intro b h_mem
    rcases h_mem with ⟨h_n⟩
    · exact (le_sSup (h_n ▸ N₀.prop))
    · rename b ∈ {sSup I.S} => h_i
      have h' : sSup I.S ≤ sSup J.S := by
        rw [I.h_top, J.h_top]
      simp only [Set.mem_singleton_iff] at h_i
      exact (h_i ▸ h')
  let B : Set (PersistenceSubmodule M) := {C | ∃ A : I.S, C ≤ A.val ∧ C ∈ J.S}
  have h_sub : B ⊆ J.S := by
    intro C h_C_mem
    simp [B] at h_C_mem
    exact h_C_mem.right
  have h_aux : sSup B = sSup I.S := by
    apply le_antisymm
    apply sSup_le
    intro b h_mem
    simp [B] at h_mem
    rcases h_mem with ⟨h₁, _⟩
    rcases h₁ with ⟨a, h_a, h_le⟩
    exact (le_sSup_of_le h_a h_le)
    have h_le_subset : ∀ A : I.S, ∃ C ⊆ B, A ≤ sSup C := by
      intro A
      choose f hf hf' using h
      let C' := f A.val (A.prop)
      use C'
      constructor
      intro α h_α
      simp [B]
      constructor
      use A
      constructor
      exact A.prop
      rw [(hf' A.val A.prop)]
      exact (le_sSup h_α)
      exact ((hf A.val A.prop) h_α)
      rw [←(hf' A.val A.prop)]
    apply sSup_le
    intro A h_A_mem
    rcases h_le_subset ⟨A, h_A_mem⟩ with ⟨C, h_C⟩
    simp only at h_C
    exact le_trans h_C.right (sSup_le_sSup h_C.left)
  have h_aux' : N₀.val ∉ B := by
    intro h_contra
    simp [B] at h_contra
    rcases h_contra with ⟨A, h₁, h₂⟩
    exact (h_not_le (⟨A, h₁⟩) h₂)
  have h_disj : Disjoint N₀.val (sSup B) := by
    exact (CompleteLattice.SetIndependent.disjoint_sSup J.h_indep N₀.prop h_sub h_aux')
  have h_not_bot : N₀.val ≠ ⊥ := by
    intro h_contra
    exact J.not_bot_mem (h_contra ▸ N₀.prop)
  have h_gt : sSup I.S < N₀.val ⊔ sSup I.S := by
    rw [←h_aux]
    --No clue why I couldn't use this theorem from mathlib directly and had to copy paste it here instead
    --assuming it has to do with needing to bump
    exact (right_lt_sup_of_left_ne_bot h_disj h_not_bot)
  have contra : (⊤ : PersistenceSubmodule M) < ⊤ := by
    rw [I.h_top, J.h_top] at *
    apply lt_of_lt_of_le h_gt h_ge
  exact (lt_self_iff_false (⊤ : PersistenceSubmodule M)).mp contra


instance : Preorder (DirectSumDecomposition M) where
  le D₁ D₂ := IsRefinement D₂ D₁
  --D₁ ≤ D₂ iff D₂ refines D₁.
  le_refl D := by intro N _; use {N}; aesop
  le_trans I₁ I₂ I₃ h12 h23 := by
    intro N h_mem
    rcases (h12 N h_mem) with ⟨C, h_sub, h_eq⟩
    choose f hf hf' using h23
    let A := ⨆ (c : C), (f c.val (h_sub c.prop))
    use A
    constructor
    · apply iSup_le_iff.mpr
      intro c
      exact hf c.val (h_sub c.prop)
    · have h_aux' : sSup A = sSup C := by
        apply le_antisymm
        apply sSup_le_iff.mpr
        intro a h_a
        have h_aux'' : ∃ (c : C), a ∈ (f c.val (h_sub c.prop)) := by aesop
        rcases h_aux'' with ⟨c_a, h_ca⟩
        have h_le : a ≤ c_a := by
          rw [hf' c_a _]
          apply le_sSup h_ca
        apply le_sSup_of_le c_a.prop h_le
        apply sSup_le
        intro c h_mem_c
        let c' : C := ⟨c, h_mem_c⟩
        have h_le_c : c ≤ sSup (f c'.val (h_sub c'.prop)) := by
          rw [← (hf' c'.val (h_sub c'.prop))]
        apply le_trans h_le_c
        apply sSup_le
        intro a h_mem_a
        have h_a_in_A : a ∈ A := by
          have h_subs : (f c'.val (h_sub c'.prop)) ≤ A := by
            apply le_iSup_of_le c'
            exact le_rfl
          exact h_subs h_mem_a
        exact le_sSup h_a_in_A
      rwa [h_aux']


instance : PartialOrder (DirectSumDecomposition M) where
  --I suspect this will be painful to prove
  le_antisymm := by
    intro I J h_I_le_J h_J_le_I
    have h_final_left : ∀ N ∈ J.S, N ∈ I.S := by
      intro N
      by_contra h_neg
      push_neg at h_neg
      rcases h_neg with ⟨h_N_in_J, h_N_not_in_I⟩
      let N' : J.S := ⟨N, h_N_in_J⟩
      have h_A : ∃ A : I.S, N ≤ A.val := by
        exact (RefinementMapSurj' I J h_I_le_J) N'
      rcases h_A with ⟨A, h_N_le_A⟩
      choose f hf hf' using h_J_le_I
      let B := f N'.val N'.prop
      let h_B₁ := hf' N'.val N'.prop
      let h_B₂ := hf N'.val N'.prop
      simp only at h_B₁
      have h_mem : A.val ∈ B := by
        by_contra h_A_not_mem
        have h_aux : Disjoint A.val (sSup B) := by
          exact (CompleteLattice.SetIndependent.disjoint_sSup I.h_indep A.prop h_B₂ h_A_not_mem)
        have h_aux' : sSup B ≤ A.val := by
          exact (h_B₁ ▸ h_N_le_A)
        have h_last : sSup B = (⊥ : PersistenceSubmodule M) := by
          rw [disjoint_comm] at h_aux
          exact (Disjoint.eq_bot_of_le h_aux h_aux')
        rw [←h_B₁] at h_last
        subst h_last
        exact (J.not_bot_mem h_N_in_J)
      have h_A_le_N : A.val ≤ N := by
        rw [h_B₁]
        exact le_sSup h_mem
      have h_A_eq_N : A.val = N := by
        exact (le_antisymm h_A_le_N h_N_le_A)
      have h_contra : N ∈ I.S := by
        exact h_A_eq_N ▸ A.prop
      aesop
    have h_final_right : ∀ N ∈ I.S, N ∈ J.S := by
      sorry
    aesop

end DirectSumDecomposition
