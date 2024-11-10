import Mathlib.Algebra.DirectSum.Module
import PersistentDecomp.Mathlib.Order.Disjoint
import PersistentDecomp.Prereqs.Indecomposable
import PersistentDecomp.Prereqs.PersistenceSubmodule

open CategoryTheory Classical CategoryTheory.Limits DirectSum
open CompleteLattice hiding sSup_le -- TODO: Fix in mathlib

variable {C : Type} [Category.{0, 0} C] {K : Type} [DivisionRing K] {M : C ⥤ ModuleCat K}

section DirectSumDecomposition

variable (M) in
@[ext]
structure DirectSumDecomposition where
  carrier : Set (PersistenceSubmodule M)
  setIndependent' : SetIndependent carrier
  sSup_eq_top' : sSup carrier = ⊤
  --(h : ∀ (x : C), DirectSum.IsInternal (M := M.obj x) (S := Submodule K (M.obj x))
    --(fun (p : PersistenceSubmodule M) (hp : p ∈ S) => p  x))
  not_bot_mem' : ⊥ ∉ carrier

namespace DirectSumDecomposition

instance : SetLike (DirectSumDecomposition M) (PersistenceSubmodule M) where
  coe := carrier
  coe_injective' D₁ D₂ := by cases D₁; cases D₂; sorry

attribute [-instance] SetLike.instPartialOrder

lemma setIndependent (D : DirectSumDecomposition M) : SetIndependent (SetLike.coe D) :=
  D.setIndependent'

lemma sSup_eq_top (D : DirectSumDecomposition M) : sSup (SetLike.coe D) = ⊤ := D.sSup_eq_top'
lemma not_bot_mem (D : DirectSumDecomposition M) : ⊥ ∉ D := D.not_bot_mem'

lemma pointwise_iSup_eq_top (D : DirectSumDecomposition M) (x : C) : ⨆ p ∈ D, p x = ⊤ := sorry

lemma pointwise_sSup_eq_top (D : DirectSumDecomposition M) (x : C) : ⨆ p ∈ D, p x = ⊤ := sorry

lemma isInternal (I : DirectSumDecomposition M) (c : C) :
    IsInternal (M := M.obj c) (S := Submodule K (M.obj c)) fun p : I ↦ p.val c := by
  rw [DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top]
  constructor
  sorry
  sorry
  --rw [← iSup_apply, ← sSup_eq_iSup', I.sSup_eq_top]
  --rfl

-- We should probably go for this definition instead of the one above
variable {M : C ⥤ ModuleCat K} in
def IsRefinement (D₁ D₂ : DirectSumDecomposition M) : Prop :=
  ∀ ⦃N⦄, N ∈ D₂ → ∃ B : Set (PersistenceSubmodule M), B ⊆ D₁ ∧ N = sSup B

variable {M : C ⥤ ModuleCat K} in
lemma RefinementMapSurj' (I : DirectSumDecomposition M) (J : DirectSumDecomposition M)
  (h : IsRefinement J I) : ∀ N : J, ∃ A : I, N.val ≤ A.val := by
  by_contra! h_contra
  rcases h_contra with ⟨N₀, h_not_le⟩
  have h_ge : N₀.val ⊔ sSup I ≤ sSup J := by
    rw [← sSup_pair]
    apply sSup_le_iff.mpr
    intro b h_mem
    rcases h_mem with ⟨h_n⟩
    · exact (le_sSup (h_n ▸ N₀.prop))
    · rename b ∈ {sSup (SetLike.coe I)} => h_i
      have h' : sSup (SetLike.coe I) ≤ sSup J := by
        rw [I.sSup_eq_top, J.sSup_eq_top]
      simp only [Set.mem_singleton_iff] at h_i
      exact (h_i ▸ h')
  let B : Set (PersistenceSubmodule M) := {C | ∃ A : I, C ≤ A.val ∧ C ∈ J}
  have h_sub : B ⊆ J := by
    intro C h_C_mem
    simp [B] at h_C_mem
    exact h_C_mem.right
  have h_aux : sSup B = sSup I := by
    apply le_antisymm
    apply sSup_le
    intro b h_mem
    simp [B] at h_mem
    rcases h_mem with ⟨h₁, _⟩
    rcases h₁ with ⟨a, h_a, h_le⟩
    exact (le_sSup_of_le h_a h_le)
    have h_le_subset : ∀ A : I, ∃ C ⊆ B, A ≤ sSup C := by
      intro A
      choose f hf hf' using h
      let C' := f (A.prop)
      use C'
      constructor
      intro α h_α
      simp [B]
      constructor
      use A
      constructor
      exact A.prop
      rw [(hf' A.prop)]
      exact (le_sSup h_α)
      exact ((hf A.prop) h_α)
      rw [← (hf' A.prop)]
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
    exact (SetIndependent.disjoint_sSup J.setIndependent' N₀.prop h_sub h_aux')
  have h_not_bot : N₀.val ≠ ⊥ := by
    intro h_contra
    exact J.not_bot_mem (h_contra ▸ N₀.prop)
  have h_gt : sSup I < N₀.val ⊔ sSup I := by
    rw [← h_aux]
    --No clue why I couldn't use this theorem from mathlib directly and had to copy paste it here instead
    --assuming it has to do with needing to bump
    exact (right_lt_sup_of_left_ne_bot h_disj h_not_bot)
  have contra : (⊤ : PersistenceSubmodule M) < ⊤ := by
    rw [I.sSup_eq_top, J.sSup_eq_top] at *
    apply lt_of_lt_of_le h_gt h_ge
  exact (lt_self_iff_false (⊤ : PersistenceSubmodule M)).mp contra


instance : Preorder (DirectSumDecomposition M) where
  le D₁ D₂ := IsRefinement D₂ D₁
  --D₁ ≤ D₂ iff D₂ refines D₁.
  le_refl D := by intro N _; use {N}; aesop
  le_trans I₁ I₂ I₃ h12 h23 := by
    intro N h_mem
    rcases (h12 h_mem) with ⟨C, h_sub, h_eq⟩
    choose f hf hf' using h23
    let A := ⨆ (c : C), (f (h_sub c.prop))
    use A
    constructor
    · apply iSup_le_iff.mpr
      intro c
      exact hf (h_sub c.prop)
    · have h_aux' : sSup A = sSup C := by
        apply le_antisymm
        apply sSup_le_iff.mpr
        intro a h_a
        have h_aux'' : ∃ (c : C), a ∈ (f (h_sub c.prop)) := by aesop
        rcases h_aux'' with ⟨c_a, h_ca⟩
        have h_le : a ≤ c_a := by
          rw [hf' (N := c_a)]
          apply le_sSup h_ca
        apply le_sSup_of_le c_a.prop h_le
        apply sSup_le
        intro c h_mem_c
        let c' : C := ⟨c, h_mem_c⟩
        have h_le_c : c ≤ sSup (f (h_sub c'.prop)) := by
          rw [← hf' (h_sub c'.prop)]
        apply le_trans h_le_c
        apply sSup_le
        intro a h_mem_a
        have h_a_in_A : a ∈ A := by
          have h_subs : f (h_sub c'.prop) ≤ A := by
            apply le_iSup_of_le c'
            exact le_rfl
          exact h_subs h_mem_a
        exact le_sSup h_a_in_A
      rwa [h_aux']

instance : PartialOrder (DirectSumDecomposition M) where
  --I suspect this will be painful to prove
  le_antisymm := by
    intro I J h_I_le_J h_J_le_I
    have h_final_left : ∀ N ∈ J, N ∈ I := by
      intro N
      by_contra h_neg
      push_neg at h_neg
      rcases h_neg with ⟨h_N_in_J, h_N_not_in_I⟩
      let N' : J := ⟨N, h_N_in_J⟩
      have h_A : ∃ A : I, N ≤ A.val := by
        exact (RefinementMapSurj' I J h_I_le_J) N'
      rcases h_A with ⟨A, h_N_le_A⟩
      choose f hf hf' using h_J_le_I
      let B := f N'.prop
      let h_B₁ := hf' N'.prop
      let h_B₂ := hf N'.prop
      simp only at h_B₁
      have h_mem : A.val ∈ B := by
        by_contra h_A_not_mem
        have h_aux : Disjoint A.val (sSup B) := by
          exact (I.setIndependent.disjoint_sSup A.prop h_B₂ h_A_not_mem)
        have h_aux' : sSup B ≤ A.val := h_B₁ ▸ h_N_le_A
        have h_last : sSup B = (⊥ : PersistenceSubmodule M) := by
          rw [disjoint_comm] at h_aux
          exact (Disjoint.eq_bot_of_le h_aux h_aux')
        rw [← h_B₁] at h_last
        subst h_last
        exact (J.not_bot_mem h_N_in_J)
      have h_A_le_N : A.val ≤ N := by
        rw [h_B₁]
        exact le_sSup h_mem
      have h_A_eq_N : A.val = N := by
        exact (le_antisymm h_A_le_N h_N_le_A)
      have h_contra : N ∈ I := by
        exact h_A_eq_N ▸ A.prop
      aesop
    have h_final_right : ∀ N ∈ I, N ∈ J := by
      sorry
    aesop

section Indecomposable
variable {D : DirectSumDecomposition M}

/--
If `D` is a direct sum decomposition of `M` and for each `N` appearing in `S` we are given a direct
sum decomposition of `N`, we can construct a refinement of `D`.
-/
def refinement (B : ∀ N ∈ D, Set (PersistenceSubmodule M))
    (hB : ∀ N hN, N = sSup (B N hN)) (hB' : ∀ N hN, SetIndependent (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) : DirectSumDecomposition M where
  carrier := ⋃ N, ⋃ hN, B N hN
  setIndependent' x hx a ha ha' := by
    sorry
  sSup_eq_top' := by
    sorry
  not_bot_mem' := by simp [Set.mem_iUnion, hB'']

lemma refinement_le (B : ∀ N ∈ D, Set (PersistenceSubmodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, SetIndependent (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) :
    refinement B hB hB' hB'' ≤ D := sorry

lemma refinement_lt_of_exists_ne_singleton (B : ∀ N ∈ D, Set (PersistenceSubmodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, SetIndependent (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN)
    (H : ∃ (N : PersistenceSubmodule M) (hN : N ∈ D), B N hN ≠ {N}) :
    refinement B hB hB' hB'' < D := sorry

lemma Indecomposable_of_mem_Min_Direct_sum_decomposition
    (D : DirectSumDecomposition M) (N : PersistenceSubmodule M) (hN : N ∈ D) (hmax : IsMin D) :
    Indecomposable N := by
  by_contra hNotMax
  simp only [_root_.Indecomposable, not_forall, Classical.not_imp, not_or] at hNotMax
  obtain ⟨x, y, hxy, rfl, hx, hy⟩ := hNotMax
  let B (N) (hN : N ∈ D) : Set (PersistenceSubmodule M) := if N = x ⊔ y then {x, y} else {N}
  set newD : DirectSumDecomposition M := refinement
    B sorry sorry sorry
  have contra : ¬ IsMin D := by
    simp only [not_isMin_iff]
    use newD
    apply refinement_lt_of_exists_ne_singleton
    use x ⊔ y, hN
    simp only [B, if_true]
    intro h
    --This should be easy
    sorry
  sorry

-- /-- If `N` is a submodule of `M` that is part of a minimal direct sum decomposition, then `N` is indecomposable -/
-- lemma Indecomposable_of_mem_Min_Direct_sum_decomposition'
--   (D : DirectSumDecomposition M) (N : PersistenceSubmodule M) (hN : N ∈ D) (hmax : IsMin D) : Indecomposable N := by
--   by_contra hNotMax
--   rw [Indecomposable] at hNotMax
--   simp only [not_forall, Classical.not_imp, not_or, exists_and_left] at hNotMax
--   obtain ⟨x, hx, y, hx', hy', hxy, hxy', hy⟩ := hNotMax
--   set newD : DirectSumDecomposition M := refinement
--     (fun (M : PersistenceSubmodule M) (hM : M ∈ D) => if M = N then {x, y} else {M}) sorry sorry sorry

--   set S : Set (PersistenceSubmodule M) := (D \ {N}) ∪ {x, y} with hS
--   have h : ∀ (x : C), IsInternal (fun p : S => (p.val  x : Submodule _ _)) := by
--     intro x'
--     rw [isInternal_submodule_iff_independent_and_iSup_eq_top]
--     constructor
--     · --this is going to be a bit of a pain to prove
--       intro a b hab hb'
--       by_cases ha : a = x
--       · have : b ≤ N  x' := le_trans (ha ▸ hab) (hx' x')
--         --this should now follow from the independence of the direct sum decomposition `D`
--         --have := calc b ≤ (⨆ j, ⨆ (_ : j ≠ a), (fun (p : S) ↦ p.val  x') j) := by sorry
--         --_ ≤ (⨆ j, ⨆ (_ : j ≠ a), (fun (p : D) ↦ p.val  x') j)
--         sorry
--       · by_cases hb : a = y
--         · have : b ≤ N  x' := le_trans (hb ▸ hab) (hy' x')
--           --this should now follow from the independence of the direct sum decomposition `D`
--           sorry
--           --Since the sum is over j ≠ a, it will include `x ⊔ y = N` so we can rewrite it in a nicer way
--         · have : (⨆ j, ⨆ (_ : j ≠ a), (fun (p : S) ↦ p.val  x') j) =
--             ⨆ j, ⨆ (_ : j.val ≠ a.val), (fun (p : D) => p.val  x') j := by
--             sorry
--           --this should now follow from the independence of the direct sum decomposition `D`
--           rw [this] at hb'
--           sorry
--       --The direct sum is indexed over all `j` in `S` so we can rewrite it in a nicer way by using `x ⊔ y = N`.
--     · calc (⨆ (p : S), p.val  x') = (⨆ (p : D), p.val  x') := by sorry
--       _ = ⊤ := ((isInternal_submodule_iff_independent_and_iSup_eq_top _).mp <| D.h x').right
--   let Cex : DirectSumDecomposition M := ⟨S, h, sorry⟩
--   have contra : ¬ IsMin D := by
--     simp only [not_isMin_iff]
--     use Cex
--     apply lt_of_le_of_ne
--     --this is very golfable
--     · set d : D → Set (PersistenceSubmodule M) := fun (I : D) ↦ if I.val = N then {x, y} else {I.val} with hd
--       use d, fun I => ?_, fun I => ?_
--       · by_cases hI : I.val = N
--         · simp only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton, ←  hxy']
--         · simp only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton]
--       · by_cases hI : I.val = N
--         · simpa only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton, hS] using Set.subset_union_right
--         · simp only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton, Set.singleton_subset_iff]
--           apply Set.mem_union_left _ (Set.mem_diff_of_mem I.prop _)
--           rw [Set.mem_singleton_iff]
--           exact hI
--     · --this can probably be golfed with the right API
--       intro h
--       have : D ≠ Cex := by
--         simp only [ne_eq]
--         intro h'
--         have: N ∉ S := by
--           intro h''
--           rw [hS, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_diff, Set.mem_singleton_iff] at h''
--           simp only [not_true_eq_false, and_false, false_or] at h''
--           rcases h'' with h'' | h''
--           · rw [← h'', inf_eq_right.mpr hy'] at hxy
--             exact hy hxy
--           · rw [← h'', inf_eq_left.mpr hx'] at hxy
--             exact hx hxy
--         rw [h'] at hN
--         exact this hN
--       exact this (congrArg DirectSumDecomposition h.symm)
--   exact contra hmax

end Indecomposable

end DirectSumDecomposition
