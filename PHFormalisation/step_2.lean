import Mathlib.Algebra.DirectSum.Module
import PHFormalisation.DirectSumDecomposition


open CategoryTheory Classical CategoryTheory.Limits
open Filter


variable {C : Type} [Category.{0, 0} C] {K : Type} [DivisionRing K] (M : FunctCat C K)

/- In this file we sketch what we'll need to prove to
get Step 2 done. Most of the work is setting the stage so
we can apply Zorn's lemma.-/

/- For now we work with types in the 0-th universe. To make the code universe polymorphic we'll need to
make a few edits below-/

section Chains

/- In this section we set up what's needed to take an inverse limit of direct sum
decompositions. Since these are defined in terms of sets, we could construct the
inverse limit explicitly but I think this would be really painful and messy...-/

-- Here we write some code to go from chains in directSumDecompositions to diagrams in the category of types
variable {M} in
noncomputable def ToTypeCat : (DirectSumDecomposition M) ⥤ Type where
  obj D := Subtype D.S
  -- Define the maps f_{IJ} induced by "J refines I"
  map {I J} f := by
    dsimp
    let h_le := leOfHom f
    let g : J.S → I.S := fun N => (RefinementMapSurj' I J h_le N).choose
    sorry
    --exact g is what we want but this is wrong arrow direction


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


variable (N : PH.Submodule M) (T : Set (DirectSumDecomposition M)) (l : limit (ChainToTypeCat T))
variable (I : Subtype T)
variable (D : DirectSumDecomposition M)
#check (limit.π (ChainToTypeCat T)) --this is the morphism L ⟶ ChainToTypeCat.obj I
#check ((limit.π (ChainToTypeCat T) I) l) -- apply this morphism to l. This has type (ChainToTypeCat T).obj I - other words, Subtype I.val.S
#check ((limit.π (ChainToTypeCat T) I) l).val --PH.Submodule
#check ((limit.π (ChainToTypeCat T) I) l).prop
#check (ChainToTypeCat T)
#check I.val
#check (ChainToTypeCat T)
#check (ChainToTypeCat T).obj I

/-Construct `M[λ]` in the notation of our doc -/
variable {M} in
noncomputable def Submodule_of_chain {T : Set (DirectSumDecomposition M)}-- (hT : IsChainLE.le T)
  (l : limit (ChainToTypeCat T)) : PH.Submodule M := by
  let f : Subtype T → PH.Submodule M := fun (I : Subtype T) ↦ ((limit.π (ChainToTypeCat T) I) l).val
  let M_l : (PH.Submodule M) := ⨅ (I : Subtype T), f I
  exact M_l

notation3:max M"["l"]" => Submodule_of_chain l

/-`M` is the direct sum of all the `M[λ]` -/
variable {M} in
lemma M_is_dir_sum_lambdas {T : Set (DirectSumDecomposition M)} (hT : IsChain
  LE.le T) (c : C) :
  DirectSum.IsInternal (fun (l : limit (ChainToTypeCat T)) => ((Submodule_of_chain  l).mods c : Submodule K (M.obj c))) := by
  rw [DirectSum.isInternal_iff]
  constructor
  · intro m h_ker
    let Λ I := limit.π (ChainToTypeCat T) I
    obtain ⟨J, hJ⟩ : ∃ (J : T), Pairwise fun l₁ l₂ ↦ Λ J l₁ ≠ Λ J l₂ := by
      sorry
    have : DirectSum.IsInternal (fun (j : J.val.S) => j.val.mods c) := by
      sorry
    simp_rw [DirectSum.isInternal_iff, DirectSum.ext_iff K] at this
    --rw [DirectSum.isInternal_iff]
    apply DirectSum.ext (R := K)
    intro i
    simp only [map_zero] at this ⊢
    obtain ⟨x, hx⟩ := this.right <| m i--(limit.π (ChainToTypeCat T) J i).val.mods c
    obtain ⟨j, y, rfl⟩ : ∃ j y, x = DirectSum.of _ j y := by
      sorry
    --simp? [ZeroMemClass.coe_zero, implies_true, DirectSum.of, DFinsupp.singleAddHom] at hx
    --simp?
    aesop
    --rw [←this.left]
    sorry
  · sorry

-- /-`M` is the direct sum of all the `M[λ]` -/
-- variable {M} in
-- lemma M_is_dir_sum_lambdas {T : Set (DirectSumDecomposition M)} (hT : IsChain
--   LE.le T) (x : C) :
--   DirectSum.IsInternal (fun (l : limit (ChainToTypeCat T)) => ((Submodule_of_chain hT l).mods x : Submodule K (M.obj x))) := by
--   apply (DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top _).mpr
--   constructor
--   · intro a
--     sorry
--   · sorry


/- The `M[λ]` are linearly independent -/
variable {M} in
lemma lambdas_indep {T : Set (DirectSumDecomposition M)} (hT : IsChain
  LE.le T) : CompleteLattice.SetIndependent
  { M[l] | (l : limit (ChainToTypeCat T)) (_ : ¬ IsBot M[l])} := by
  intro a b ha hb hab
  sorry

variable {M} in
/-- The `M[λ]` span `M` -/
lemma sSup_lambdas_eq_top {T : Set (DirectSumDecomposition M)} (hT : IsChain
  LE.le T) : sSup {M[l] | (l : limit (ChainToTypeCat T)) (_ : ¬ IsBot M[l])} = ⊤ := by
  sorry



variable {M} in
/-- Get a direct sum out of a chain (this should be the index set 𝓤 in out doc)-/
def DirectSumDecomposition_of_chain {T : Set (DirectSumDecomposition M)} (hT : IsChain
  LE.le T) : DirectSumDecomposition M where
  S := {(Submodule_of_chain l) | (l : limit (ChainToTypeCat T)) (_ : ¬ IsBot (Submodule_of_chain hT l))}
  h_top := sSup_lambdas_eq_top hT
  h_indep := lambdas_indep hT
  bot_notin := sorry

/- The set `𝓤` is an upper bound for the chain `T` -/
lemma every_chain_has_an_upper_bound (N : PH.Submodule M)
    {T : Set (DirectSumDecomposition M)} (hT : IsChain LE.le T) :
    ∀ D ∈ T, D ≤ DirectSumDecomposition_of_chain hT := by
  intro D hD
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

-- For this to work we would need to change the definition of a DirectSumDecompositon
-- since at the moment it only work for `⊤`.
-- Alternatively, we could also construct the subfunctor that arises from a submodule
def TrivialDecomp (N : PH.Submodule M) : DirectSumDecomposition M where
  S := {N}
  h_indep := by sorry
  h_top := by sorry
  bot_notin := sorry

/--`M` is indecomposable iff its only non-trivial submodule is the zero submodule `⊥`-/
def Indecomposable : Prop := IsMax (TrivialDecomp M ⊤)

variable {M} in
/--This is the definition of indecomposability we should be using since it's more general
(works at a lattice theoretic level)-/
-- TODO: we don't need `a ≤ N` and `b ≤ N` in the implications
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
  have h (x : C) : DirectSum.IsInternal (fun p : S => (p.val.mods x : Submodule _ _)) := by sorry
  have h' : ⊤ = sSup S := by sorry
  let Cex : DirectSumDecomposition M := ⟨S, sorry, sorry, sorry⟩
  have contra : ¬ IsMax D := by sorry
  exact contra hmax

variable {M} in
/--
If `D` is a direct sum decomposition of `M` and for each `N` appearing in `S` we are given a direct
sum decomposition of `N`, we can construct a refinement of `D`.
-/
def RefinedDirectSumDecomposition
    {D : DirectSumDecomposition M}
    (B : ∀ (N : PH.Submodule M), N ∈ D.S → Set (PH.Submodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, CompleteLattice.SetIndependent (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) :
    DirectSumDecomposition M where
    S := ⋃ (N) (hN), B N hN
    h_indep := by
      intro x hx a ha ha'
      simp_rw [Set.mem_iUnion] at hx
      obtain ⟨N, hN, hN'⟩ := hx
      have lem₁ : a ≤ N := sorry
      have lem₂ : a ≤ sSup (D.S \ {N}) := sorry
      refine D.h_indep hN ?_ ?_
      · apply le_trans ha
        rw [hB N hN]
        apply le_sSup hN'
      · let S := a ⊓
        apply le_trans ha'
        calc sSup (⋃ (N) (hN), B N hN \ {x}) = ⨆ (N) (hN), sSup (B N hN \ {x}) := by sorry
          _ = (⨆ (M) (hM) (_ : M ≠ N), sSup (B M hM)) ⊔ sSup (B N hN \ {x}) := by sorry
          _ =
        --apply sSup_le_sSup

#exit
        --We need to show that the submodules appearing in the decomposition are independent
        --might be a little annoying
        sorry
    h_top := by
      simp_rw [sSup_iUnion]
      calc
        ⨆ i, ⨆ (i_1 : i ∈ D.S), sSup (B i i_1) = ⨆ (i) (i_1 : i ∈ D.S), i := by
          apply iSup_congr
          intro I
          by_cases hI : I ∈ D.S
          · simp only [hB I hI, instSupSetSubmodule, exists_prop]
          · simp only [hI, instSupSetSubmodule, exists_prop, not_false_eq_true, iSup_neg]
        _ = ⊤ := by rw [←D.h_top, sSup_eq_iSup]
    bot_notin := by
      intro h
      simp_rw [Set.mem_iUnion] at h
      obtain ⟨N, hN, hbot⟩ := h
      exact hB'' N hN hbot

lemma RefinedDirectSumDecomposition_le
    {D : DirectSumDecomposition M}
    (B : ∀ (N : PH.Submodule M), N ∈ D.S → Set (PH.Submodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, CompleteLattice.SetIndependent (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN) :
    (RefinedDirectSumDecomposition B hB hB' hB'') ≤ D := sorry

lemma RefinedDirectSumDecomposition_lt_of_exists_ne_singleton
    {D : DirectSumDecomposition M}
    (B : ∀ (N : PH.Submodule M), N ∈ D.S → Set (PH.Submodule M))
    (hB : ∀ N hN, N = sSup (B N hN))
    (hB' : ∀ N hN, CompleteLattice.SetIndependent (B N hN))
    (hB'' : ∀ N hN, ⊥ ∉ B N hN)
    (H : ∃ (N : PH.Submodule M) (hN : N ∈ D.S), B N hN ≠ {N}) :
    (RefinedDirectSumDecomposition B hB hB' hB'') < D := sorry

lemma Indecomposable'_of_mem_Min_Direct_sum_decomposition
  (D : DirectSumDecomposition M) (N : PH.Submodule M) (hN : N ∈ D.S) (hmax : IsMin D) : Indecomposable' N := by
  by_contra hNotMax
  rw [Indecomposable'] at hNotMax
  simp only [not_forall, Classical.not_imp, not_or, exists_and_left] at hNotMax
  obtain ⟨x, hx, y, hx', hy', hxy, hxy', hy⟩ := hNotMax
  set B : ∀ (N : PH.Submodule M), N ∈ D.S → Set (PH.Submodule M) :=
    fun (M : PH.Submodule M) (hM : M ∈ D.S) => if M = N then {x, y} else {M} with hB
  set newD : DirectSumDecomposition M := RefinedDirectSumDecomposition
    B sorry sorry sorry
  have contra : ¬ IsMin D := by
    simp only [not_isMin_iff]
    use newD
    apply RefinedDirectSumDecomposition_lt_of_exists_ne_singleton
    use N, hN
    simp only [hB, if_true]
    intro h
    --This should be easy
    sorry
  sorry

-- /-- If `N` is a submodule of `M` that is part of a minimal direct sum decomposition, then `N` is indecomposable -/
-- lemma Indecomposable'_of_mem_Min_Direct_sum_decomposition'
--   (D : DirectSumDecomposition M) (N : PH.Submodule M) (hN : N ∈ D.S) (hmax : IsMin D) : Indecomposable' N := by
--   by_contra hNotMax
--   rw [Indecomposable'] at hNotMax
--   simp only [not_forall, Classical.not_imp, not_or, exists_and_left] at hNotMax
--   obtain ⟨x, hx, y, hx', hy', hxy, hxy', hy⟩ := hNotMax
--   set newD : DirectSumDecomposition M := RefinedDirectSumDecomposition
--     (fun (M : PH.Submodule M) (hM : M ∈ D.S) => if M = N then {x, y} else {M}) sorry sorry sorry

--   set S : Set (PH.Submodule M) := (D.S \ {N}) ∪ {x, y} with hS
--   have h : ∀ (x : C), DirectSum.IsInternal (fun p : S => (p.val.mods x : Submodule _ _)) := by
--     intro x'
--     rw [DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top]
--     constructor
--     · --this is going to be a bit of a pain to prove
--       intro a b hab hb'
--       by_cases ha : a = x
--       · have : b ≤ N.mods x' := le_trans (ha ▸ hab) (hx' x')
--         --this should now follow from the independence of the direct sum decomposition `D`
--         --have := calc b ≤ (⨆ j, ⨆ (_ : j ≠ a), (fun (p : S) ↦ p.val.mods x') j) := by sorry
--         --_ ≤ (⨆ j, ⨆ (_ : j ≠ a), (fun (p : D.S) ↦ p.val.mods x') j)
--         sorry
--       · by_cases hb : a = y
--         · have : b ≤ N.mods x' := le_trans (hb ▸ hab) (hy' x')
--           --this should now follow from the independence of the direct sum decomposition `D`
--           sorry
--           --Since the sum is over j ≠ a, it will include `x ⊔ y = N` so we can rewrite it in a nicer way
--         · have : (⨆ j, ⨆ (_ : j ≠ a), (fun (p : S) ↦ p.val.mods x') j) =
--             ⨆ j, ⨆ (_ : j.val ≠ a.val), (fun (p : D.S) => p.val.mods x') j := by
--             sorry
--           --this should now follow from the independence of the direct sum decomposition `D`
--           rw [this] at hb'
--           sorry
--       --The direct sum is indexed over all `j` in `S` so we can rewrite it in a nicer way by using `x ⊔ y = N`.
--     · calc (⨆ (p : S), p.val.mods x') = (⨆ (p : D.S), p.val.mods x') := by sorry
--       _ = ⊤ := ((DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top _).mp <| D.h x').right
--   let Cex : DirectSumDecomposition M := ⟨S, h, sorry⟩
--   have contra : ¬ IsMin D := by
--     simp only [not_isMin_iff]
--     use Cex
--     apply lt_of_le_of_ne
--     --this is very golfable
--     · set d : D.S → Set (PH.Submodule M) := fun (I : D.S) ↦ if I.val = N then {x, y} else {I.val} with hd
--       use d, fun I => ?_, fun I => ?_
--       · by_cases hI : I.val = N
--         · simp only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton, ← hxy']
--         · simp only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton]
--       · by_cases hI : I.val = N
--         · simpa only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton, hS] using Set.subset_union_right
--         · simp only [hd, hI, ↓reduceIte, sSup_insert, csSup_singleton, Set.singleton_subset_iff]
--           apply Set.mem_union_left _ (Set.mem_diff_of_mem I.prop _)
--           rw [Set.mem_singleton_iff]
--           exact hI
--     · --this can probably be golfed with the right API
--       intro h
--       have : D.S ≠ Cex.S := by
--         simp only [ne_eq]
--         intro h'
--         have: N ∉ S := by
--           intro h''
--           rw [hS, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_diff, Set.mem_singleton_iff] at h''
--           simp only [not_true_eq_false, and_false, false_or] at h''
--           rcases h'' with h'' | h''
--           · rw [←h'', inf_eq_right.mpr hy'] at hxy
--             exact hy hxy
--           · rw [←h'', inf_eq_left.mpr hx'] at hxy
--             exact hx hxy
--         rw [h'] at hN
--         exact this hN
--       exact this (congrArg DirectSumDecomposition.S h.symm)
--   exact contra hmax

end Indecomposable

section

/- TODO in this section: construct the persistence module associated to a submodule,
and show that submodules that are atoms yield indecomposable persistence modules-/

end
