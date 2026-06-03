module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import PersistentDecomp.DirectSumDecomposition.Fiber
public import PersistentDecomp.EndRingIsLocal
public import PersistentDecomp.Mathlib.CategoryTheory.Limits.Types.Chain
public import PersistentDecomp.Mathlib.Data.Nat.Finite
public import PersistentDecomp.Mathlib.Order.Chain
public import PersistentDecomp.Mathlib.Order.Partition.Limit
public import PersistentDecomp.Mathlib.Order.Zorn

/-!
This file constructs a maximal direct-sum decomposition of a pointwise finite persistence module
and proves that its summands have local endomorphism rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum
open DirectSumDecomposition

variable {C : Type} [Category.{0, 0} C] {K : Type} [DivisionRing K] {M : C ⥤ ModuleCat K}

section Chains

variable (N : PersistenceSubmodule M) {T : Set (DirectSumDecomposition M)}

local notation "L" T:arg => limit (Partition.toTypeCatOn T)

variable (l : L T) (I : T) (D : DirectSumDecomposition M)

/-- Construct `M[λ]` in the notation of our doc -/
noncomputable def chainBound (l : L T) : PersistenceSubmodule M :=
  ⨅ I, (limit.π (Partition.toTypeCatOn T) I l).val

notation3:max "M["l"]" => chainBound l
notation3:max "M["l"]_[" c "]" => chainBound l c

open scoped Classical in
/-- A limit element obtained by tracking the unique summand containing a fixed vector. -/
@[nolint unusedArguments]
noncomputable def limitOfContainingSummands (_hT : IsChain LE.le T) {c : C} {x : M.obj c}
    (hcontains : ∀ I : T, ∃! q : I.val, x ∈ q.val c) : L T :=
  Partition.limitMkOfUnique (fun (I : T) (q : I.val) => x ∈ q.val c) hcontains
    (fun {I J} hIJ q hq => (refinementMap_le J.val I.val hIJ q c) hq)

/-- The tracked vector lies in the chain-bound submodule of its limit element. -/
lemma mem_chainBound_limitOfContainingSummands (hT : IsChain LE.le T) {c : C} {x : M.obj c}
    (hcontains : ∀ I : T, ∃! q : I.val, x ∈ q.val c) :
    x ∈ M[limitOfContainingSummands hT hcontains]_[c] := by
  simp only [chainBound, PersistenceSubmodule.iInf_apply, Submodule.mem_iInf]
  intro I
  let contains : (I : T) → I.val → Prop := fun I q => x ∈ q.val c
  let hmap : ∀ {I J : T} (hIJ : I ≤ J) (q : I.val),
      contains I q → contains J (refinementMap J.val I.val hIJ q) :=
    fun {I J} hIJ q hq => (refinementMap_le J.val I.val hIJ q c) hq
  change x ∈ (limit.π (Partition.toTypeCatOn T) I
    (Partition.limitMkOfUnique contains hcontains hmap)).val c
  exact Partition.limitMkOfUnique_spec contains hcontains hmap I

variable [∀ c : C, Module.Finite K (M.obj c)]

open scoped Classical in
lemma exists_max_fiberDecomp_support_card (hTne : T.Nonempty) (c : C)
    [DecidableEq (M.obj c)] (b : M.obj c) :
    ∃ J : T, ∀ I : T, (fiberDecomp I.val c b).support.card ≤
      (fiberDecomp J.val c b).support.card := by
  classical
  rcases hTne with ⟨J₀, hJ₀⟩
  exact exists_max_nat_of_bdd (ι := T) ⟨⟨J₀, hJ₀⟩⟩
    (fun I : T => (fiberDecomp I.val c b).support.card)
    (fun I => fiberDecomp_support_card_le_finrank I.val c b)

open scoped Classical in
lemma exists_max_fiberDecomp_support_summand_contains_unique (hT : IsChain LE.le T)
    (hTne : T.Nonempty) (c : C) [DecidableEq (M.obj c)] (b : M.obj c) :
    ∃ J : T, ∀ p : {p : J.val // p ∈ (fiberDecomp J.val c b).support},
      ∀ I : T, ∃! q : I.val, ((fiberDecomp J.val c b) p.val : M.obj c) ∈ q.val c := by
  classical
  obtain ⟨J, hJmax⟩ := exists_max_fiberDecomp_support_card (T := T) hTne c b
  refine ⟨J, ?_⟩
  intro p I
  by_cases hIJ_eq : I = J
  · subst I
    exact existsUnique_summand_contains_fiberDecomp J.val c b p.prop
  · have hvalne : I.val ≠ J.val := fun h ↦ hIJ_eq (Subtype.ext h)
    rcases hT I.prop J.prop hvalne with hIJ | hJI
    · exact existsUnique_summand_contains_fiberDecomp_of_refinement_of_card_le
        I.val J.val hIJ c b (hJmax I) p.prop
    · exact existsUnique_summand_contains_fiberDecomp_of_refinement I.val J.val hJI c b p.prop

/-- The remaining algebraic content in the chain construction: every vector should have a finite
direct-sum expansion by the limit summands. -/
lemma chainBound_surjective (hT : IsChain LE.le T) (hTne : T.Nonempty)
    [DecidableEq (L T)] (c : C) [DecidableEq (M.obj c)] :
    ∀ b : M.obj c, ∃ a : ⨁ l : L T, M[l]_[c],
      (DFinsupp.sum a fun _i x ↦ (x : M.obj c)) = b := by
  classical
  intro b
  obtain ⟨J, hcontains⟩ :=
    exists_max_fiberDecomp_support_summand_contains_unique (T := T) hT hTne c b
  let mkLimit (p : {p : J.val // p ∈ (fiberDecomp J.val c b).support}) : L T :=
    limitOfContainingSummands hT (fun I ↦ hcontains p I)
  have hxchain (p : {p : J.val // p ∈ (fiberDecomp J.val c b).support}) :
      ((fiberDecomp J.val c b) p.val : M.obj c) ∈ M[mkLimit p]_[c] := by
    simpa [mkLimit] using
      mem_chainBound_limitOfContainingSummands (hT := hT) (fun I ↦ hcontains p I)
  let candidate : ⨁ l : L T, M[l]_[c] :=
    ∑ p : {p : J.val // p ∈ (fiberDecomp J.val c b).support},
      DirectSum.of (fun l : L T => M[l]_[c]) (mkLimit p)
        ⟨((fiberDecomp J.val c b) p.val : M.obj c), hxchain p⟩
  refine ⟨candidate, ?_⟩
  calc
    DFinsupp.sum candidate (fun _i x ↦ (x : M.obj c))
        = DirectSum.coeLinearMap (fun l : L T => M[l]_[c]) candidate :=
          (DirectSum.coeLinearMap_eq_dfinsuppSum (R := K) (ι := L T) (M := M.obj c)
            (A := fun l : L T => M[l]_[c]) (x := candidate)).symm
    _ = b := by
      simp only [candidate, map_sum, DirectSum.coeLinearMap_of]
      have hsupport_sum :
          (∑ p : {p : J.val // p ∈ (fiberDecomp J.val c b).support},
            ((fiberDecomp J.val c b) p.val : M.obj c)) = b :=
        (Finset.sum_attach (fiberDecomp J.val c b).support
          (fun p : J.val => ((fiberDecomp J.val c b) p : M.obj c))).trans
          (by simpa [DFinsupp.sum] using fiberDecomp_sum J.val c b)
      exact hsupport_sum

open scoped Classical in
/-- `M` is the direct sum of all the `M[λ]`. -/
lemma chainBound_isInternal (hT : IsChain LE.le T) (c : C) :
    IsInternal fun l : L T ↦ M[l]_[c] := by
  classical
  by_cases hTne : T.Nonempty
  · rw [isInternal_iff]
    refine ⟨?_, ?_⟩
    · intro m hm
      obtain ⟨J, hJ⟩ :=
        Types.exists_limitProj_injOn_finset (Partition.toTypeCatOn T) hT hTne m.support
      have : IsInternal fun j : J.val ↦ j.val c :=
        DirectSumDecomposition.isInternal J.val c
      refine DFinsupp.ext fun l ↦ ?_
      ext : 1
      by_cases hl : l ∈ m.support
      · exact this.eq_zero_of_subsingleton_preimage (limit.π (Partition.toTypeCatOn T) J)
          (fun l ↦ m l) m.support hJ
          (fun l ↦
            (iInf_le (fun I : T => (limit.π (Partition.toTypeCatOn T) I l).val) J)
              c (m l).2)
          hm hl
      · simpa using hl
    · exact chainBound_surjective hT hTne c
  · have : IsEmpty T := ⟨fun I ↦ hTne ⟨I, I.prop⟩⟩
    have hsub : Subsingleton (L T) :=
      ⟨fun x y => Types.limit_ext (Partition.toTypeCatOn T) x y fun I => isEmptyElim I⟩
    let : DecidableEq (L T) := Classical.decEq (L T)
    have htop (l : L T) : M[l]_[c] = ⊤ := by
      simp [chainBound]
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · rw [iSupIndep_def]
      intro l
      rw [disjoint_iff_inf_le]
      have hnone : (⨆ j, ⨆ (_ : j ≠ l), M[j]_[c]) = ⊥ := by
        refine le_antisymm ?_ bot_le
        exact iSup_le fun j => iSup_le fun hj => False.elim (hj (hsub.elim j l))
      simp [hnone]
    · refine le_antisymm le_top ?_
      let f' : (I : T) → (Partition.toTypeCatOn T).obj I := fun I ↦ isEmptyElim I
      let l₀ : L T := CategoryTheory.Limits.Types.Limit.mk (Partition.toTypeCatOn T) f'
        (by intro I; exact isEmptyElim I)
      calc
        ⊤ = M[l₀]_[c] := (htop l₀).symm
        _ ≤ ⨆ l : L T, M[l]_[c] := le_iSup (fun l : L T ↦ M[l]_[c]) l₀

/-- The `M[λ]` are linearly independent -/
lemma chainBound_sSupIndep (hT : IsChain LE.le T) :
    sSupIndep {M[l] | (l : L T) (_ : ¬ IsBot M[l])} := by
  classical
  have h_indep : iSupIndep fun l : L T ↦ M[l] := by
    rw [iSupIndep_def]
    intro l
    rw [disjoint_iff_inf_le]
    intro c
    have hc_ind : iSupIndep fun l : L T ↦ M[l] c :=
      (chainBound_isInternal hT c).submodule_iSupIndep
    rw [iSupIndep_def] at hc_ind
    simpa [disjoint_iff_inf_le, PersistenceSubmodule.inf_apply,
      PersistenceSubmodule.iSup_apply] using hc_ind l
  exact h_indep.sSupIndep_range.mono (by
    rintro x ⟨l, _hl, rfl⟩
    exact ⟨l, rfl⟩)

/-- The `M[λ]` span `M` -/
lemma sSup_chainBound_eq_top (hT : IsChain LE.le T) :
    sSup {M[l] | (l : L T) (_ : ¬ IsBot M[l])} = ⊤ := by
  classical
  have htop : (⨆ l : L T, M[l]) = ⊤ := by
    ext c x
    simp [PersistenceSubmodule.iSup_apply, (chainBound_isInternal hT c).submodule_iSup_eq_top]
  refine le_antisymm le_top ?_
  exact htop.symm.le.trans <| iSup_le fun l => by
    by_cases hl : IsBot M[l]
    · rw [hl.eq_bot]
      exact bot_le
    · exact le_sSup ⟨l, hl, rfl⟩

/-- The direct-sum decomposition obtained as a lower bound of a chain of decompositions. -/
def directSumDecompositionOfChain (hT : IsChain LE.le T) : DirectSumDecomposition M where
  parts := {M[l] | (l : L T) (_ : ¬ IsBot M[l])}
  sSupIndep' := chainBound_sSupIndep hT
  bot_notMem' := by
    rintro ⟨l, hnot, h_eq⟩
    exact hnot (h_eq ▸ isBot_bot)
  sSup_eq' := sSup_chainBound_eq_top hT

/-- The set `𝓤` is a lower bound for the chain `T` in the `Partition` order. -/
lemma directSumDecompositionOfChain_le (hT : IsChain LE.le T) :
    ∀ D ∈ T, directSumDecompositionOfChain hT ≤ D := by
  intro D hD x hx
  change x ∈ {M[l] | (l : L T) (_ : ¬ IsBot M[l])} at hx
  rcases hx with ⟨l, _hl, rfl⟩
  let q := limit.π (Partition.toTypeCatOn T) ⟨D, hD⟩ l
  refine ⟨q.val, q.prop, ?_⟩
  exact iInf_le (fun I : T => (limit.π (Partition.toTypeCatOn T) I l).val) ⟨D, hD⟩

/-- Every chain has a lower bound, hence there is a minimal `Partition` direct sum decomposition. -/
lemma exists_isMin_directSumDecomposition (_N : PersistenceSubmodule M) :
    ∃ (D : DirectSumDecomposition M), IsMin D :=
  zorn_le_of_bddBelow_chains fun _ hT =>
    ⟨directSumDecompositionOfChain hT, directSumDecompositionOfChain_le hT⟩

/-- Every chain has an upper bound in the max-order convention, hence there is a maximal
direct sum decomposition. -/
lemma exists_isMax_directSumDecomposition (N : PersistenceSubmodule M) :
    ∃ (D : MaxOrder.DirectSumDecomposition M), IsMax D := by
  rcases exists_isMin_directSumDecomposition (M := M) N with ⟨D, hD⟩
  exact ⟨MaxOrder.DirectSumDecomposition.ofPartition D, hD.toDual⟩

/-- The decomposition part of Botnan--Crawley-Boevey Theorem 1.1: a pointwise finite persistence
module has a direct-sum decomposition into indecomposable persistence submodules. -/
theorem exists_indecomposable_directSumDecomposition :
    ∃ D : MaxOrder.DirectSumDecomposition M,
      ∀ N : PersistenceSubmodule M, N ∈ D → Indecomposable N := by
  rcases exists_isMax_directSumDecomposition (M := M) (⊤ : PersistenceSubmodule M) with
    ⟨D, hD⟩
  exact ⟨D, fun N hN =>
    MaxOrder.DirectSumDecomposition.indecomposable_of_mem_of_isMax D N hN hD⟩

/-- Botnan--Crawley-Boevey Theorem 1.1, stated using the direct-sum decomposition API. -/
theorem exists_indecomposable_directSumDecomposition_isLocalRing :
    ∃ D : MaxOrder.DirectSumDecomposition M,
      (∀ N : PersistenceSubmodule M, N ∈ D → Indecomposable N) ∧
        ∀ N : PersistenceSubmodule M, N ∈ D →
          IsLocalRing (End N.toFunctor) := by
  rcases exists_indecomposable_directSumDecomposition (M := M) with ⟨D, hD⟩
  refine ⟨D, hD, ?_⟩
  intro N hN
  have : ∀ c : C, Module.Finite K (N.toFunctor.obj c) := fun c => by
    change Module.Finite K (N c)
    infer_instance
  have hN_ne_bot : N ≠ ⊥ := fun hbot =>
    MaxOrder.DirectSumDecomposition.bot_notMem D (hbot ▸ hN)
  rcases PersistenceSubmodule.exists_nontrivial_toFunctor_obj_of_ne_bot N hN_ne_bot with
    ⟨X, hX⟩
  have : Nontrivial (N.toFunctor.obj X) := hX
  exact endRing_isLocalRing_of_isIndecomposableFunctor C K N.toFunctor X
    (PersistenceSubmodule.isIndecomposable_toFunctor_of_indecomposable N (hD N hN))

end Chains
