module

public import Mathlib.Order.SupIndep

public section

open CompleteLattice

variable {ι κ α : Type*} [CompleteLattice α] {f : ι → κ → α}

lemma Pi.iSupIndep_iff : iSupIndep f ↔ ∀ k, iSupIndep (f · k) := by
  simpa [iSupIndep, Pi.disjoint_iff] using forall_comm

/-- If every `a ∈ S` is the supremum of a family `B a ha`, then the supremum of the
union of those families is the supremum of `S`. -/
lemma sSup_iUnion₂_eq_sSup {α : Type*} [CompleteLattice α] {S : Set α}
    {B : ∀ a, a ∈ S → Set α} (hB : ∀ a ha, a = sSup (B a ha)) :
    sSup (⋃ a, ⋃ ha, B a ha) = sSup S := by
  apply le_antisymm
  · apply sSup_le
    intro x hx
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨a, ha, hx⟩
    exact le_sSup_of_le ha (by rw [hB a ha]; exact le_sSup hx)
  · apply sSup_le
    intro a ha
    rw [hB a ha]
    apply sSup_le
    intro x hx
    apply le_sSup
    simp only [Set.mem_iUnion]
    exact ⟨a, ha, hx⟩

/-- If `⊥` is in none of the dependent families `B a ha`, then it is not in their union. -/
lemma bot_notMem_iUnion₂ {α : Type*} [CompleteLattice α] {S : Set α}
    {B : ∀ a, a ∈ S → Set α} (hbot : ∀ a ha, ⊥ ∉ B a ha) :
    ⊥ ∉ ⋃ a, ⋃ ha, B a ha := by
  intro h
  simp only [Set.mem_iUnion] at h
  rcases h with ⟨a, ha, hmem⟩
  exact hbot a ha hmem

/-- In a supremum-independent set, if a nonzero element `N = sSup B` lies below a
member `A` of the independent set and `B` is a subset of that independent set, then
`A ∈ B`. -/
lemma sSupIndep.mem_of_sSup_eq_of_le_of_ne_bot {α : Type*} [CompleteLattice α]
    {S B : Set α} {N A : α} (hS : sSupIndep S) (hB : B ⊆ S)
    (hN : N = sSup B) (hNA : N ≤ A) (hA : A ∈ S) (hN_ne : N ≠ ⊥) :
    A ∈ B := by
  by_contra hA_not_mem
  have h_disj : Disjoint A (sSup B) := hS.disjoint_sSup hA hB hA_not_mem
  have h_le : sSup B ≤ A := hN ▸ hNA
  have h_bot : sSup B = ⊥ := by
    rw [disjoint_comm] at h_disj
    exact Disjoint.eq_bot_of_le h_disj h_le
  exact hN_ne (by rw [hN, h_bot])

/-- Two members of a supremum-independent set with a common nonzero lower bound are equal. -/
lemma sSupIndep.eq_of_le_of_le {α : Type*} [CompleteLattice α] {S : Set α}
    {x a b : α} (hS : sSupIndep S) (hx : x ≠ ⊥) (ha : a ∈ S) (hb : b ∈ S)
    (hxa : x ≤ a) (hxb : x ≤ b) : a = b := by
  by_contra hne
  have h_disj : Disjoint a b :=
    (sSupIndep_pair hne).mp <| sSupIndep.mono hS <| by
      intro y hy
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
  exact hx <| le_bot_iff.mp <| (le_inf hxa hxb).trans (disjoint_iff_inf_le.mp h_disj)

/-- Replacing each element of a supremum-independent set by a supremum-independent family
with the same supremum preserves supremum-independence, in a modular complete lattice. -/
lemma sSupIndep.iUnion₂ {α : Type*} [CompleteLattice α] [IsModularLattice α]
    {S : Set α} {B : ∀ a, a ∈ S → Set α} (hS : sSupIndep S)
    (hB : ∀ a ha, a = sSup (B a ha)) (hBi : ∀ a ha, sSupIndep (B a ha)) :
    sSupIndep (⋃ a, ⋃ ha, B a ha) := by
  intro x hx a ha ha'
  simp only [Set.mem_iUnion] at hx
  rcases hx with ⟨N, hN, hxN⟩
  have hx_le_N : x ≤ N := by
    rw [hB N hN]
    exact le_sSup hxN
  have hsplit :
      sSup ((⋃ N, ⋃ (hN : N ∈ S), B N hN) \ {x}) ≤
        sSup (B N hN \ {x}) ⊔ sSup (S \ {N}) := by
    apply sSup_le
    intro y hy
    rcases hy with ⟨hyU, hyne⟩
    simp only [Set.mem_iUnion] at hyU
    rcases hyU with ⟨N', hN', hyB⟩
    by_cases hNN : N' = N
    · subst N'
      exact le_trans (le_sSup (show y ∈ B N hN \ {x} from ⟨hyB, hyne⟩)) le_sup_left
    · have hy_le_N' : y ≤ N' := by
        rw [hB N' hN']
        exact le_sSup hyB
      have hN'_other : N' ∈ S \ {N} :=
        ⟨hN', by simpa [Set.mem_singleton_iff] using hNN⟩
      exact le_trans hy_le_N' (le_trans (le_sSup hN'_other) le_sup_right)
  have hS_disj : Disjoint N (sSup (S \ {N})) := hS hN
  have ha_disj_other : Disjoint a (sSup (S \ {N})) :=
    hS_disj.mono_left (ha.trans hx_le_N)
  have ha_same : a ≤ sSup (B N hN \ {x}) := by
    have same_le_N : sSup (B N hN \ {x}) ≤ N :=
      (sSup_le_sSup (fun _ h => h.1)).trans (le_of_eq (hB N hN).symm)
    have ha_le_N : a ≤ N := ha.trans hx_le_N
    refine (le_of_eq (inf_eq_left.2 ha_le_N).symm).trans ?_
    refine (inf_le_inf_right N (ha'.trans hsplit)).trans ?_
    refine (le_of_eq <| @sup_inf_assoc_of_le α _ _
      (sSup (B N hN \ {x})) (sSup (S \ {N})) N same_le_N).trans ?_
    simpa using sup_le_sup_left hS_disj.symm.le_bot (sSup (B N hN \ {x}))
  exact (hBi N hN hxN) ha ha_same
