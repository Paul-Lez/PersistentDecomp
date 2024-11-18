import Mathlib.CategoryTheory.Limits.Types
import PersistentDecomp.DirectSumDecompositionDual
import PersistentDecomp.Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Limits.Types

open CategoryTheory Classical CategoryTheory.Limits DirectSum DirectSumDecomposition

variable {C : Type} [Category.{0, 0} C] {K : Type} [DivisionRing K] {M : C ⥤ ModuleCat K}

/- In this file we sketch what we'll need to prove to
get Step 2 done. Most of the work is setting the stage so
we can apply Zorn's lemma.-/

/- For now we work with types in the 0-th universe. To make the code universe polymorphic we'll need to
make a few edits below-/

section Chains

/- In this section we set up what's needed to take an inverse limit of direct sum
decompositions. Since these are defined in terms of sets, we could construct the
inverse limit explicitly but I think this would be really painful and messy...-/

/-- Here we write some code to go from chains in directSumDecompositions to diagrams in the category of types-/
noncomputable def ToTypeCat : DirectSumDecomposition M ⥤ Type  where
  obj D := D
  -- Define the maps f_{IJ} induced by "J refines I"
  map {J I} f := by
    simp
    exact (RefinementMap I J (leOfHom f))
  map_id {I} := by
    aesop
  map_comp {I J L} f g := by
    have h₁ := leOfHom f
    have h₂ := leOfHom g
    ext N : 2
    simp
    exact RefinmentMapFunctorial .. --THANK YOU FOR .. YAEL!!

/-- This is possibly useful to make things a bit cleaner so let's keep it for now but possibly
remove it later -/
noncomputable def Pone (T : Set (DirectSumDecomposition M)) : T ⥤ Type where
  obj D := ToTypeCat.obj D.val
  map {J I} f := ToTypeCat.map f
  map_id I := by rw [← ToTypeCat.map_id]; rfl
  map_comp {I J K} f g := by rw [← ToTypeCat.map_comp]; rfl


variable (N : PersistenceSubmodule M) {T : Set (DirectSumDecomposition M)}

local notation "L" T:arg => limit (Pone T)

noncomputable abbrev Λ (I : T) := limit.π (Pone T) I

variable (l : L T) (I : T) (D : DirectSumDecomposition M)

/-- Construct `M[λ]` in the notation of our doc -/
noncomputable def chainBound (l : L T) : PersistenceSubmodule M := ⨅ I, (Λ I l).val

notation3:max "M["l"]" => chainBound l
notation3:max "M["l"]_[" c "]" => chainBound l c

lemma chainBound_le : M[l] ≤ (Λ I l).val := iInf_le ..


noncomputable def limit_elt_mk (hT : IsChain LE.le T) (f : T → PersistenceSubmodule M)
  (h_le : ∀ (I J : T), I ≤ J → f J ≤ f I) (h_mem : ∀ I : T, (f I) ∈ I.val) : (L T) := by
  let f' : (I : T) → (Pone T).obj I := by
    intro I
    simp[Pone, ToTypeCat]
    exact ⟨(f I), h_mem I⟩
  have h_compatible : (∀ (j j' : ↑T) (f : j ⟶ j'), (Pone T).map f (f' j) = f' j') := by
    intro I J g
    have h_ij := leOfHom g
    sorry
  let l := CategoryTheory.Limits.Types.Limit.mk (Pone T) f' h_compatible
  exact l


/-- `M` is the direct sum of all the `M[λ]`. -/
lemma isInternal_chainBound (hT : IsChain LE.le T) (c : C) : IsInternal fun l : L T ↦ M[l]_[c] := by
  rw [isInternal_iff]
  constructor
  · intro m hm
    obtain ⟨J, hJ⟩ : ∃ J : T, (m.support : Set (L T)).InjOn (Λ J) := by
      sorry
    have : IsInternal fun j : J.val ↦ j.val c := J.1.isInternal _
    refine DFinsupp.ext fun l ↦ ?_
    ext : 1
    by_cases hl : l ∈ m.support
    · exact this.eq_zero_of_subsingleton_preimage (Λ J) (fun l ↦ m l) m.support hJ
        (fun l ↦ chainBound_le _ _ _ (m l).2) hm hl
    · simpa using hl
  · sorry

/-- The `M[λ]` are linearly independent -/
lemma lambdas_indep (hT : IsChain LE.le T) :
    CompleteLattice.SetIndependent {M[l] | (l : L T) (_ : ¬ IsBot M[l])} := by
  intro a b ha hb hab
  sorry

/-- The `M[λ]` span `M` -/
lemma sSup_lambdas_eq_top (hT : IsChain LE.le T) :
    sSup {M[l] | (l : L T) (_ : ¬ IsBot M[l])} = ⊤ := by
  sorry

/-- Get a direct sum out of a chain (this should be the index set 𝓤 in out doc)-/
def DirectSumDecomposition_of_chain (hT : IsChain LE.le T) : DirectSumDecomposition M where
  carrier := {M[l] | (l : L T) (_ : ¬ IsBot M[l])}
  sSup_eq_top' := sSup_lambdas_eq_top hT
  setIndependent' := lambdas_indep hT
  not_bot_mem' := sorry

/-- The set `𝓤` is an upper bound for the chain `T` -/
lemma every_chain_has_an_upper_bound (N : PersistenceSubmodule M) (hT : IsChain LE.le T) :
    ∀ D ∈ T, D ≤ DirectSumDecomposition_of_chain hT := by
  intro D hD
  sorry

/--Every chain has an upper bound, hence there is a maximal direct sum decomposition `D`-/
lemma zorny_lemma (N : PersistenceSubmodule M) : ∃ (D : DirectSumDecomposition M), IsMax D := by
  apply zorn_le
  rintro T hT
  rw [bddAbove_def]
  use (DirectSumDecomposition_of_chain hT)
  exact (every_chain_has_an_upper_bound N hT)

end Chains

section

/- TODO in this section: construct the persistence module associated to a submodule,
and show that submodules that are atoms yield indecomposable persistence modules-/

end
