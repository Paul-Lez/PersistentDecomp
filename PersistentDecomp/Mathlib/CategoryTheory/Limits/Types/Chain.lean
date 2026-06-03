module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import PersistentDecomp.Mathlib.Order.Chain

/-!
# Limits over chains in `Type`

This file collects small facts about projections from limits of Type-valued functors indexed by a
nonempty chain.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.Types

variable {α : Type*} [Preorder α] {T : Set α} (F : T ⥤ Type)
variable [HasLimit F]

/-- Two different elements of a Type-valued limit differ after some projection. -/
lemma exists_limitProj_ne_of_ne {x y : limit F} (h : x ≠ y) :
    ∃ I : T, limit.π F I x ≠ limit.π F I y := by
  by_contra hnone
  exact h <| Types.limit_ext F x y fun I => by
    by_contra hne
    exact hnone ⟨I, hne⟩

/-- If two limit elements differ after a later projection, they differ after any earlier
projection. -/
lemma limitProj_ne_of_le {J I : T} (hJI : J ≤ I) {x y : limit F}
    (hne : limit.π F I x ≠ limit.π F I y) :
    limit.π F J x ≠ limit.π F J y := by
  intro h
  apply hne
  have hmapx := limit.w_apply F (homOfLE hJI) x
  have hmapy := limit.w_apply F (homOfLE hJI) y
  change limit.π F I x = limit.π F I y
  change limit.π F J x = limit.π F J y at h
  rw [← hmapx, ← hmapy, h]

/-- On any finite set of elements in a Type-valued limit over a nonempty chain, some projection is
injective. -/
lemma exists_limitProj_injOn_finset (hT : IsChain LE.le T) (hTne : T.Nonempty)
    (s : Finset (limit F)) : ∃ J : T, (s : Set (limit F)).InjOn (limit.π F J) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rcases hTne with ⟨J, hJ⟩
      refine ⟨⟨J, hJ⟩, ?_⟩
      simp [Set.InjOn]
  | insert l s hls ih =>
      rcases ih with ⟨J₀, hJ₀⟩
      have hsep_exists :
          ∃ J : T, J ≤ J₀ ∧ ∀ x ∈ s, limit.π F J x ≠ limit.π F J l := by
        induction s using Finset.induction with
        | empty =>
            exact ⟨J₀, le_rfl, by simp⟩
        | insert x s hxs ihs =>
            have hxl : x ≠ l := by
              intro hxl
              exact hls (hxl ▸ Finset.mem_insert_self x s)
            have hls' : l ∉ s := by
              intro hl
              exact hls (Finset.mem_insert_of_mem hl)
            have hJ₀' : Set.InjOn (limit.π F J₀) (s : Set (limit F)) :=
              hJ₀.mono (by
                intro y hy
                exact Finset.mem_insert_of_mem hy)
            rcases ihs hls' hJ₀' with ⟨J₁, hJ₁J₀, hsep₁⟩
            rcases exists_limitProj_ne_of_ne F hxl with ⟨I, hI⟩
            rcases exists_finset_lower_bound hT hTne ({J₁, I} : Finset T) with ⟨J, hJ⟩
            have hJJ₁ : J ≤ J₁ := hJ J₁ (by simp)
            have hJI : J ≤ I := hJ I (by simp)
            refine ⟨J, hJJ₁.trans hJ₁J₀, ?_⟩
            intro y hy
            rw [Finset.mem_insert] at hy
            rcases hy with rfl | hy
            · exact limitProj_ne_of_le F hJI hI
            · exact limitProj_ne_of_le F hJJ₁ (hsep₁ y hy)
      rcases hsep_exists with ⟨J, hJJ₀, hsep⟩
      refine ⟨J, ?_⟩
      intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · rfl
        · exact False.elim ((hsep y hy) hxy.symm)
      · rcases hy with rfl | hy
        · exact False.elim ((hsep x hx) hxy)
        · apply hJ₀ hx hy
          have hmapx := limit.w_apply F (homOfLE hJJ₀) x
          have hmapy := limit.w_apply F (homOfLE hJJ₀) y
          change limit.π F J₀ x = limit.π F J₀ y
          change limit.π F J x = limit.π F J y at hxy
          rw [← hmapx, ← hmapy, hxy]

end CategoryTheory.Limits.Types
