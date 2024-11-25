import Mathlib.Data.DFinsupp.BigOperators

@[to_additive (attr := simp)]
lemma SubmonoidClass.coe_dfinsuppProd {B ι N : Type*} {M : ι → Type*} [DecidableEq ι]
    [∀ i, Zero (M i)] [∀ i (x : M i), Decidable (x ≠ 0)] [CommMonoid N] [SetLike B N]
    [SubmonoidClass B N] {S : B} (f : Π₀ i, M i) (g : ∀ i, M i → S) :
    (↑(f.prod g) : N) = f.prod fun i x ↦ (g i x : N) :=
  map_dfinsupp_prod (SubmonoidClass.subtype S) ..
