module

public import Mathlib.Order.Interval.Basic
public import Mathlib.Order.Interval.Set.OrdConnected

public section

open Set

variable {α : Type*} [Preorder α]

namespace NonemptyInterval

lemma ordConnected (I : NonemptyInterval α) : (I : Set α).OrdConnected where
  out' _x hx _z hz := Icc_subset_Icc hx.1 hz.2

end NonemptyInterval

namespace Interval
variable {α : Type*} [PartialOrder α]

lemma ordConnected : ∀ I : Interval α, (I : Set α).OrdConnected
  | none => ordConnected_empty
  | some I => I.ordConnected

end Interval
