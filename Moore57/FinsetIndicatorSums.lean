import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Finset indicator-sum helpers

Small generic lemmas for converting constant-valued indicator sums into cardinals
of filtered finite sets.
-/

namespace Moore57

open Finset

/-- A constant-valued indicator sum over a finset is the constant times the
cardinality of the filtered finset. -/
theorem Finset.sum_ite_const_nat_eq_mul_card_filter {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → Prop) [DecidablePred p] (c : ℕ) :
    (∑ i ∈ s, if p i then c else 0) = c * (s.filter p).card := by
  classical
  rw [← Finset.sum_filter]
  rw [show (∑ i ∈ s.filter p, c) = (s.filter p).card * c by
    exact Finset.sum_const_nat
      (s := s.filter p)
      (m := c)
      (f := fun _i : ι => c)
      (by intro _i _hi; rfl)]
  rw [Nat.mul_comm]

/-- The `univ` form of `Finset.sum_ite_const_nat_eq_mul_card_filter`. -/
theorem Fintype.sum_ite_const_nat_eq_mul_card_filter {ι : Type*} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (c : ℕ) :
    (∑ i, if p i then c else 0) = c * ((Finset.univ : Finset ι).filter p).card := by
  classical
  simpa using
    (Finset.sum_ite_const_nat_eq_mul_card_filter (s := (Finset.univ : Finset ι)) p c)

/-- The constant `38` specialization over an arbitrary finset. -/
theorem Finset.sum_ite_thirtyEight_eq_mul_card_filter {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (∑ i ∈ s, if p i then 38 else 0) = 38 * (s.filter p).card := by
  simpa using Finset.sum_ite_const_nat_eq_mul_card_filter (s := s) p 38

/-- The constant `38` specialization over `univ`. -/
theorem Fintype.sum_ite_thirtyEight_eq_mul_card_filter {ι : Type*} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] :
    (∑ i, if p i then 38 else 0) = 38 * ((Finset.univ : Finset ι).filter p).card := by
  simpa using Fintype.sum_ite_const_nat_eq_mul_card_filter (ι := ι) p 38

end Moore57
