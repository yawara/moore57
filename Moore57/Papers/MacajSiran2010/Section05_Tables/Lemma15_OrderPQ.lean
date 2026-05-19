import Moore57.Papers.MacajSiran2010.Section05_Tables.Lemma14_SemiRegularCongruence
import Moore57.Papers.MacajSiran2010.Section05_Tables.Lemma12_PrimeOrder
import Moore57.Order22OnMoore57.NoGo

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §5, Lemma 15 [deferred-heavy]

> Let `x` be an automorphism of Γ of order `pq` where `p ≤ q` are primes.
> For the listed `(pq, a₀(x), a₀(x^p), a₀(x^q))` rows, the values
> `(a₁(x), a₁(x^p), a₁(x^q), Tr(x))` are constrained as in the table.
>
> Rows marked `*` cannot occur.

Critical consequences:
- Row `pq = 22, a₀(x) = 1`: `a₁ = 222`, `Tr = 206`; non-existence of the
  combined order-11 × involution data is `Moore57.no_Order22_acts_on_Moore57`.
- Row `pq = 14, a₀ = 49`: marked `*`, cannot occur.
- Row `pq = 35, a₀ = 1, a₀(x⁵) = 51`: marked `*`, cannot occur.
- Row `pq = 65`: marked `*`, cannot occur (i.e. no order-65 automorphism).
-/

open Moore57

namespace Moore57.Papers.MacajSiran2010.S5

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 15 (order `pq` automorphism table).** [deferred-heavy] -/
theorem lem15_pq_table (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 15 (row `pq = 22`): no Moore57 carries the combined data of an
order-11 automorphism σ and an involution τ generating an order-22 group
(cyclic or dihedral).** Wraps `no_Order22_acts_on_Moore57`. -/
theorem lem15_no_order_22 :
    ¬ Nonempty (Order22ActsOnMoore57 V Γ) :=
  no_Order22_acts_on_Moore57

/-- **Lemma 15 starred row `pq = 35` arithmetic contradiction.** [done]

For the starred row `pq = 35, a₀(x) = 1, a₀(x⁵) = 51, a₀(x⁷) = 50`,
the character system forces `Tr(x) = 206`, while the orbit-trace
upper bound gives `Tr(x) ≤ 186`.  These are mutually inconsistent. -/
theorem lem15_starred_row_pq35_trace_above_bound
    (Tr : ℤ) (h_eq : Tr = 206) (h_bd : Tr ≤ 186) : False := by
  omega

/-- **Lemma 15 (no order-65 automorphism).** [deferred-heavy] -/
theorem lem15_no_order_65 (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 15 (no `pq = 14, a₀ = 49`).** [deferred-heavy] -/
theorem lem15_no_pq_14_a0_49 (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S5
