import Moore57.Papers.MacajSiran2010.Section05_Tables.Lemma14_SemiRegularCongruence
import Moore57.Papers.MacajSiran2010.Section05_Tables.Lemma12_PrimeOrder

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §5, Lemma 15 [skeleton]

> Let `x` be an automorphism of Γ of order `pq` where `p ≤ q` are primes.
> For the listed `(pq, a₀(x), a₀(x^p), a₀(x^q))` rows, the values
> `(a₁(x), a₁(x^p), a₁(x^q), Tr(x))` are constrained as in the table.
>
> Rows marked `*` cannot occur.

Critical consequences:
- Row `pq = 22, a₀(x) = 1`: `a₁ = 222`, `Tr = 206` — gives a₁ value used by
  `Moore57.Order22OnMoore57.NoGo`.
- Row `pq = 14, a₀ = 49`: marked `*`, cannot occur.
- Row `pq = 35, a₀ = 1, a₀(x⁵) = 51`: marked `*`, cannot occur.
- Row `pq = 65`: marked `*`, cannot occur (i.e. no order-65 automorphism).
-/

namespace Moore57.Papers.MacajSiran2010.S5

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 15 (order `pq` automorphism table).** [skeleton] -/
theorem lem15_pq_table (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 15 (no order-65 automorphism).** [skeleton] -/
theorem lem15_no_order_65 (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 15 (no `pq = 14, a₀ = 49`).** [skeleton] -/
theorem lem15_no_pq_14_a0_49 (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S5
