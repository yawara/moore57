import Moore57.Papers.MacajSiran2010.Section05_Tables.Lemma12_PrimeOrder

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §5, Lemma 13 [deferred-heavy]

> Let `x` be an automorphism of Γ of order `p²` where `p = 3` or `p = 5`.
> Then the values `a₁(x), a₁(x^p), Tr(x)` satisfy a 6-row table.
>
> Two rows (marked `*`) require non-integral traces and cannot occur.

Used downstream: this excludes orders `p² · q` configurations and feeds
into Theorems 4, 5.
-/

namespace Moore57.Papers.MacajSiran2010.S5

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 13 (`p²`-order auto: `(a₁(x), a₁(x^p), Tr(x))` table).** [deferred-heavy] -/
theorem lem13_prime_squared_table (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S5
