import Moore57.Papers.MacajSiran2010.Section05_Tables.Lemma12_PrimeOrder

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §5, Lemma 13

> Let `x` be an automorphism of Γ of order `p²` where `p = 3` or `p = 5`.
> Then the values `a₁(x), a₁(x^p), Tr(x)` satisfy a 6-row table.
>
> Two rows (marked `*`) require non-integral traces and cannot occur.

Status:
* `lem13_prime_squared_table` — full 6-row table, deferred-heavy.
* `lem13_starred_row_5_0_5_no_integer_trace` and
  `lem13_starred_row_5_5_5_no_integer_trace` — **proven** arithmetic
  cores for the two starred rows (non-integrality contradictions).
-/

namespace Moore57.Papers.MacajSiran2010.S5

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 13 starred row arithmetic: row `5* (0, 5)` excluded.** [done]

For `p = 5`, `a₀(x) = 0`, `a₀(x⁵) = 5`, the paper's character system
forces `Tr(x) = 33.6 + 60·k + 60·l`, equivalently
`5·Tr(x) = 168 + 300·k + 300·l`.  Since `168 ≡ 3 (mod 5)`, no integer
`Tr(x)` can satisfy this, hence the row cannot occur. -/
theorem lem13_starred_row_5_0_5_no_integer_trace
    (Tr : ℤ) (k l : ℕ) (h : 5 * Tr = 168 + 300 * k + 300 * l) :
    False := by
  omega

/-- **Lemma 13 starred row arithmetic: row `5* (5, 5)` excluded.** [done]

For `p = 5`, `a₀(x) = 5`, `a₀(x⁵) = 5`, the paper's character system
forces `Tr(x) = 21.6 + 60·k + 60·l`, equivalently
`5·Tr(x) = 108 + 300·k + 300·l`.  Since `108 ≡ 3 (mod 5)`, no integer
`Tr(x)` can satisfy this, hence the row cannot occur. -/
theorem lem13_starred_row_5_5_5_no_integer_trace
    (Tr : ℤ) (k l : ℕ) (h : 5 * Tr = 108 + 300 * k + 300 * l) :
    False := by
  omega

/-- **Lemma 13 (`p²`-order auto: `(a₁(x), a₁(x^p), Tr(x))` table).** [deferred-heavy]

The full 6-row table requires Proposition 2 (character system) and
Lemma 3 (character formula).  Arithmetic cores for the two starred
(non-integral) rows are proven above. -/
theorem lem13_prime_squared_table (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S5
