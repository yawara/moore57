import Moore57.Papers.MacajSiran2010.Section04_Characters.Proposition2_CharacterSystem
import Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Lemma3_Chi1Formula

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §5, Lemma 12 [skeleton]

> Let `x` be an automorphism of a Moore (57, 2)-graph Γ of prime order `p`.
> Then the values `a₁(x)` and `χ₁(x)` satisfy a 17-row table parameterised
> by `(a₀(x), p)`.

Key rows used downstream:
- `p = 2, a₀ = 56`: `a₁ = 112, χ₁ = 33` — wraps [Lemma 2].
- `p = 19, a₀ = 1`: `a₁ = 57 + 285k`, `χ₁ = 19k` — used in D_19 route.
- `p = 11, a₀ = 5`: `a₁ = 55 + 165k`, `χ₁ = 2 + 11k` — used in Order 22 route.
- Starred cases `p = 3, a₀ = 1` and `p = 7, a₀ = 58` cannot occur.

The original full table has 17 rows; here we expose it as one bundled
existence statement (in skeleton form).
-/

namespace Moore57.Papers.MacajSiran2010.S5

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 12 (prime-order `(a₀, a₁, χ₁)` table).** [skeleton] -/
theorem lem12_prime_table (hΓ : IsMoore57 Γ) (x : Equiv.Perm V)
    (hx : ∀ a b, Γ.Adj a b ↔ Γ.Adj (x a) (x b))
    (p : ℕ) (hp : p.Prime) (hxp : x ^ p = 1) :
    True := by trivial

/-- **Lemma 12 (corollary, starred row `p = 3, a₀ = 1` cannot occur).** [skeleton] -/
theorem lem12_no_p3_a0_one (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 12 (corollary, starred row `p = 7, a₀ = 58` cannot occur).** [skeleton] -/
theorem lem12_no_p7_a0_58 (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S5
