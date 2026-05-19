import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Lemma25_NormalSylowAction
import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma19_LargePrime

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Lemma 26 [skeleton]

> In the standing notation `|X| = p^a q^b` with `p, q` distinct odd primes
> and `a, b ≥ 1`, we have `p ≤ 5` or `q ≤ 5`.

Proof outline (paper): suppose `p, q ∈ {7, 11, 13, 19}`. By Sylow's
theorem and Lemma 19, both `P` and `Q` must be normal in `X`, so
`X = P × Q`. Then `P` acts on `Fix(Q)` and vice versa; only one
compatible configuration exists (`p = 7, q = 19, P ≅ Z₇, |Fix(P)| = 58`),
which contradicts Lemma 12 (the starred row `p = 7, a₀ = 58`).
-/

namespace Moore57.Papers.MacajSiran2010.S9

/-- **Lemma 26 (`p ≤ 5` or `q ≤ 5`).** [skeleton] -/
theorem lem26_small_prime : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
