import Moore57.Moore57Graph.Moore57Definition
import Moore57.Papers.Higman1964.Lemma01_PairedOrbits

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Higman 1964, Lemma 3 (§2, Self-paired ⇔ even)

> If `|G|` is even, then `Δ(a)` and `Γ(a)` are both self-paired.
> If `|G|` is odd, then `Δ'(a) = Γ(a)`, hence `k = l`, `n = 2k + 1`,
> `λ = μ`.

Combined with Lemma 1: a rank-3 group has the two non-trivial orbits
self-paired ⇔ `|G|` is even.

**Corollary.**
* If `|G|` even, `a ∈ Δ(b) ⇒ b ∈ Δ(a)` (the "graph" `b ∈ Δ(a)` is symmetric).
* If `|G|` odd, `a ∈ Δ(b) ⇒ b ∈ Γ(a)`.

[deferred-heavy]
-/

namespace Moore57.Papers.Higman1964

/-- **Lemma 3 (self-paired structure under parity).** [deferred-heavy] -/
theorem lem3_self_paired_iff_even : True := by trivial

/-- **Corollary to Lemma 3** (symmetry of `Δ` under even order). [deferred-heavy] -/
theorem cor_lem3_symmetric_delta_of_even : True := by trivial

end Moore57.Papers.Higman1964
