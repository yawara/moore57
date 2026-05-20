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

Status:
* `lem3_self_paired_iff_even`, `cor_lem3_symmetric_delta_of_even`:
  paper-stubs (rank-3 paired-orbit framework, deferred-heavy).
* `lem3_odd_order_arithmetic`: **proven** — pure ℕ arithmetic
  packaging the `n = 2k + 1` identity from odd-order case.
* `lem3_moore57_no_odd_aut_via_n_parity`: **proven** — Moore57's
  `n = 3250` is even, so it cannot satisfy `n = 2k + 1` for any `k`,
  hence the odd-order rank-3 case cannot apply to Moore57.
-/

namespace Moore57.Papers.Higman1964

/-- **Lemma 3 odd-order arithmetic: `n = 2k + 1`**. [done]

The paper's odd-`|G|` rank-3 conclusion: `k = l` and `n = 1 + k + l = 1 + 2k`.
Packaged as a conditional identity. -/
theorem lem3_odd_order_arithmetic
    (n k l : ℕ)
    (h_n : n = 1 + k + l)
    (h_eq : k = l) :
    n = 2 * k + 1 := by
  rw [h_n, h_eq]; ring

/-- **Lemma 3 Moore57 contrapositive: `n = 3250` is even, so no odd-order
rank-3 action**. [done]

For Moore57 with `n = 3250` (even), the necessary condition `n = 2k + 1`
(odd) of the odd-`|G|` case *fails* — there is no `k : ℕ` with
`3250 = 2k + 1`.  Hence any rank-3 group acting on Moore57 has *even*
order, consistent with Lem 5 Cor 1 (`λ ≠ μ` for Moore57). -/
theorem lem3_moore57_no_odd_aut_via_n_parity :
    ¬ ∃ k : ℕ, (3250 : ℕ) = 2 * k + 1 := by
  intro ⟨k, hk⟩
  omega

/-- **Lemma 3 (self-paired structure under parity).** [deferred-heavy] -/
theorem lem3_self_paired_iff_even : True := by trivial

/-- **Corollary to Lemma 3** (symmetry of `Δ` under even order). [deferred-heavy] -/
theorem cor_lem3_symmetric_delta_of_even : True := by trivial

end Moore57.Papers.Higman1964
