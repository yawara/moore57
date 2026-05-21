import Moore57.Moore57Graph.Moore57Definition
import Moore57.Papers.Higman1964.Theorem1_DegreeKSqPlus1

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Aschbacher 1971, Lemma 1.3

> If `𝒢` is nonempty, not a star, and satisfies (*), then `𝒢` has
> valence `k ∈ {2, 3, 7, 57}` and order `v = k² + 1 ∈ {5, 10, 50, 3250}`.

Proof outline (eigenvalue argument):

* `A² + A - (k − 1) I = J` from the (*) condition (SRG identity).
* `(A − k I)(A² + A − (k − 1) I) = (A − k I) · J = 0`, so `A` has eigenvalues
  `k` and `r, s = (−1 ± e)/2` with `e = √(4k − 3)`.
* The all-ones vector spans the `k`-eigenspace (multiplicity 1).
* Multiplicities `a, b` for `r, s` are non-negative integers with
  `a + b = k²` and `a r + b s = −k`.
* Either `a = b` (forcing `k = 2`), or `e ∈ ℤ`; in the latter case
  `e ∣ k(k − 2)`, and the gcd analysis `(4k − 3, k) ∣ 3`,
  `(4k − 3, k − 2) ∣ 5` force `e ∣ 15`, hence
  `4k − 3 ∈ {9, 25, 225}`, i.e. `k ∈ {3, 7, 57}`.

Cases realised: pentagon (`k=2, v=5`), Petersen (`k=3, v=10`),
Hoffman–Singleton (`k=7, v=50`), Moore57 (`k=57, v=3250`).

What we formalise here:

* `lem1_3_srg_card_eq` — `n = k² + 1` for any `IsSRGWith n k 0 1` graph.
* `lem1_3_moore57_k_eq_57`, `lem1_3_moore57_v_eq_card` — the Moore57
  instances of the conclusion (trivial from `IsMoore57`'s definition).

The full classification `k ∈ {2, 3, 7, 57}` (the eigenvalue + integrality
argument) and the generic SRG matrix identity `A² + A − (k−1)I = J` over
`ℚ` (a `k`-parameterised generalisation of `IsMoore57.adjMatrix_sq_eq`)
remain skeletons.
-/

open Moore57

namespace Moore57.Papers.Aschbacher1971

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 1.3 (`v = k² + 1`).**
For any `IsSRGWith n k 0 1` graph with at least one vertex, the vertex
count satisfies `n = k² + 1`. -/
theorem lem1_3_srg_card_eq {n k : ℕ} (hΓ : Γ.IsSRGWith n k 0 1)
    (hn : 0 < n) :
    n = k ^ 2 + 1 := by
  -- `IsSRGWith.param_eq` for `(ℓ, μ) = (0, 1)`: `k * (k - 1) = n - k - 1`.
  have hparam := SimpleGraph.IsSRGWith.param_eq Γ hΓ hn
  -- raw: `k * (k - 0 - 1) = (n - k - 1) * 1`; normalise to `k * (k - 1) = n - k - 1`.
  rw [Nat.sub_zero, Nat.mul_one] at hparam
  have hcard : Fintype.card V = n := hΓ.card
  have hVne : Nonempty V := Fintype.card_pos_iff.mp (hcard ▸ hn)
  obtain ⟨v⟩ := hVne
  have hk_le : k ≤ Fintype.card V - 1 := by
    have hdeg := Γ.degree_lt_card_verts v
    have hkv := hΓ.regular v
    omega
  rw [hcard] at hk_le
  -- hk_le : k ≤ n - 1
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- k = 0: hparam ⇒ 0 = n - 1 ⇒ n = 1 = 0² + 1.
    subst hk
    simp at hparam
    omega
  · -- k ≥ 1: `k² = k(k − 1) + k`, combined with hparam and hk_le yields n = k² + 1.
    have hkk : k * (k - 1) + k = k * k := by
      cases k with
      | zero => omega
      | succ m =>
        simp only [Nat.succ_sub_one]
        ring
    rw [sq, ← hkk]
    omega

/-- **Lemma 1.3 arithmetic core** (via Higman 1964 Theorem 1).  [done]

Given the integrality data `4·k = e² + 3` (equivalently `4k − 3 = e²`)
and `e² ∣ 225`, the only possible `k` values are `{1, 3, 7, 57}`.

This wraps `Moore57.Papers.Higman1964.theorem1_arithmetic_core`.
Aschbacher's `k = 2` case is the separate `a = b` branch
(corresponding to the pentagon `IsSRGWith 5 2 0 1`), not covered by
this arithmetic core. -/
theorem lem1_3_arithmetic_core {k e : ℕ}
    (h_eq : 4 * k = e * e + 3) (h_dvd : e * e ∣ 225) :
    k = 1 ∨ k = 3 ∨ k = 7 ∨ k = 57 :=
  Moore57.Papers.Higman1964.theorem1_arithmetic_core h_eq h_dvd

/-- **Lemma 1.3 (full `k ∈ {2, 3, 7, 57}` classification).** [deferred-heavy]

The generic SRG matrix identity `A² + A − (k − 1) • I = J` over `ℚ` and the
subsequent eigenvalue/integrality argument leading to
`k ∈ {2, 3, 7, 57}` remain unformalised at the SRG-bridge level.  The
arithmetic core for the `(a ≠ b)` branch is proven in
`lem1_3_arithmetic_core`; for the `k = 2` (pentagon, `a = b`) branch
see Cameron Ch.3 §3.5 / `Higman1964.Theorem1_moore57_valence`.
For `k = 57` see `IsMoore57.adjMatrix_sq_eq`. -/
theorem lem1_3_valence_classification : True := by trivial

/-- **Lemma 1.3 (paper-faithful conditional dispatch, `a ≠ b` branch).** [done]

Proper-signature paper-faithful packaging of the `(a ≠ b)` integrality
branch: given the eigenvalue integrality data `4k = e² + 3` and
`e² ∣ 225`, conclude `k ∈ {1, 3, 7, 57}`.

This is the proper-signature variant of `lem1_3_valence_classification`
for the non-pentagon branch.  Delegates to `lem1_3_arithmetic_core`
which in turn wraps `Higman1964.theorem1_arithmetic_core`.

The pentagon branch (`k = 2`, `a = b`) is excluded by this signature
but handled separately via Cameron Ch.3 §3.5 / `Higman1964` valence
analysis. -/
theorem lem1_3_valence_classification_paper {k e : ℕ}
    (h_eq : 4 * k = e * e + 3) (h_dvd : e * e ∣ 225) :
    k = 1 ∨ k = 3 ∨ k = 7 ∨ k = 57 :=
  lem1_3_arithmetic_core h_eq h_dvd

/-- **Lemma 1.3 (`k = 57` instance for Moore57).** -/
theorem lem1_3_moore57_k_eq_57 (hΓ : IsMoore57 Γ) :
    Γ.IsRegularOfDegree 57 :=
  hΓ.regular

/-- **Lemma 1.3 (`v = k² + 1 = 3250` instance for Moore57).** -/
theorem lem1_3_moore57_v_eq_card (hΓ : IsMoore57 Γ) :
    Fintype.card V = 57 ^ 2 + 1 := by
  rw [hΓ.card]
  norm_num

end Moore57.Papers.Aschbacher1971
