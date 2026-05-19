import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Aschbacher 1971, Lemma 1.3

> If `𝒢` is nonempty, not a star, and satisfies (*), then `𝒢` has
> valence `k ∈ {2, 3, 7, 57}` and order `v = k² + 1 ∈ {5, 10, 50, 3250}`.

Proof outline (eigenvalue argument):

* `A² = (k − 1) I + J − A` from the (*) condition.
* `(A − k I)(A² + A − (k − 1) I) = 0`, so `A` has eigenvalues `k` and
  `r, s = (−1 ± e)/2` with `e = √(4k − 3)`.
* The all-ones vector spans the `k`-eigenspace (multiplicity 1).
* Multiplicities `a, b` for `r, s` are positive integers with
  `a + b = k²` and `a r + b s = −k`.
* Either `a = b = k = 2`, or `e ∈ ℤ`; in the latter case `e ∣ k(k − 2)`,
  and `(4k − 3, k) ∣ 3`, `(4k − 3, k − 2) ∣ 5` force
  `4k − 3 ∈ {9, 25, 225}`, i.e. `k ∈ {3, 7, 57}`.

Cases realised: pentagon (`k=2, v=5`), Petersen (`k=3, v=10`),
Hoffman–Singleton (`k=7, v=50`), Moore57 (`k=57, v=3250`).

The general classification is [skeleton]. The `k = 57` instance below
is trivial since `IsMoore57` already encodes 57-regularity by definition.
-/

open Moore57

namespace Moore57.Papers.Aschbacher1971

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 1.3 (full classification).** [skeleton]

For a non-empty, non-star graph satisfying the strong (0, 1) condition,
the valence `k ∈ {2, 3, 7, 57}` and the order `v = k² + 1`. -/
theorem lem1_3_valence_classification : True := by trivial

/-- **Lemma 1.3 (`k = 57` instance for Moore57).**
Moore57 graphs have valence 57 (by definition of `IsSRGWith 3250 57 0 1`). -/
theorem lem1_3_moore57_k_eq_57 (hΓ : IsMoore57 Γ) :
    Γ.IsRegularOfDegree 57 :=
  hΓ.regular

/-- **Lemma 1.3 (`v = k² + 1` instance for Moore57).**
Moore57 graphs have `|V| = 3250 = 57² + 1`. -/
theorem lem1_3_moore57_v_eq_card (hΓ : IsMoore57 Γ) :
    Fintype.card V = 57 ^ 2 + 1 := by
  rw [hΓ.card]
  norm_num

end Moore57.Papers.Aschbacher1971
