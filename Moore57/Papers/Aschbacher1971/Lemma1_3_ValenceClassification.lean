import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Aschbacher 1971, Lemma 1.3 [skeleton]

> If `𝒢` is nonempty, not a star, and satisfies (*), then `𝒢` has
> valence `k ∈ {2, 3, 7, 57}` and order `v = k² + 1 ∈ {5, 10, 50, 3250}`.

Proof outline (eigenvalue argument):
* `A² = (k − 1) I + J − A` from the (*) condition.
* `(A − k I)(A² + A − (k − 1) I) = 0`, so `A` has eigenvalues
  `k` and `r, s = (−1 ± e)/2` with `e = √(4k − 3)`.
* The all-ones vector spans the `k`-eigenspace (multiplicity 1).
* Multiplicities `a, b` for `r, s` are positive integers with
  `a + b = k²` and `a r + b s = −k`.
* Either `a = b = k = 2`, or `e ∈ ℤ`; in the latter case `e | k(k − 2)`,
  and `(4k − 3, k) | 3`, `(4k − 3, k − 2) | 5` force
  `4k − 3 ∈ {9, 25, 225}`, i.e. `k ∈ {3, 7, 57}`.

The `k = 57` case is the Moore57 graph we care about; cases `k = 2, 3, 7`
are realised by the pentagon, the Petersen graph and the Hoffman–Singleton
graph respectively.
-/

namespace Moore57.Papers.Aschbacher1971

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 1.3 (valence ∈ {2, 3, 7, 57}).** [skeleton] -/
theorem lem1_3_valence_classification : True := by trivial

end Moore57.Papers.Aschbacher1971
