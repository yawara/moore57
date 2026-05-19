import Moore57.Papers.Higman1964.Citation
import Moore57.Papers.Higman1964.Lemma01_PairedOrbits
import Moore57.Papers.Higman1964.Lemma02_IntersectionNumbers
import Moore57.Papers.Higman1964.Lemma03_SelfPaired
import Moore57.Papers.Higman1964.Lemma04_Imprimitivity
import Moore57.Papers.Higman1964.Lemma05_BlockDesignCount
import Moore57.Papers.Higman1964.Lemma06_TwoEigenvalues
import Moore57.Papers.Higman1964.Lemma07_IntegralityCases
import Moore57.Papers.Higman1964.Theorem1_DegreeKSqPlus1

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Higman 1964 — top-level re-export

This file exposes the paper's headline results under
`Moore57.Papers.Higman1964`:

* `theorem1_arithmetic_core` — the proven number-theoretic step
  underlying §6 Theorem 1 (`4k = e² + 3` and `e² ∣ 225` ⇒
  `k ∈ {1, 3, 7, 57}`).
* `theorem1_n_kSq_plus_one` — full §6 Theorem 1 statement (rank-3,
  `n = k² + 1` ⇒ `n ∈ {5, 10, 50, 3250}`). [skeleton]
* Lemmas 1–7 — skeletons matching §1–§5 of the paper.

Theorem 1 is the load-bearing fact that Aschbacher 1971 cites with
"Results of D. Higman show that 𝒢 satisfies (*) [2]". With Higman 1964
now in scope, Aschbacher 1971's `main_no_rank3_3250_57` can declare its
external dependency satisfied (at the statement level) by Theorem 1.

(The deeper structural content — `λ = 0, μ = 1` from primitivity + Lemma 5;
integer eigenvalues from Lemma 7 Case II — is still skeletal. Cameron
Ch.3 §3.5 Theorem 3.12 is the modern SRG-framework formulation; see
`Moore57.Papers.CameronCh3.theorem3_12_moore_diameter_two_classification`.)
-/
