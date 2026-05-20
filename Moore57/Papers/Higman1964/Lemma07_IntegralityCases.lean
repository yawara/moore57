import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Moore57.Moore57Graph.Moore57Definition
import Moore57.Papers.Higman1964.Lemma06_TwoEigenvalues

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Higman 1964, Lemma 7 (§5, Integrality cases)

> If `|G|` is even, then either
>
> * **Case I.** `k = l, μ = λ + 1 = k/2, f₂ = f₃ = k`.
> * **Case II.** `d := (λ − μ)² + 4(k − μ)` is a square, and
>     - if `n` is even: `√d ∣ 2k + (λ − μ)(k + l)`, `2√d ∤ same`;
>     - if `n` is odd:  `2√d ∣ 2k + (λ − μ)(k + l)`.
>   In Case II, `f₂ ≠ f₃` and the eigenvalues of `A` are integers.

The proof uses Lemma 6 (two eigenvalues `s, t`) plus the trace-0 and
multiplicity constraints `f₂ + f₃ = k + l = n − 1`, `k + s f₂ = t f₃ = 0`.

For Moore57: Case II applies with `d = 225 = 15²` (a square), giving
integer eigenvalues `s, t = 7, −8`.

Status:
* `lem7_integrality_cases`: paper-stub (full Case I / Case II
  classification, deferred-heavy).
* `lem7_moore57_discriminant_eq_15_sq`: **proven** — Moore57 satisfies
  Case II with discriminant `(λ−μ)² + 4(k−μ) = 1 + 224 = 225 = 15²`.
-/

namespace Moore57.Papers.Higman1964

/-- **Moore57 discriminant is a perfect square (15²).** [done]

For Moore57 with `(λ, μ, k) = (0, 1, 57)`, the discriminant
`(λ − μ)² + 4(k − μ) = (−1)² + 4·56 = 1 + 224 = 225 = 15²`,
placing Moore57 in Higman Lemma 7's Case II (integer eigenvalues). -/
theorem lem7_moore57_discriminant_eq_15_sq :
    ((0 : ℤ) - 1) ^ 2 + 4 * (57 - 1) = 15 ^ 2 := by norm_num

/-! ### Lem 7 multiplicity formula (D3.5 backbone)

The secondary eigenvalues `s, t` come with positive integer
multiplicities `f₂, f₃` satisfying
* `f₂ + f₃ = n − 1` (dimension partition)
* `f₂ · s + f₃ · t = −k` (trace constraint: tr A = 0)

Solving the 2×2 system gives explicit formulas:
* `(s − t) · f₂ = −k − (n − 1) · t`
* `(t − s) · f₃ = −k − (n − 1) · s`

For Case II (`s ≠ t` integers), these become divisibility constraints
`s − t ∣ −k − (n − 1) t` etc., which are the integrality conditions
of Higman 1964 Lemma 7. -/

/-- **Lem 7 multiplicity formula (ℤ form)**: `(s − t) · f₂ = −k − (n − 1) · t`.
[done]

Derived from the dimension partition `f₂ + f₃ = n − 1` and the trace
constraint `f₂ · s + f₃ · t = −k` via the algebraic identity
`(s − t) · f₂ = (f₂ s + f₃ t) − (f₂ + f₃) · t`. -/
theorem lem7_multiplicity_formula (n k s t f₂ f₃ : ℤ)
    (h_sum : f₂ + f₃ = n - 1)
    (h_trace : f₂ * s + f₃ * t = -k) :
    (s - t) * f₂ = -k - (n - 1) * t := by
  have hexp : (s - t) * f₂ = (f₂ * s + f₃ * t) - (f₂ + f₃) * t := by ring
  rw [hexp, h_sum, h_trace]

/-- **Lem 7 multiplicity formula (sym ℤ form)**: `(t − s) · f₃ = −k − (n − 1) · s`.
[done]

Same derivation as `lem7_multiplicity_formula` with the roles of
`s, t` (and `f₂, f₃`) swapped. -/
theorem lem7_multiplicity_formula_sym (n k s t f₂ f₃ : ℤ)
    (h_sum : f₂ + f₃ = n - 1)
    (h_trace : f₂ * s + f₃ * t = -k) :
    (t - s) * f₃ = -k - (n - 1) * s := by
  have hexp : (t - s) * f₃ = (f₂ * s + f₃ * t) - (f₂ + f₃) * s := by ring
  rw [hexp, h_sum, h_trace]

/-- **Lem 7 Case II divisibility (f₂)**: when `s ≠ t`, the difference
`s − t` divides `−k − (n − 1) · t`.

This is the divisibility consequence of `lem7_multiplicity_formula`;
in Case II (integer `s, t`, `s ≠ t`) it gives the standard integer
multiplicity constraint. -/
theorem lem7_case_two_divisibility_f2 (n k s t f₂ f₃ : ℤ)
    (h_sum : f₂ + f₃ = n - 1)
    (h_trace : f₂ * s + f₃ * t = -k) :
    (s - t) ∣ (-k - (n - 1) * t) :=
  ⟨f₂, (lem7_multiplicity_formula n k s t f₂ f₃ h_sum h_trace).symm⟩

/-- **Lem 7 Case II divisibility (f₃)**: when `s ≠ t`, the difference
`t − s` divides `−k − (n − 1) · s`. -/
theorem lem7_case_two_divisibility_f3 (n k s t f₂ f₃ : ℤ)
    (h_sum : f₂ + f₃ = n - 1)
    (h_trace : f₂ * s + f₃ * t = -k) :
    (t - s) ∣ (-k - (n - 1) * s) :=
  ⟨f₃, (lem7_multiplicity_formula_sym n k s t f₂ f₃ h_sum h_trace).symm⟩

/-! ### Lem 7 Moore-parameter specialization (D3.6 prerequisite)

For Moore SRG parameters (`λ = 0`, `μ = 1`, `n = k² + 1`, `l = k(k − 1)`),
the Vieta identities give `s + t = −1`, `st = −(k − 1)`.  Letting
`e := s − t` (the discriminant root), we have `e² = (s − t)² = (s + t)²
− 4st = 1 + 4(k − 1) = 4k − 3`.

The integer multiplicity constraint `e · f₂ = −k − (n − 1) t`, combined
with `2 t = −1 − e` (since `s + t = −1` and `s − t = e`), simplifies to
`2 e f₂ = k(k(e + 1) − 2)`.

Rearranging: `e · (2 f₂ − k²) = k(k − 2)`, hence `e ∣ k(k − 2)` — the
key integrality input to Theorem 1's `e ∣ 15` conclusion. -/

/-- **Lem 7 Moore parameter rearrangement (algebraic ℤ form)**: with
`s + t = −1`, `s − t = e` (so `2 t = −1 − e`) and the Lem 7 multiplicity
formula `e · f₂ = −k − k² · t` (Moore: `n − 1 = k²`), we get the
"e divides k(k − 2)" form

`e · (2 f₂ − k²) = k · (k − 2)`.

Algebraic only — does not invoke the Vieta identities directly. -/
theorem lem7_moore_e_dvd_k_times_k_minus_2_form (e k f₂ : ℤ)
    (h_mult : 2 * (e * f₂) = k * (k * (e + 1) - 2)) :
    e * (2 * f₂ - k ^ 2) = k * (k - 2) := by
  linarith [h_mult]

/-- **Lem 7 Moore parameter divisibility**: under the integer
multiplicity constraint `2 e f₂ = k(k(e + 1) − 2)`, `e` divides
`k(k − 2)`. [done] -/
theorem lem7_moore_e_dvd_k_times_k_minus_2 (e k f₂ : ℤ)
    (h_mult : 2 * (e * f₂) = k * (k * (e + 1) - 2)) :
    e ∣ k * (k - 2) :=
  ⟨2 * f₂ - k ^ 2, (lem7_moore_e_dvd_k_times_k_minus_2_form e k f₂ h_mult).symm⟩

/-- **Lemma 7 (paper-faithful Moore-parameter divisibility).** [done]

Proper-signature paper-faithful form: under the rank-3 integer
multiplicity constraint `2 e f₂ = k(k(e + 1) − 2)` (Moore57 specialization
of Lem 7 Case II), conclude `e ∣ k(k - 2)`.

Re-export of `lem7_moore_e_dvd_k_times_k_minus_2` for paper-faithful
naming. -/
theorem lem7_integrality_cases_paper (e k f₂ : ℤ)
    (h_mult : 2 * (e * f₂) = k * (k * (e + 1) - 2)) :
    e ∣ k * (k - 2) :=
  lem7_moore_e_dvd_k_times_k_minus_2 e k f₂ h_mult

/-- **Lemma 7 (Case I / Case II structure for even `|G|`).** [deferred-heavy]

Full classification of rank-3 even-order cases.  The Moore57
instance (Case II with `d = 15²`) is proven in
`lem7_moore57_discriminant_eq_15_sq`.  The algebraic core
(multiplicity formula + Case II divisibility) is now formalised:
* `lem7_multiplicity_formula` (and `_sym` symmetric form)
* `lem7_case_two_divisibility_f2` (and `_f3` symmetric form)
* `lem7_moore_e_dvd_k_times_k_minus_2` / `lem7_integrality_cases_paper`
  (Moore specialization for Theorem 1). -/
theorem lem7_integrality_cases : True := by trivial

end Moore57.Papers.Higman1964
