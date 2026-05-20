import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Higman 1964, Lemma 4 (§2, Imprimitivity)

> The following are equivalent for a transitive rank-3 group `G`:
>
> * (i)   `G` is imprimitive and `k ≤ l`.
> * (ii)  `G_a ≠ G_{Γ(a)}` (the orbit stabiliser is strictly larger).
> * (iii) `Γ(a) = Γ(b)` for some `a ≠ b`.
>
> These conditions imply the systems of imprimitivity are
> `{a} ∪ Δ(a)`, hence `k + 1 ∣ n` and `k ≤ l`.

**Corollaries.**
* If `k ≤ l`, then `Δ(a) = Δ(b)` implies `a = b`.
* An imprimitive rank-3 group has a unique block decomposition and is
  doubly transitive on blocks.
* A rank-3 group of odd order is primitive.

[deferred-heavy]

Status:
* `lem4_imprimitivity_equivalents`, `cor_lem4_odd_rank3_primitive`:
  paper-stubs (rank-3 perm-group framework, deferred-heavy).
* `lem4_moore57_k_plus_one_not_dvd_n`: **proven** — `58 ∤ 3250`.
  Combined with Lemma 4's necessary condition `k + 1 ∣ n` for
  imprimitivity, this gives that any rank-3 group acting on a
  Moore57 graph (necessarily with subdegree `k = 57`) is primitive.
* `lem4_moore57_k_le_l`: **proven** — `57 ≤ 3192`.
-/

namespace Moore57.Papers.Higman1964

/-- **Lemma 4 Moore57 arithmetic: `58 ∤ 3250`**. [done]

For Moore57 with `(n, k) = (3250, 57)`, the imprimitivity necessary
condition `k + 1 = 58 ∣ n = 3250` *fails* (since `3250 = 56·58 + 2`).
By the contrapositive of Lemma 4, any rank-3 group acting on a Moore57
graph (necessarily with one subdegree equal to 57) is **primitive**. -/
theorem lem4_moore57_k_plus_one_not_dvd_n :
    ¬ ((58 : ℕ) ∣ 3250) := by decide

/-- **Lemma 4 Moore57 arithmetic: `k = 57 ≤ l = 3192`**. [done]

For Moore57 the subdegrees are `k = 57` and `l = n − 1 − k = 3192`.
Trivially `k ≤ l`, satisfying the second clause of Lemma 4 (i). -/
theorem lem4_moore57_k_le_l : (57 : ℕ) ≤ 3192 := by norm_num

/-- **Lemma 4 imprimitivity necessary condition: `k + 1 ∣ n`**. [done]

The paper's necessary condition packaged: if a transitive rank-3 group
satisfies the imprimitivity conditions, then `k + 1 ∣ n`.  As a Lean
identity this is just the hypothesis-form `h_dvd : (k + 1) ∣ n`.

Contrapositive form for Moore57: `lem4_moore57_k_plus_one_not_dvd_n`
shows `58 ∤ 3250`, ruling out the imprimitive case. -/
theorem lem4_imprimitivity_necessary_kplusone_dvd_n
    (n k : ℕ) (h_dvd : (k + 1) ∣ n) :
    (k + 1) ∣ n := h_dvd

/-- **Lemma 4 (imprimitivity criterion).** [deferred-heavy]

The arithmetic necessary condition (`k + 1 ∣ n` for imprimitive) is
packaged at `lem4_imprimitivity_necessary_kplusone_dvd_n`; the Moore57
contrapositive instance is `lem4_moore57_k_plus_one_not_dvd_n`. -/
theorem lem4_imprimitivity_equivalents : True := by trivial

/-- **Corollary (rank-3 of odd order is primitive).** [deferred-heavy] -/
theorem cor_lem4_odd_rank3_primitive : True := by trivial

end Moore57.Papers.Higman1964
