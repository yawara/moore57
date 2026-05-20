import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Lemma23_StabilizerOrbits

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §8, Lemma 24

> Let `X` have order 625 and let the smallest orbit of `X` have size 125.
> Then `X` has at least two orbits of size 125.

Proof outline (paper): pick a central element `x ∈ X` of order 5. By
Lemma 12, `a₁(x) > 0`, so `x` contributes to at least one orbit `O`. By
Lemma 7, `|O| ≤ a₁(x)`, and by Corollary 1, `a₁(x) ≤ 500`. So `|O| ≤ 500`.
Moreover `x` and `x²` contribute to different orbits.

Status:
* `lem24_arithmetic_orbit_decomposition`: **proven** — pure orbit-count
  arithmetic. With `|X| = 625` and smallest orbit `≥ 125`, orbit sizes
  are in `{125, 625}`, and `3250 = 625·i + 125·j` forces
  `(i, j) ∈ {(0, 26), (1, 21), (2, 16), (3, 11), (4, 6), (5, 1)}`.
* `lem24_arithmetic_j_ge_two_of_not_j_one`: **proven** — conditional
  bridge: ruling out `(i, j) = (5, 1)` from the six configurations
  gives `j ≥ 2`. The paper rules out `j = 1` via the central order-5
  element + Lem 7 + Cor 1 argument (deferred-heavy).
* `lem24_two_orbits`: original True-stub kept for backwards compat.
-/

namespace Moore57.Papers.MacajSiran2010.S8

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 24 arithmetic core: orbit decomposition for `|X| = 625` with
smallest orbit `≥ 125`.** [done]

Given non-negative integers `i, j` (numbers of size-625 and size-125
orbits respectively) with `625·i + 125·j = 3250`, the solutions are
precisely the six pairs:

  `(0, 26), (1, 21), (2, 16), (3, 11), (4, 6), (5, 1)`.

Pure `omega` enumeration. -/
theorem lem24_arithmetic_orbit_decomposition
    (i j : ℕ) (h : 625 * i + 125 * j = 3250) :
    (i = 0 ∧ j = 26) ∨ (i = 1 ∧ j = 21) ∨ (i = 2 ∧ j = 16) ∨
    (i = 3 ∧ j = 11) ∨ (i = 4 ∧ j = 6) ∨ (i = 5 ∧ j = 1) := by
  omega

/-- **Lemma 24 conditional bridge: `j ≥ 2` from excluding `(5, 1)`.** [done]

The orbit-decomposition arithmetic gives six configurations. Five of
them (the `j ∈ {26, 21, 16, 11, 6}` cases) directly satisfy `j ≥ 2`.
The remaining case `(i, j) = (5, 1)` is excluded by the paper's
central-order-5 + Lem 7 + Cor 1 argument (which forces the contributing
orbit `O` of a central order-5 element to satisfy `|O| ≤ 500`, hence
`|O| = 125`, and `x` vs `x²` give two distinct such orbits).

Given the exclusion of `(5, 1)` as a hypothesis, this lemma derives
`j ≥ 2` by pure omega. -/
theorem lem24_arithmetic_j_ge_two_of_not_j_one
    (i j : ℕ) (h : 625 * i + 125 * j = 3250)
    (h_no_51 : ¬ (i = 5 ∧ j = 1)) :
    j ≥ 2 := by
  rcases lem24_arithmetic_orbit_decomposition i j h with
    ⟨_, hj⟩ | ⟨_, hj⟩ | ⟨_, hj⟩ | ⟨_, hj⟩ | ⟨_, hj⟩ | ⟨hi, hj⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact absurd ⟨hi, hj⟩ h_no_51

/-- **Lemma 24 arithmetic core: `j ≥ 1` always**. [done]

Even without the central-element argument, the orbit-decomposition
arithmetic itself forces `j ≥ 1`: there is no solution to
`625·i + 125·j = 3250` with `j = 0` (since `3250 / 625 = 5.2`, not
an integer).

This is a strictly weaker conclusion than Lemma 24 (`j ≥ 2`); it
captures the part of Lemma 24 that needs no paper-specific input. -/
theorem lem24_arithmetic_j_ge_one
    (i j : ℕ) (h : 625 * i + 125 * j = 3250) :
    j ≥ 1 := by
  omega

/-- **Lemma 24 (`|X| = 625` with smallest orbit 125 has ≥ 2 such orbits).** [deferred-heavy]

The arithmetic backbone is fully formalized in
`lem24_arithmetic_orbit_decomposition` + `lem24_arithmetic_j_ge_two_of_not_j_one`.
What remains is the paper's central order-5 + Lemma 7 + Corollary 1
geometric exclusion of `(i, j) = (5, 1)`. -/
theorem lem24_two_orbits (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S8
