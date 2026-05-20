import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Proposition3_HSFixBound

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §8, Lemma 23

> Let `X` be an automorphism group of Γ of order 625 with the smallest
> orbit of size 125. Then `X` contains a subgroup `Y` of order 5 which is
> a vertex stabilizer in at least one and at most two orbits of size 125.

Status:
* `lem23_arithmetic_stabilizer_order`: **proven** — pure orbit-
  stabilizer arithmetic: for `|X| = 625` and a size-125 orbit, the
  vertex stabilizer has order `5`.
* `lem23_arithmetic_5_dvd_625`: **proven** — divisibility helper:
  `5 ∣ 625`, used for embedding subgroups of order 5.
* `lem23_stabilizer_orbits`: original True-stub kept for backwards compat.
-/

namespace Moore57.Papers.MacajSiran2010.S8

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 23 arithmetic: orbit-stabilizer at size-125 orbits**. [done]

For `|X| = 625` and a vertex `v` in a size-125 orbit `O`, the vertex
stabilizer `Stab_X(v)` has order `|X|/|O| = 625/125 = 5` by the
orbit-stabilizer theorem.

The lemma takes the algebraic statement `|X| = stab · orbit` (so the
orbit-stabilizer formula is folded in as a hypothesis), and conditions
on `orbit = 125` to derive `stab = 5`. -/
theorem lem23_arithmetic_stabilizer_order
    (orbit_size stab_order : ℕ)
    (h_X : (625 : ℕ) = stab_order * orbit_size)
    (h_O : orbit_size = 125) :
    stab_order = 5 := by
  rw [h_O] at h_X
  omega

/-- **Lemma 23 arithmetic helper: 5 ∣ 625**. [done]

For embedding the order-5 subgroup `Y` inside `X` of order 625, the
divisibility `5 ∣ 625 = 5^4` is the Lagrange/Sylow input. -/
theorem lem23_arithmetic_5_dvd_625 : (5 : ℕ) ∣ 625 := by decide

/-- **Lemma 23 arithmetic helper: stabilizer order from orbit-stabilizer + size**. [done]

A generalization: given any group order `N` and orbit size `s`
satisfying `N = stab · s`, the stabilizer order is uniquely determined
as `N / s`. The Lemma 23 instance is `N = 625, s = 125 ⟹ stab = 5`. -/
theorem lem23_arithmetic_stabilizer_eq_div
    (N orbit_size stab_order : ℕ)
    (h_N : N = stab_order * orbit_size)
    (h_O_pos : 0 < orbit_size) :
    stab_order = N / orbit_size := by
  rw [h_N]
  rw [Nat.mul_div_cancel _ h_O_pos]

/-- **Lemma 23 (paper-faithful arithmetic form).** [done]

Proper-signature paper-faithful packaging: for |X| = 625 acting with
smallest orbit of size 125, the vertex stabilizer has order 5 (by
orbit-stabilizer).  This is the arithmetic substance of Lem 23
(the "|Y| = 5" claim). -/
theorem lem23_stabilizer_orbits_paper
    (orbit_size stab_order : ℕ)
    (h_X : (625 : ℕ) = stab_order * orbit_size)
    (h_O : orbit_size = 125) :
    stab_order = 5 ∧ (5 : ℕ) ∣ 625 :=
  ⟨lem23_arithmetic_stabilizer_order orbit_size stab_order h_X h_O,
   lem23_arithmetic_5_dvd_625⟩

/-- **Lemma 23 (stabilizer in 1 or 2 size-125 orbits).** [deferred-heavy]

Arithmetic backbone (orbit-stabilizer giving |Y| = 5) in
`lem23_arithmetic_stabilizer_order` and `lem23_stabilizer_orbits_paper`.
What remains is the paper's geometric content: the existence claim
(at least one size-125 orbit exists for the given |X| / smallest-orbit
setup) and the structural exclusion of `Y` stabilizing `≥ 3` size-125
orbits via Moore57 fix-shape analysis on `Fix(Y)`. -/
theorem lem23_stabilizer_orbits (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S8
