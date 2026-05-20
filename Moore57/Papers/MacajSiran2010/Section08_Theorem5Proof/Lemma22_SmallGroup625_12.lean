import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.IntervalCases
import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Proposition3_HSFixBound

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §8, Lemma 22 [GAP]

> If `X` is a group of automorphisms of Γ of order 625 and with the
> smallest orbit size 25, then `X ≅ SmallGroup(625, 12)` of the GAP library.

Lean strategy: hand-construct `SmallGroup(625, 12)` and verify uniqueness
criterion via `native_decide`. Performance with 625-element group may be
borderline.

Status:
* `lem22_arithmetic_stabilizer_25`: **proven** — pure orbit-stabilizer
  arithmetic: for `|X| = 625` and a size-25 orbit, the vertex stabilizer
  has order `625 / 25 = 25`.
* `lem22_arithmetic_orbit_25_dvd_625`: **proven** — size-25 orbits
  divide `|X| = 625`.
* `lem22_arithmetic_orbit_decomp_smallest_25`: **proven** — pure
  arithmetic enumeration of orbit decompositions with smallest orbit
  size 25 for `|X| = 625`.
* `lem22_smallGroup_625_12`: original True-stub kept for backwards
  compat (GAP-dependent SG(625, 12) identification).
-/

namespace Moore57.Papers.MacajSiran2010.S8

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 22 arithmetic: orbit-stabilizer at size-25 orbits**. [done]

For `|X| = 625` and a vertex `v` in a size-25 orbit `O`, the vertex
stabilizer `Stab_X(v)` has order `|X|/|O| = 625/25 = 25` by the
orbit-stabilizer theorem. -/
theorem lem22_arithmetic_stabilizer_25
    (orbit_size stab_order : ℕ)
    (h_X : (625 : ℕ) = stab_order * orbit_size)
    (h_O : orbit_size = 25) :
    stab_order = 25 := by
  rw [h_O] at h_X
  omega

/-- **Lemma 22 arithmetic helper: 25 ∣ 625**. [done] -/
theorem lem22_arithmetic_orbit_25_dvd_625 : (25 : ℕ) ∣ 625 := by decide

/-- **Lemma 22 arithmetic: orbit decomposition with smallest orbit = 25**. [done]

For `|X| = 625` acting with smallest orbit size 25 (so all orbits have
size in `{25, 125, 625}`), the orbit count equation `25·i + 125·j +
625·k = 3250` reduces to `i + 5·j + 25·k = 130` (with `i ≥ 1`).

The pure arithmetic form: given `i ≥ 1, j ≥ 0, k ≥ 0` with
`25·i + 125·j + 625·k = 3250`, the resulting `(i, j, k)` triple
satisfies `i + 5·j + 25·k = 130`. -/
theorem lem22_arithmetic_orbit_decomp_smallest_25
    (i j k : ℕ) (h_pos : 1 ≤ i)
    (h_sum : 25 * i + 125 * j + 625 * k = 3250) :
    i + 5 * j + 25 * k = 130 := by
  omega

/-- **Lemma 22 arithmetic: `5^k = 625 ↔ k = 4`.** [done]

The order-625 hypothesis pins the 5-group exponent uniquely as `5^4`. -/
theorem lem22_arithmetic_5group_eq_625_pow_four (k : ℕ) :
    5 ^ k = 625 ↔ k = 4 := by
  refine ⟨?_, fun h => h ▸ rfl⟩
  intro h
  have h_le : 5 ^ k ≤ 625 := h.le
  have h_ge : 625 ≤ 5 ^ k := h.ge
  have h_k_le : k ≤ 4 := by
    by_contra h_lt
    have h5 : 5 ≤ k := Nat.lt_of_not_le h_lt
    have : 5 ^ 5 ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) h5
    omega
  interval_cases k <;> omega

/-- **Lemma 22 arithmetic: 5-group with `|X| ∣ 625` enumeration.** [done]

For a 5-group `X` (`|X| = 5^k`), `|X| ∣ 625 = 5^4` forces
`|X| ∈ {1, 5, 25, 125, 625}`. -/
theorem lem22_arithmetic_5group_dvd_625_enumeration
    (k : ℕ) (h_dvd : 5 ^ k ∣ 625) :
    5 ^ k = 1 ∨ 5 ^ k = 5 ∨ 5 ^ k = 25 ∨ 5 ^ k = 125 ∨ 5 ^ k = 625 := by
  have h_le : 5 ^ k ≤ 625 := Nat.le_of_dvd (by norm_num) h_dvd
  have h_k_le : k ≤ 4 := by
    by_contra h
    have h5 : 5 ≤ k := Nat.lt_of_not_le h
    have : 5 ^ 5 ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) h5
    omega
  interval_cases k
  · left; rfl
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; left; rfl
  · right; right; right; right; rfl

/-- **Lemma 22 conditional + arithmetic (5-group, order 625).** [done]

If a single graph-automorphism σ has order a power of 5 (`σ^(5^k) = 1`)
and `orderOf σ ∣ 625`, then `orderOf σ ∈ {1, 5, 25, 125, 625}`. -/
theorem lem22_orderOf_in_625_divisors
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (h_dvd : orderOf σ ∣ 625) :
    orderOf σ = 1 ∨ orderOf σ = 5 ∨ orderOf σ = 25 ∨
    orderOf σ = 125 ∨ orderOf σ = 625 := by
  have h5k : orderOf σ ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one pow_pk
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp h5k with ⟨j, _hj, hord⟩
  rw [hord] at h_dvd ⊢
  exact lem22_arithmetic_5group_dvd_625_enumeration j h_dvd

/-- **Lemma 22 (`|X| = 625, smallest orbit 25` ⇒ `X = SmallGroup(625, 12)`).**
[GAP, skeleton]

Arithmetic backbone: orbit-stabilizer arithmetic
(`lem22_arithmetic_stabilizer_25`), divisibility helper
(`lem22_arithmetic_orbit_25_dvd_625`), orbit-decomposition
arithmetic (`lem22_arithmetic_orbit_decomp_smallest_25`), and the
5-group exponent / divisor enumeration
(`lem22_arithmetic_5group_eq_625_pow_four`,
`lem22_arithmetic_5group_dvd_625_enumeration`,
`lem22_orderOf_in_625_divisors`).

What remains is the GAP-dependent classification: among the groups
of order 625 (= 5^4), the unique one acting with smallest orbit
size 25 on Moore57 is `SmallGroup(625, 12)` of the GAP library. -/
theorem lem22_smallGroup_625_12 (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S8
