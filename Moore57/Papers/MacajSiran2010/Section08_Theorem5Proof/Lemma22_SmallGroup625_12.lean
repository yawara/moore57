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

/-- **Lemma 22 (`|X| = 625, smallest orbit 25` ⇒ `X = SmallGroup(625, 12)`).**
[GAP, skeleton]

Arithmetic backbone: orbit-stabilizer arithmetic
(`lem22_arithmetic_stabilizer_25`), divisibility helper
(`lem22_arithmetic_orbit_25_dvd_625`), and orbit-decomposition
arithmetic (`lem22_arithmetic_orbit_decomp_smallest_25`).

What remains is the GAP-dependent classification: among the groups
of order 625 (= 5^4), the unique one acting with smallest orbit
size 25 on Moore57 is `SmallGroup(625, 12)` of the GAP library. -/
theorem lem22_smallGroup_625_12 (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S8
