import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma20_ConjugateFix

/-!
# Orbit decomposition arithmetic for `p`-groups acting on Moore-style sets

Self-contained arithmetic helpers used in Mačaj–Širáň 2010 §7 (Theorem 4)
and §8 (Theorem 5) to constrain the orbit-size multiset of a small
`p`-group acting on a neighbourhood of `Γ`.

These results are *purely combinatorial*: they take the orbit-size
constraints (e.g., "no size-9 orbits", "at most one size-3 orbit") as
hypotheses and derive the forced orbit counts.  The hypotheses themselves
come from Mačaj–Širáň Lemma 21 (for the 3-group case) which is in turn
based on the Petersen/singleton dichotomy of Lemma 17 (still open).

## Main result

* `orbit_count_81_on_57` — for a 3-group of order `81` acting on `N(a)`
  (57 vertices) with no size-9 orbits, no size-81 orbits, no fixed
  points, and at most one size-3 orbit, the orbit-size multiset
  necessarily consists of one size-3 orbit and two size-27 orbits.
-/

namespace Moore57.Foundations.GroupTheory

/-- **Orbit count for a 3-group of order 81 on a 57-set.**

If `b` size-3 orbits and `d` size-27 orbits partition a 57-set (i.e.,
`3·b + 27·d = 57`), and `b ≤ 1`, then necessarily `b = 1` and `d = 2`.

In the Mačaj–Širáň 2010 §7 context, this is the orbit decomposition of
a 3-group `X` of order 81 acting on `N(a)` (Mačaj–Širáň's "1 orbit of
size 3 and 2 orbits of size 27" claim).  The constraints come from
Lemma 21:

* No size-9 orbit (Lemma 21 (2)).
* No size-81 orbit (since `81 > 57`).
* No size-1 orbit (since `Fix(X) = {a}` and `a ∉ N(a)`).
* At most one size-3 orbit (Lemma 21 (1) — two would force `|X| = 9`).

Under these constraints, the only orbit sizes available are `{3, 27}`,
and the multiset is fully determined by `(b, d) = (1, 2)`. -/
theorem orbit_count_81_on_57 (b d : ℕ)
    (h_sum : 3 * b + 27 * d = 57) (h_b : b ≤ 1) :
    b = 1 ∧ d = 2 := by
  omega

/-- **Variant**: the same statement without the `b ≤ 1` hypothesis fails.
This records that the constraint `b ≤ 1` is actually necessary: without
it, `(b, d) = (19, 0)` (nineteen size-3 orbits) is also a solution. -/
example : 3 * 19 + 27 * 0 = 57 := by decide

/-! ## Class size from Lemma 20

The Mačaj–Širáň "class size = 9" step in Corollary 2 follows from
Lemma 20 once one knows `|orbit| = 27` and `|Fix(stab) ∩ orbit| = 3`.
The latter equality is the geometric input from Lemma 17 — not proven
here, taken as a hypothesis. -/

open MulAction Subgroup

/-- **Mačaj–Širáň 2010 §7, Cor 2 (class-size step).**

For any `MulAction G α` and `o : α`, if the orbit of `o` has size `27`
and the `(stab o)`-fixed points in that orbit number `3`
(converted by Lemma 20 to `[N_G(stab o) : stab o] = 3`), then `stab o`
has exactly `9` conjugates in `G`.

This is the direct application of Lemma 20 once the geometric inputs
are available; in the §7 context these inputs are supplied by Lemma 17
(`Fix(stab o)` is the Petersen graph, intersecting each size-`27` orbit
in 3 points). -/
theorem class_size_9_of_orbit_27_fix_3
    {G α : Type*} [Group G] [MulAction G α] (o : α)
    [Finite (stabilizer G o : Set G)]
    (h_orbit : (orbit G o).ncard = 27)
    (h_fix : (fixedPoints (stabilizer G o) α ∩ orbit G o).ncard = 3) :
    (Subgroup.normalizer (stabilizer G o : Set G)).index = 9 := by
  have h_relIndex : (stabilizer G o).relIndex
      (Subgroup.normalizer (stabilizer G o : Set G)) = 3 := by
    rw [← Moore57.Papers.MacajSiran2010.S6.ncard_fixedPoints_inter_orbit_eq_relIndex_normalizer
      (G := G) (α := α) o]
    exact h_fix
  have h := Moore57.Papers.MacajSiran2010.S6.lem20_fix_conjugate (G := G) o
  rw [h_orbit, h_relIndex] at h
  omega

end Moore57.Foundations.GroupTheory
