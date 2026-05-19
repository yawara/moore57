import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma18_5Group
import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Lemma5_AdjacencyMatrix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §8, Proposition 3 [deferred-heavy]

> Let `X` be a group of automorphisms of a Moore (57, 2)-graph Γ of order
> a power of 5. If `Fix(X)` is the Hoffman–Singleton graph, then `|X| ≤ 5`.

Proof outline (paper §8):
1. Assume `|X| = 25`. Then `X` acts semi-regularly on `Γ \ Fix(X)`,
   yielding 50 size-1 + 128 size-25 orbits.
2. Two orbits of size 25 lie in the neighbourhood of each fixed point,
   both with trace 0. The trace of `X` is congruent to `6 mod 15` and at
   most 56, so at least one of the remaining 28 orbits has trace 0.
3. Pick `O₁₇₈` an orbit with zero trace. Analyse the entry
   `Σⱼ b²_{178,j}` in `B² + B − 56 I = 1ᵀ s`.
4. Derive the simultaneous equations
   `Σ b_{178,i} = 7` and `Σ b²_{178,i} = 31` (for `i ∈ {151..177}`).
5. No non-negative integer solution exists — contradiction.
-/

namespace Moore57.Papers.MacajSiran2010.S8

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Proposition 3 arithmetic core: no partition of 7 has square-sum 31.**
[done]

For non-negative integers `x_0, ..., x_7` where `x_k` is the count of
parts equal to `k`, the simultaneous constraints

  `1·x_1 + 2·x_2 + 3·x_3 + 4·x_4 + 5·x_5 + 6·x_6 + 7·x_7 = 7`
  `1·x_1 + 4·x_2 + 9·x_3 + 16·x_4 + 25·x_5 + 36·x_6 + 49·x_7 = 31`

have no solution.

This is the §8 Prop 3 arithmetic core (step 5 of the paper proof):
the simultaneous equations
  `Σⱼ b_{178,j} = 7` and `Σⱼ b²_{178,j} = 31` (for the 27 orbits
`j ∈ {151..177}`) have no non-negative integer solution.

The proof packages the multiset of `b_{178,j}` values via their
value-counts `x_k = |{j : b_{178,j} = k}|`.  omega handles the
non-existence directly. -/
theorem prop3_arithmetic_core_no_partition_of_7_with_sq_31
    (x1 x2 x3 x4 x5 x6 x7 : ℕ)
    (h_sum : x1 + 2 * x2 + 3 * x3 + 4 * x4 + 5 * x5 + 6 * x6 + 7 * x7 = 7)
    (h_sq_sum :
      x1 + 4 * x2 + 9 * x3 + 16 * x4 + 25 * x5 + 36 * x6 + 49 * x7 = 31) :
    False := by
  -- Bound each x_i: x_i = 0 forced for i ≥ 4 except small cases.
  have hx7 : x7 = 0 := by omega
  have hx6 : x6 = 0 := by omega
  have hx5 : x5 ≤ 1 := by omega
  have hx4 : x4 ≤ 1 := by omega
  have hx3 : x3 ≤ 2 := by omega
  have hx2 : x2 ≤ 3 := by omega
  subst hx7
  subst hx6
  interval_cases x5 <;> interval_cases x4 <;>
    interval_cases x3 <;> interval_cases x2 <;> omega

/-- **Proposition 3 (Hoffman–Singleton-fix 5-group `|X| ≤ 5`).** [deferred-heavy] -/
theorem prop3_hs_fix_bound (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S8
