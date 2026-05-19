import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma18_5Group
import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Lemma5_AdjacencyMatrix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §8, Proposition 3 [skeleton]

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

/-- **Proposition 3 (Hoffman–Singleton-fix 5-group `|X| ≤ 5`).** [skeleton] -/
theorem prop3_hs_fix_bound (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S8
