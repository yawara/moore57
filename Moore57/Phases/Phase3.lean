import Moore57.Phases.Phase1

/-!
# Phase 3 prebuilt: reflection 7-eigenspace character value

The natural-language Lemma 9.3 gives `χ₇(t) = 33` for any reflection `t`:
from the Higman trace formula and the reflection counts `a₀ = 56`, `a₁ = 112`,

  χ₇(t) = (8·56 + 112 − 65) / 15 = 495 / 15 = 33.

Phase 3.1 (`a₀ = 56`, `a₁ = 112`) is already exposed in `PhaseOnePrebuilt`.
This file adds Phase 3.2.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Phase 3.2: every reflection has 7-eigenspace character value `33`.

Derived from the Higman trace formula evaluated at the reflection, using the
raw-action consequences `a₀(t) = 56` and `a₁(t) = 112`. -/
theorem reflection_E7_trace_eq_thirtyThree
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
      (33 : ℚ) := by
  rw [h.isMoore.higman_trace_formula (h.smulEquiv (DihedralGroup.sr k))]
  rw [h.reflection_fixedVertexCount_eq_fiftySix k,
    h.reflection_adjacentMovedCount_eq_oneHundredTwelve k]
  norm_num

end D19ActsOnMoore57

end Moore57
