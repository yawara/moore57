import Moore57.ReflectionRegularBranchExclusion

/-!
# Raw-reflection fixed-star connectors for D19 linear-character inputs

This file records thin wrappers around
`D19LinearCharacterInput.involutionFixedSetStar56_of_raw_reflection`, exposing
the existing downstream `K_{1,55}` and count inputs.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace D19LinearCharacterInput

/-- Raw-reflection bridge to the explicit downstream `K_{1,55}` input. -/
theorem nonempty_involutionK155_of_raw_reflection
    (hin : D19LinearCharacterInput h) (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (hin.involutionFixedSetStar56_of_raw_reflection k).nonempty_involutionK155

/-- Raw-reflection bridge to the fixed-point count input. -/
theorem fixedVertexCount_reflection_eq_56_of_raw_reflection
    (hin : D19LinearCharacterInput h) (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
  (hin.involutionFixedSetStar56_of_raw_reflection k).fixedVertexCount_eq_56

/-- Raw-reflection bridge to the adjacent-moved count input. -/
theorem adjacentMovedCount_reflection_eq_112_of_raw_reflection
    (hin : D19LinearCharacterInput h) (k : ZMod 19) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 112 :=
  (hin.involutionFixedSetStar56_of_raw_reflection k).adjacentMovedCount_eq_112
    h.isMoore

/-- Raw-reflection bridge to the weaker fixed-star count abstraction. -/
theorem nonempty_involutionFixedStar55_of_raw_reflection
    (hin : D19LinearCharacterInput h) (k : ZMod 19) :
    Nonempty (InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (hin.involutionFixedSetStar56_of_raw_reflection k).nonempty_involutionFixedStar55
    h.isMoore

end D19LinearCharacterInput

end D19ActsOnMoore57

end

end Moore57
