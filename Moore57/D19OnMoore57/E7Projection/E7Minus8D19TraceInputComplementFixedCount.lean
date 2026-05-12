import Moore57.D19OnMoore57.E7Projection.E7Minus8D19TraceInputComplementBoundary
import Moore57.D19OnMoore57.Fixed.FixedInducedStrongStarBridge

/-!
# Complementary minus-8 route from reflection fixed count only

The complementary `D19TraceInput` route previously accepted both the reflection
fixed count `56` and the adjacent-moved count `112`.  The fixed count already
implies the paper-shaped fixed-star statement for a raw reflection, and that
paper statement supplies the adjacent-moved count.  This file records the
smaller input surface.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the packaged E7/minus-8 boundary from `D19TraceInput h` and only
the fixed count `56` for the standard reflection representative.  The
adjacent-moved count is derived via the paper-shaped fixed-star bridge. -/
def ofD19TraceInputComplementAndReflectionFixedCount
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19TraceInputComplementAndReflectionStar h traceInput
    (h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56
      0 reflection_fixed_count)

end E7Minus8CharacterReflectionCountBoundary

/-- `D19TraceInput` plus the standard reflection fixed count gives a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionFixedCount
    h traceInput
      reflection_fixed_count)
      |>.nonempty_d19LinearCharacterInput

/-- The fixed-count-only complementary route gives the paper-shaped fixed-star
boundary for any reflection. -/
theorem involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionFixedCount
    h traceInput
      reflection_fixed_count)
      |>.involutionFixedSetStar56_raw_reflection k

/-- The fixed-count-only complementary route gives a nonempty `K_{1,55}`
witness for any reflection. -/
theorem nonempty_involutionK155_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionFixedCount
    h traceInput
      reflection_fixed_count)
      |>.nonempty_involutionK155_raw_reflection k

/-- The fixed-count-only complementary route gives the fixed-center leaf
boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionFixedCount
    h traceInput
      reflection_fixed_count)
      |>.reflectionFixedCenterLeafBoundary

/-- The fixed-count-only complementary route gives the representation
character component boundary. -/
theorem representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionFixedCount
    h traceInput
      reflection_fixed_count)
      |>.representationCharacterComponentsBoundary

/-- The fixed-count-only complementary route rules out the current final-gap
boundary. -/
theorem no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionFixedCount
    h traceInput
      reflection_fixed_count)
      |>.no_currentFinalGapBoundary

end D19ActsOnMoore57

end

end Moore57
