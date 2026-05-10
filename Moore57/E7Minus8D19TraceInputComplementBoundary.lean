import Moore57.E7Minus8TraceRepresentationComplementBoundary

/-!
# D19 trace input plus complementary minus-8 boundary

This file lifts the concrete complementary `(-8)` bridge from
`TraceRepresentationData h.a1` to `D19TraceInput h`.  The trace input supplies
both the trace-representation data and the nontrivial rotation fixed-count
input; the remaining assumptions are the standard reflection representative
counts, or equivalently the fixed-star boundary at `sr 0`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the packaged E7/minus-8 boundary from `D19TraceInput h`, using the
complementary minus-8 projection formula and the standard reflection
representative counts. -/
def ofD19TraceInputComplement
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationDataComplement h
    traceInput.toTraceRepresentationData
    traceInput.fixed.rotation_fixed
    reflection_fixed_count reflection_adjacent_moved

/-- Fixed-star variant of `ofD19TraceInputComplement`. -/
def ofD19TraceInputComplementAndReflectionStar
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19TraceInputComplement h traceInput
    hStar.fixedVertexCount_eq_56
    (hStar.adjacentMovedCount_eq_112 h.isMoore)

end E7Minus8CharacterReflectionCountBoundary

/-- `D19TraceInput` plus the standard reflection counts gives a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_d19TraceInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement h
    traceInput reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_d19LinearCharacterInput

/-- The complementary `D19TraceInput` route gives the paper-shaped fixed-star
boundary for any reflection. -/
theorem involutionFixedSetStar56_of_d19TraceInputComplement_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement h
    traceInput reflection_fixed_count reflection_adjacent_moved)
      |>.involutionFixedSetStar56_raw_reflection k

/-- The complementary `D19TraceInput` route gives a nonempty `K_{1,55}` witness
for any reflection. -/
theorem nonempty_involutionK155_of_d19TraceInputComplement_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement h
    traceInput reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_involutionK155_raw_reflection k

/-- The complementary `D19TraceInput` route gives the fixed-center leaf
boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_d19TraceInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement h
    traceInput reflection_fixed_count reflection_adjacent_moved)
      |>.reflectionFixedCenterLeafBoundary

/-- The complementary `D19TraceInput` route gives the representation character
component boundary. -/
theorem representationCharacterComponentsBoundary_of_d19TraceInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement h
    traceInput reflection_fixed_count reflection_adjacent_moved)
      |>.representationCharacterComponentsBoundary

/-- The complementary `D19TraceInput` route rules out the current final-gap
boundary. -/
theorem no_currentFinalGapBoundary_of_d19TraceInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement h
    traceInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_currentFinalGapBoundary

/-- Fixed-star input variant of
`nonempty_d19LinearCharacterInput_of_d19TraceInputComplement`. -/
theorem nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionStar
    h traceInput hStar)
      |>.nonempty_d19LinearCharacterInput

/-- Fixed-star input variant of
`involutionFixedSetStar56_of_d19TraceInputComplement_raw_reflection`. -/
theorem involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionStar
    h traceInput hStar)
      |>.involutionFixedSetStar56_raw_reflection k

/-- Fixed-star input variant of
`nonempty_involutionK155_of_d19TraceInputComplement_raw_reflection`. -/
theorem nonempty_involutionK155_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionStar
    h traceInput hStar)
      |>.nonempty_involutionK155_raw_reflection k

/-- Fixed-star input variant of
`reflectionFixedCenterLeafBoundary_of_d19TraceInputComplement`. -/
theorem reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionStar
    h traceInput hStar)
      |>.reflectionFixedCenterLeafBoundary

/-- Fixed-star input variant of
`representationCharacterComponentsBoundary_of_d19TraceInputComplement`. -/
theorem representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionStar
    h traceInput hStar)
      |>.representationCharacterComponentsBoundary

/-- Fixed-star input variant of
`no_currentFinalGapBoundary_of_d19TraceInputComplement`. -/
theorem no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionStar
    h traceInput hStar)
      |>.no_currentFinalGapBoundary

end D19ActsOnMoore57

end

end Moore57
