import Moore57.E7Minus8TraceRepresentationPackageBridge

/-!
# Direct consequences of trace-representation E7/minus-8 data

This file keeps the `TraceRepresentationData h.a1` surface thin: build the
packaged E7/minus-8 character boundary, then expose the standard downstream
linear-character, fixed-star, `K_{1,55}`, component, and current-gap
consequences.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Trace-representation E7 data plus minus-8 value data and the standard
count inputs give a nonempty linear-character input. -/
theorem nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationData h
    data A B C minus8Values rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_d19LinearCharacterInput

/-- Trace-representation E7 data plus minus-8 value data and the standard
count inputs give the paper-shaped fixed-star boundary for any reflection. -/
theorem involutionFixedSetStar56_of_traceRepresentationDataAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationData h
    data A B C minus8Values rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.involutionFixedSetStar56_raw_reflection k

/-- Trace-representation E7 data plus minus-8 value data and the standard
count inputs give a nonempty `K_{1,55}` witness for any reflection. -/
theorem nonempty_involutionK155_of_traceRepresentationDataAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationData h
    data A B C minus8Values rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_involutionK155_raw_reflection k

/-- Trace-representation E7 data plus minus-8 value data and the standard
count inputs give the fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_traceRepresentationDataAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationData h
    data A B C minus8Values rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.reflectionFixedCenterLeafBoundary

/-- Trace-representation E7 data plus minus-8 value data and the standard
count inputs give the representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_traceRepresentationDataAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationData h
    data A B C minus8Values rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.representationCharacterComponentsBoundary

/-- Trace-representation E7 data plus minus-8 value data and the standard
count inputs rule out the current final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_traceRepresentationDataAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationData h
    data A B C minus8Values rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.no_currentFinalGapBoundary

/-- Fixed-star input variant of
`nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8Values`.
-/
theorem nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndReflectionStar
    h data A B C minus8Values rotation_fixed hStar)
      |>.nonempty_d19LinearCharacterInput

/-- Fixed-star input variant of
`involutionFixedSetStar56_of_traceRepresentationDataAndMinus8Values`. -/
theorem involutionFixedSetStar56_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndReflectionStar
    h data A B C minus8Values rotation_fixed hStar)
      |>.involutionFixedSetStar56_raw_reflection k

/-- Fixed-star input variant of
`nonempty_involutionK155_of_traceRepresentationDataAndMinus8Values`. -/
theorem nonempty_involutionK155_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndReflectionStar
    h data A B C minus8Values rotation_fixed hStar)
      |>.nonempty_involutionK155_raw_reflection k

/-- Fixed-star input variant of
`reflectionFixedCenterLeafBoundary_of_traceRepresentationDataAndMinus8Values`.
-/
theorem reflectionFixedCenterLeafBoundary_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndReflectionStar
    h data A B C minus8Values rotation_fixed hStar)
      |>.reflectionFixedCenterLeafBoundary

/-- Fixed-star input variant of
`representationCharacterComponentsBoundary_of_traceRepresentationDataAndMinus8Values`.
-/
theorem representationCharacterComponentsBoundary_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndReflectionStar
    h data A B C minus8Values rotation_fixed hStar)
      |>.representationCharacterComponentsBoundary

/-- Fixed-star input variant of
`no_currentFinalGapBoundary_of_traceRepresentationDataAndMinus8Values`. -/
theorem no_currentFinalGapBoundary_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndReflectionStar
    h data A B C minus8Values rotation_fixed hStar)
      |>.no_currentFinalGapBoundary

end D19ActsOnMoore57

end

end Moore57
