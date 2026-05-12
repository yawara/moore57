import Moore57.D19OnMoore57.E7Projection.Minus8TraceRepresentationComplementFixedCount
import Moore57.D19OnMoore57.Reflection.TraceThirtyThreeFixedCount

/-!
# Complementary boundary from E7 reflection trace value `33`

This file replaces the standard reflection fixed-count input in the direct
trace-representation complement route by the more representation-theoretic
input that every reflection has E7 trace value `33`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the packaged E7/minus-8 boundary from trace-core character data and
the reflection-side E7 trace value `33`.  The raw action supplies the rotation
fixed-count data, while `trace = 33` supplies the reflection fixed count `56`. -/
def ofTraceCoreCharacterBoundaryComplementAndE7ReflectionTraceThirtyThree
    (traceCore : TraceCoreCharacterBoundary h)
    (htrace33 :
      ∀ k : ZMod 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
          (33 : ℚ)) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationDataComplementAndReflectionFixedCount h
    traceCore.toTraceRepresentationData
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)
    (h.fixedVertexCount_reflection_eq_56_of_E7_trace_eq_33 0 (htrace33 0))

/-- Prop-valued component boundary variant of
`ofTraceCoreCharacterBoundaryComplementAndE7ReflectionTraceThirtyThree`. -/
def ofRepresentationCharacterComponentsBoundaryComplementAndE7ReflectionTraceThirtyThree
    (components : RepresentationCharacterComponentsBoundary h)
    (htrace33 :
      ∀ k : ZMod 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
          (33 : ℚ)) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationDataComplementAndReflectionFixedCount h
    components.toTraceRepresentationData
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)
    (h.fixedVertexCount_reflection_eq_56_of_E7_trace_eq_33 0 (htrace33 0))

end E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Trace-core character data plus the reflection-side E7 trace value `33`
gives a nonempty linear-character input through the complementary route. -/
theorem nonempty_d19LinearCharacterInput_of_traceCoreComplementAndE7ReflectionTraceThirtyThree
    (traceCore : TraceCoreCharacterBoundary h)
    (htrace33 :
      ∀ k : ZMod 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
          (33 : ℚ)) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceCoreCharacterBoundaryComplementAndE7ReflectionTraceThirtyThree
      h traceCore htrace33)
      |>.nonempty_d19LinearCharacterInput

/-- Trace-core character data plus reflection trace `33` gives fixed-star
boundaries for all reflections through the complementary route. -/
theorem involutionFixedSetStar56_of_traceCoreComplementAndE7ReflectionTraceThirtyThree
    (traceCore : TraceCoreCharacterBoundary h)
    (htrace33 :
      ∀ k : ZMod 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
          (33 : ℚ))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceCoreCharacterBoundaryComplementAndE7ReflectionTraceThirtyThree
      h traceCore htrace33)
      |>.involutionFixedSetStar56_raw_reflection k

/-- Trace-core character data plus reflection trace `33` rules out the current
final-gap boundary through the complementary route. -/
theorem no_currentFinalGapBoundary_of_traceCoreComplementAndE7ReflectionTraceThirtyThree
    (traceCore : TraceCoreCharacterBoundary h)
    (htrace33 :
      ∀ k : ZMod 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
          (33 : ℚ)) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceCoreCharacterBoundaryComplementAndE7ReflectionTraceThirtyThree
      h traceCore htrace33)
      |>.no_currentFinalGapBoundary

/-- Component-boundary plus reflection trace `33` rules out the current final
gap through the complementary route. -/
theorem no_currentFinalGapBoundary_of_componentsComplementAndE7ReflectionTraceThirtyThree
    (components : RepresentationCharacterComponentsBoundary h)
    (htrace33 :
      ∀ k : ZMod 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
          (33 : ℚ)) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofRepresentationCharacterComponentsBoundaryComplementAndE7ReflectionTraceThirtyThree
      h components htrace33)
      |>.no_currentFinalGapBoundary

end D19ActsOnMoore57

end

end Moore57
