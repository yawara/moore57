import Moore57.D19OnMoore57.E7Projection.E7Minus8TraceRepresentationComplementNoGoConnectors
import Moore57.D19OnMoore57.Fixed.FixedInducedStrongStarBridge

/-!
# Complementary trace-representation route from reflection fixed count only

The complementary `TraceRepresentationData` route previously accepted both the
standard reflection fixed count `56` and the adjacent-moved count `112`.  The
fixed count gives the paper-shaped fixed-star statement for `sr 0`, and that
statement supplies the adjacent-moved count consumed by the existing package.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the packaged E7/minus-8 boundary from complementary
`TraceRepresentationData h.a1` and only the fixed count `56` for the standard
reflection representative. -/
def ofTraceRepresentationDataComplementAndReflectionFixedCount
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    E7Minus8CharacterReflectionCountBoundary h :=
  let hStar :=
    h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56
      0 reflection_fixed_count
  ofTraceRepresentationDataComplement h data rotation_fixed reflection_fixed_count
    (hStar.adjacentMovedCount_eq_112 h.isMoore)

end E7Minus8CharacterReflectionCountBoundary

/-- Complementary trace-representation data plus the standard reflection fixed
count gives a nonempty linear-character input. -/
theorem nonempty_d19LinearCharacterInput_of_traceRepresentationDataComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplementAndReflectionFixedCount
    h data rotation_fixed reflection_fixed_count)
      |>.nonempty_d19LinearCharacterInput

/-- The fixed-count-only complementary trace-representation route gives the
paper-shaped fixed-star boundary for any reflection. -/
theorem involutionFixedSetStar56_of_traceRepresentationDataComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplementAndReflectionFixedCount
    h data rotation_fixed reflection_fixed_count)
      |>.involutionFixedSetStar56_raw_reflection k

/-- The fixed-count-only complementary trace-representation route gives a
`K_{1,55}` witness for any reflection. -/
theorem nonempty_involutionK155_of_traceRepresentationDataComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplementAndReflectionFixedCount
    h data rotation_fixed reflection_fixed_count)
      |>.nonempty_involutionK155_raw_reflection k

/-- The fixed-count-only complementary trace-representation route gives the
fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_traceRepresentationDataComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplementAndReflectionFixedCount
    h data rotation_fixed reflection_fixed_count)
      |>.reflectionFixedCenterLeafBoundary

/-- The fixed-count-only complementary trace-representation route gives the
representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_traceRepresentationDataComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplementAndReflectionFixedCount
    h data rotation_fixed reflection_fixed_count)
      |>.representationCharacterComponentsBoundary

/-- The fixed-count-only complementary trace-representation route rules out the
current final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_traceRepresentationDataComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplementAndReflectionFixedCount
    h data rotation_fixed reflection_fixed_count)
      |>.no_currentFinalGapBoundary

end D19ActsOnMoore57

end

end Moore57
