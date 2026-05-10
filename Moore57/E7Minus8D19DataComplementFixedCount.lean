import Moore57.E7Minus8D19TraceInputComplementFixedCount
import Moore57.E7Minus8D19GeometricInputComplementBoundary
import Moore57.E7Minus8D19ActionDataComplementBoundary

/-!
# Fixed-count-only complementary minus-8 route from data packages

This file lifts the fixed-count-only `D19TraceInput` complementary route to the
action, orbit, reduced, and geometric data records.  All proofs are thin
wrappers through `data.traceInput` or `data.characterInput.toD19TraceInput`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActionConcreteData

variable {h : D19ActsOnMoore57 V Γ}

/-- Concrete action data plus the standard reflection fixed count gives a
nonempty linear-character input through the fixed-count-only complementary
minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionFixedCount
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Concrete action data plus the standard reflection fixed count gives
fixed-star boundaries for all reflections through the fixed-count-only
complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.traceInput reflection_fixed_count k

/-- Concrete action data plus the standard reflection fixed count gives
`K_{1,55}` witnesses for all reflections through the fixed-count-only
complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.traceInput reflection_fixed_count k

/-- Concrete action data plus the standard reflection fixed count gives the
fixed-center leaf boundary through the fixed-count-only complementary minus-8
route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionFixedCount
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Concrete action data plus the standard reflection fixed count gives the
representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionFixedCount
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Concrete action data plus the standard reflection fixed count rules out
the current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionFixedCount
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

end D19ActionConcreteData

namespace D19ActionOrbitConcreteData

variable {h : D19ActsOnMoore57 V Γ}

/-- Orbit-generated concrete action data plus the standard reflection fixed
count gives a nonempty linear-character input through the fixed-count-only
complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionFixedCount
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Orbit-generated concrete action data plus the standard reflection fixed
count gives fixed-star boundaries for all reflections through the
fixed-count-only complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.traceInput reflection_fixed_count k

/-- Orbit-generated concrete action data plus the standard reflection fixed
count gives `K_{1,55}` witnesses for all reflections through the
fixed-count-only complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.traceInput reflection_fixed_count k

/-- Orbit-generated concrete action data plus the standard reflection fixed
count gives the fixed-center leaf boundary through the fixed-count-only
complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionFixedCount
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Orbit-generated concrete action data plus the standard reflection fixed
count gives the representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionFixedCount
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Orbit-generated concrete action data plus the standard reflection fixed
count rules out the current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionFixedCount
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

end D19ActionOrbitConcreteData

namespace D19OrbitContributionData

variable {h : D19ActsOnMoore57 V Γ}

/-- Orbit contribution data plus the standard reflection fixed count gives a
nonempty linear-character input through the fixed-count-only complementary
minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionFixedCount
    (data : D19OrbitContributionData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Orbit contribution data plus the standard reflection fixed count gives
fixed-star boundaries for all reflections through the fixed-count-only
complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19OrbitContributionData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.traceInput reflection_fixed_count k

/-- Orbit contribution data plus the standard reflection fixed count gives
`K_{1,55}` witnesses for all reflections through the fixed-count-only
complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19OrbitContributionData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.traceInput reflection_fixed_count k

/-- Orbit contribution data plus the standard reflection fixed count gives the
fixed-center leaf boundary through the fixed-count-only complementary minus-8
route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionFixedCount
    (data : D19OrbitContributionData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Orbit contribution data plus the standard reflection fixed count gives the
representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionFixedCount
    (data : D19OrbitContributionData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

/-- Orbit contribution data plus the standard reflection fixed count rules out
the current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionFixedCount
    (data : D19OrbitContributionData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.traceInput reflection_fixed_count

end D19OrbitContributionData

namespace D19ReducedHypotheses

variable {h : D19ActsOnMoore57 V Γ}

/-- Reduced hypotheses plus the standard reflection fixed count give a
nonempty linear-character input through the fixed-count-only complementary
minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionFixedCount
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionFixedCount
    h data.characterInput.toD19TraceInput reflection_fixed_count

/-- Reduced hypotheses plus the standard reflection fixed count give fixed-star
boundaries for all reflections through the fixed-count-only complementary
minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.characterInput.toD19TraceInput reflection_fixed_count k

/-- Reduced hypotheses plus the standard reflection fixed count give
`K_{1,55}` witnesses for all reflections through the fixed-count-only
complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    h data.characterInput.toD19TraceInput reflection_fixed_count k

/-- Reduced hypotheses plus the standard reflection fixed count give the
fixed-center leaf boundary through the fixed-count-only complementary minus-8
route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionFixedCount
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.characterInput.toD19TraceInput reflection_fixed_count

/-- Reduced hypotheses plus the standard reflection fixed count give the
representation character component boundary through the fixed-count-only
complementary minus-8 route. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionFixedCount
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.characterInput.toD19TraceInput reflection_fixed_count

/-- Reduced hypotheses plus the standard reflection fixed count rule out the
current final-gap boundary through the fixed-count-only complementary minus-8
route. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionFixedCount
    (data : D19ReducedHypotheses h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    h data.characterInput.toD19TraceInput reflection_fixed_count

end D19ReducedHypotheses

namespace D19GeometricInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Geometric inputs plus the standard reflection fixed count give a nonempty
linear-character input through the fixed-count-only complementary minus-8
route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionFixedCount
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ReducedHypotheses.nonempty_d19LinearCharacterInput_of_complementAndReflectionFixedCount
    data.toD19ReducedHypotheses reflection_fixed_count

/-- Geometric inputs plus the standard reflection fixed count give fixed-star
boundaries for all reflections through the fixed-count-only complementary
minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ReducedHypotheses.involutionFixedSetStar56_of_complementAndReflectionFixedCount_raw_reflection
    data.toD19ReducedHypotheses reflection_fixed_count k

/-- Geometric inputs plus the standard reflection fixed count give `K_{1,55}`
witnesses for all reflections through the fixed-count-only complementary
minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionFixedCount_raw_reflection
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ReducedHypotheses.nonempty_involutionK155_of_complementAndReflectionFixedCount_raw_reflection
    data.toD19ReducedHypotheses reflection_fixed_count k

/-- Geometric inputs plus the standard reflection fixed count give the
fixed-center leaf boundary through the fixed-count-only complementary minus-8
route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionFixedCount
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ReducedHypotheses.reflectionFixedCenterLeafBoundary_of_complementAndReflectionFixedCount
    data.toD19ReducedHypotheses reflection_fixed_count

/-- Geometric inputs plus the standard reflection fixed count give the
representation character component boundary through the fixed-count-only
complementary minus-8 route. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionFixedCount
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ReducedHypotheses.representationCharacterComponentsBoundary_of_complementAndReflectionFixedCount
    data.toD19ReducedHypotheses reflection_fixed_count

/-- Geometric inputs plus the standard reflection fixed count rule out the
current final-gap boundary through the fixed-count-only complementary minus-8
route. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionFixedCount
    (data : D19GeometricInputs h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ReducedHypotheses.no_currentFinalGapBoundary_of_complementAndReflectionFixedCount
    data.toD19ReducedHypotheses reflection_fixed_count

end D19GeometricInputs

end

end Moore57
