import Moore57.E7Minus8D19TraceInputComplementBoundary
import Moore57.D19OrbitContributionData

/-!
# Complementary minus-8 boundary from action concrete data

This file lifts the complementary `(-8)` route from `D19TraceInput h` to the
action concrete data records that already carry `traceInput : D19TraceInput h`.
All results are thin wrappers around the trace-input boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActionConcreteData

variable {h : D19ActsOnMoore57 V Γ}

/-- Concrete action data plus the standard reflection counts gives a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complement
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Concrete action data plus the standard reflection counts gives fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complement_raw_reflection
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplement_raw_reflection
    h data.traceInput reflection_fixed_count reflection_adjacent_moved k

/-- Concrete action data plus the standard reflection counts gives `K_{1,55}`
witnesses for all reflections through the complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complement_raw_reflection
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplement_raw_reflection
    h data.traceInput reflection_fixed_count reflection_adjacent_moved k

/-- Concrete action data plus the standard reflection counts gives the
fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complement
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Concrete action data plus the standard reflection counts gives the
representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complement
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Concrete action data plus the standard reflection counts rules out the
current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complement
    (data : D19ActionConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Concrete action data plus a fixed-star reflection input gives a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
    (data : D19ActionConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Concrete action data plus a fixed-star reflection input gives fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
    (data : D19ActionConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    h data.traceInput hStar k

/-- Concrete action data plus a fixed-star reflection input gives `K_{1,55}`
witnesses for all reflections through the complementary minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
    (data : D19ActionConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    h data.traceInput hStar k

/-- Concrete action data plus a fixed-star reflection input gives the
fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
    (data : D19ActionConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Concrete action data plus a fixed-star reflection input gives the
representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionStar
    (data : D19ActionConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Concrete action data plus a fixed-star reflection input rules out the
current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionStar
    (data : D19ActionConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

end D19ActionConcreteData

namespace D19ActionOrbitConcreteData

variable {h : D19ActsOnMoore57 V Γ}

/-- Orbit-generated concrete action data plus the standard reflection counts
gives a nonempty linear-character input through the complementary minus-8
route. -/
theorem nonempty_d19LinearCharacterInput_of_complement
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Orbit-generated concrete action data plus the standard reflection counts
gives fixed-star boundaries for all reflections through the complementary
minus-8 route. -/
theorem involutionFixedSetStar56_of_complement_raw_reflection
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplement_raw_reflection
    h data.traceInput reflection_fixed_count reflection_adjacent_moved k

/-- Orbit-generated concrete action data plus the standard reflection counts
gives `K_{1,55}` witnesses for all reflections through the complementary
minus-8 route. -/
theorem nonempty_involutionK155_of_complement_raw_reflection
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplement_raw_reflection
    h data.traceInput reflection_fixed_count reflection_adjacent_moved k

/-- Orbit-generated concrete action data plus the standard reflection counts
gives the fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complement
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Orbit-generated concrete action data plus the standard reflection counts
gives the representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complement
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Orbit-generated concrete action data plus the standard reflection counts
rules out the current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complement
    (data : D19ActionOrbitConcreteData h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplement
    h data.traceInput reflection_fixed_count reflection_adjacent_moved

/-- Orbit-generated concrete action data plus a fixed-star reflection input
gives a nonempty linear-character input through the complementary minus-8
route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
    (data : D19ActionOrbitConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Orbit-generated concrete action data plus a fixed-star reflection input
gives fixed-star boundaries for all reflections through the complementary
minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
    (data : D19ActionOrbitConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    h data.traceInput hStar k

/-- Orbit-generated concrete action data plus a fixed-star reflection input
gives `K_{1,55}` witnesses for all reflections through the complementary
minus-8 route. -/
theorem nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
    (data : D19ActionOrbitConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    h data.traceInput hStar k

/-- Orbit-generated concrete action data plus a fixed-star reflection input
gives the fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
    (data : D19ActionOrbitConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Orbit-generated concrete action data plus a fixed-star reflection input
gives the representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionStar
    (data : D19ActionOrbitConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Orbit-generated concrete action data plus a fixed-star reflection input
rules out the current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionStar
    (data : D19ActionOrbitConcreteData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

end D19ActionOrbitConcreteData

namespace D19OrbitContributionData

variable {h : D19ActsOnMoore57 V Γ}

/-- Orbit contribution data plus a fixed-star reflection input gives a
nonempty linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
    (data : D19OrbitContributionData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Orbit contribution data plus a fixed-star reflection input gives fixed-star
boundaries for all reflections through the complementary minus-8 route. -/
theorem involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
    (data : D19OrbitContributionData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    h data.traceInput hStar k

/-- Orbit contribution data plus a fixed-star reflection input gives
`K_{1,55}` witnesses for all reflections through the complementary minus-8
route. -/
theorem nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
    (data : D19OrbitContributionData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    h data.traceInput hStar k

/-- Orbit contribution data plus a fixed-star reflection input gives the
fixed-center leaf boundary through the complementary minus-8 route. -/
theorem reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
    (data : D19OrbitContributionData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Orbit contribution data plus a fixed-star reflection input gives the
representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_complementAndReflectionStar
    (data : D19OrbitContributionData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

/-- Orbit contribution data plus a fixed-star reflection input rules out the
current branch-orbit final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_complementAndReflectionStar
    (data : D19OrbitContributionData h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionStar
    h data.traceInput hStar

end D19OrbitContributionData

end

end Moore57
