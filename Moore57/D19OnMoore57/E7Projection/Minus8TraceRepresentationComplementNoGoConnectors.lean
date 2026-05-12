import Moore57.D19OnMoore57.E7Projection.Minus8TraceRepresentationComplementBoundary
import Moore57.D19OnMoore57.E7Projection.Minus8BoundaryPackageCurrentGapNoGoConnectors
import Moore57.D19OnMoore57.E7Projection.Minus8BoundaryPackageActionNoGoConnectors

/-!
# No-go connectors from trace-representation data and complementary minus-8 values

This file exposes the direct consumer surface for `TraceRepresentationData h.a1`
when the `(-8)` character values are supplied by the complementary projection
formula.  The proofs only build
`E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement`
and reuse the standard downstream package methods.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Complementary trace-representation data and the standard count inputs give
the paper-shaped fixed-star boundary for any reflection. -/
theorem involutionFixedSetStar56_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.involutionFixedSetStar56_raw_reflection k

/-- Complementary trace-representation data and the standard count inputs give
a `K_{1,55}` witness for any reflection. -/
theorem nonempty_involutionK155_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_involutionK155_raw_reflection k

/-- Complementary trace-representation data and the standard count inputs give
the fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.reflectionFixedCenterLeafBoundary

/-- Complementary trace-representation data and the standard count inputs give
the representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.representationCharacterComponentsBoundary

/-- Complementary trace-representation data and the standard count inputs rule
out the current branch-orbit final gap. -/
theorem no_currentFinalGapBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_currentFinalGapBoundary

/-- Complementary trace-representation data rules out the action-level final
boundary. -/
theorem no_actionLevelFinalBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelFinalBoundary

/-- Complementary trace-representation data rules out the action-level local
obstruction boundary. -/
theorem no_actionLevelLocalObstructionBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelLocalObstructionBoundary

/-- Complementary trace-representation data rules out the action-level
reduced-coordinate witness boundary. -/
theorem no_actionLevelReducedCoordinateWitnessBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelReducedCoordinateWitnessBoundary

/-- Complementary trace-representation data rules out the action-level
set-invariant witness boundary. -/
theorem no_actionLevelSetInvariantWitnessBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelSetInvariantWitnessBoundary

/-- Complementary trace-representation data rules out the common-neighbor
reduced action-level boundary. -/
theorem no_actionLevelCommonNeighborReducedBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelCommonNeighborReducedBoundary

/-- Complementary trace-representation data rules out the minimal-remaining
action-level boundary. -/
theorem no_actionLevelMinimalRemainingBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingBoundary

/-- Complementary trace-representation data rules out the refined
minimal-remaining action-level boundary. -/
theorem no_actionLevelMinimalRemainingRefinedBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingRefinedBoundary

/-- Complementary trace-representation data rules out the matching-equation
refined minimal-remaining action-level boundary. -/
theorem no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingRefinedMatchingBoundary

end D19ActsOnMoore57

end

end Moore57
