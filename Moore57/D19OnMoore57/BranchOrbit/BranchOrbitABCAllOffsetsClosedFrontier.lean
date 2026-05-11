import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCActionLevelAllOffsetsSupportBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCFinalGapAllOffsetsContradiction
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCEndpointPairedFinalBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCEndpointObstructionFinalBoundary

/-!
# All-offset closed branch-orbit frontier

This file records the nearby action-level/final-gap packages that are already
closed by the all-offset card-two common-neighbor obstruction.  It does not add
a root import; it is only a connector/inventory file for the current frontier.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ## Named all-offset closures -/

/-- The action-level equation/support package is closed by the all-offset
support-subset obstruction. -/
theorem no_allOffsetsClosed_actionLevelDoublingEquationSupportBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :=
  not_actionLevelDoublingEquationSupportBoundary_allOffsets h

/-- The current final-gap report is closed by the all-offset common-neighbor
obstruction. -/
theorem no_allOffsetsClosed_currentFinalGapBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  not_currentFinalGapBoundary_allOffsetsCommonNeighbor h

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}
variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Generic support-subset contradiction used by nearby final-gap packages:
the A-fixing two-point support and midpoint criterion rule out the report-level
support-subset exception by the all-offset common-neighbor obstruction. -/
theorem false_of_aFixing_supportSubset_allOffsetsCommonNeighbor
    (aFixing : ReflectionFixedStarAFixingBoundary star labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (supportSubset : BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling) :
    False :=
  aFixing.toAFixingReflectionFixedNeighborCardBoundary
    |>.not_supportSubsetExceptionIssueBoundary criterion supportSubset

end BranchOrbitABCReflectionLabeling

/-! ## Nearby final-gap packages closed by the same all-offset obstruction -/

namespace BranchOrbitABCEndpointPairedFinalGapBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The endpoint-paired final-gap report has the same support-subset all-offset
contradiction as the current final-gap report; its endpoint field is not used. -/
theorem false_of_supportSubset_allOffsetsCommonNeighbor
    (boundary : BranchOrbitABCEndpointPairedFinalGapBoundary h) : False :=
  _root_.Moore57.BranchOrbitABCReflectionLabeling.false_of_aFixing_supportSubset_allOffsetsCommonNeighbor
      boundary.aFixing
      boundary.doublingReflectedEquation.midpointCriterion
      boundary.supportSubsetException

end BranchOrbitABCEndpointPairedFinalGapBoundary

/-- No endpoint-paired final-gap report exists by the all-offset
common-neighbor obstruction. -/
theorem not_endpointPairedFinalGapBoundary_allOffsetsCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCEndpointPairedFinalGapBoundary h) := by
  rintro ⟨boundary⟩
  exact boundary.false_of_supportSubset_allOffsetsCommonNeighbor

/-- Public representation-component spelling for the endpoint-paired final-gap
closure. -/
theorem no_D19_endpointPairedFinalGapBoundary_allOffsetsCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty (BranchOrbitABCEndpointPairedFinalGapBoundary h) := by
  rintro ⟨_, hboundary⟩
  exact not_endpointPairedFinalGapBoundary_allOffsetsCommonNeighbor h hboundary

/-- The endpoint-paired final package is closed because its underlying
final-gap report is closed. -/
theorem not_endpointPairedFinalBoundary_allOffsetsCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCEndpointPairedFinalBoundary h) := by
  rintro ⟨boundary⟩
  exact not_endpointPairedFinalGapBoundary_allOffsetsCommonNeighbor h
    ⟨boundary.pairedFinalGap⟩

/-- Public representation-component spelling for the endpoint-paired final
package closure. -/
theorem no_D19_endpointPairedFinalBoundary_allOffsetsCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty (BranchOrbitABCEndpointPairedFinalBoundary h) := by
  rintro ⟨_, hboundary⟩
  exact not_endpointPairedFinalBoundary_allOffsetsCommonNeighbor h hboundary

namespace BranchOrbitABCEndpointObstructionFinalBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The endpoint-obstruction final package also carries the same
support-subset all-offset contradiction; its endpoint obstruction and singleton
fields are not used. -/
theorem false_of_supportSubset_allOffsetsCommonNeighbor
    (boundary : BranchOrbitABCEndpointObstructionFinalBoundary h) : False :=
  _root_.Moore57.BranchOrbitABCReflectionLabeling.false_of_aFixing_supportSubset_allOffsetsCommonNeighbor
      boundary.aFixing
      boundary.doublingReflectedEquation.midpointCriterion
      boundary.supportSubsetException

end BranchOrbitABCEndpointObstructionFinalBoundary

/-- No endpoint-obstruction final package exists by the all-offset
common-neighbor obstruction. -/
theorem not_endpointObstructionFinalBoundary_allOffsetsCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCEndpointObstructionFinalBoundary h) := by
  rintro ⟨boundary⟩
  exact boundary.false_of_supportSubset_allOffsetsCommonNeighbor

/-- Public representation-component spelling for the endpoint-obstruction
final package closure. -/
theorem no_D19_endpointObstructionFinalBoundary_allOffsetsCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty (BranchOrbitABCEndpointObstructionFinalBoundary h) := by
  rintro ⟨_, hboundary⟩
  exact not_endpointObstructionFinalBoundary_allOffsetsCommonNeighbor h
    hboundary

end

end Moore57
