import Moore57.BranchOrbitABCDoublingEquationSupportBoundary
import Moore57.BranchOrbitABCCardTwoAllOffsetsFinalGapBoundary

/-!
# Action-level all-offset support-subset obstruction

This file connects the action-level equation/support package to the corrected
all-offset card-two obstruction.  The support-subset exception, midpoint
criterion, and two-point A-fixing support already force endpoint adjacency at
every nonzero offset; the all-offset common-neighbor obstruction rules this
out.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instActionLevelAllOffsetsSupportBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instActionLevelAllOffsetsSupportBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCActionLevelDoublingEquationSupportBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The A-fixing input in the action-level equation/support package gives the
two-point A-fixing support-card boundary used by the all-offset obstruction. -/
def toAFixingReflectionFixedNeighborCardBoundary
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :
    BranchOrbitABCReflectionLabeling.AFixingReflectionFixedNeighborCardBoundary
      boundary.labeling :=
  boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary

/-- Repackage the action-level support-subset exception as the final-gap report
field. -/
def toSupportSubsetExceptionIssueBoundary
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :
    BranchOrbitABCSupportSubsetExceptionIssueBoundary boundary.labeling where
  support_subset_exception := boundary.support_subset_exception

/-- The action-level support-subset exception and midpoint criterion produce
endpoint adjacency at every nonzero offset on the A-fixing support. -/
def allOffsetsEndpointAdj
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :=
  boundary.labeling.all_offsets_endpoint_adj_of_support_subset_midpointExceptionSet
    boundary.referenceMatching.criterion
    boundary.support_subset_exception

/-- The support-card input gives the global no-all-offsets endpoint-adjacency
package. -/
def toNoAllOffsetsEndpointAdj
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :
    BranchOrbitABCReflectionLabeling.NoAllOffsetsEndpointAdj
      boundary.labeling :=
  boundary.toAFixingReflectionFixedNeighborCardBoundary
    |>.toNoAllOffsetsEndpointAdj

/-- The support-card and midpoint criterion produce the global no-all-offsets
support-subset package. -/
def toNoAllOffsetsSupportSubsetBoundary
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :
    BranchOrbitABCReflectionLabeling.NoAllOffsetsSupportSubsetBoundary
      boundary.labeling :=
  boundary.toNoAllOffsetsEndpointAdj
    |>.toNoAllOffsetsSupportSubsetBoundary
      boundary.referenceMatching.criterion

/-- Direct contradiction between the endpoint adjacency forced by the global
support-subset exception and the all-offset endpoint obstruction. -/
theorem false_of_allOffsetsEndpointAdj
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) : False :=
  boundary.toNoAllOffsetsEndpointAdj.not_all_offsets_endpoint_adj
    boundary.allOffsetsEndpointAdj

/-- The all-offset endpoint obstruction rules out the packaged final-gap
support-subset exception field. -/
theorem not_supportSubsetExceptionIssueBoundary
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :
    ¬ BranchOrbitABCSupportSubsetExceptionIssueBoundary boundary.labeling :=
  boundary.toNoAllOffsetsSupportSubsetBoundary
    |>.not_supportSubsetExceptionIssueBoundary

/-- Direct contradiction from the action-level global support-subset exception,
support-card boundary, and midpoint criterion. -/
theorem false_of_allOffsetsSupportSubset
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) : False :=
  boundary.not_supportSubsetExceptionIssueBoundary
    boundary.toSupportSubsetExceptionIssueBoundary

end BranchOrbitABCActionLevelDoublingEquationSupportBoundary

/-- No action-level equation/support package exists once the all-offset
card-two obstruction is used. -/
theorem not_actionLevelDoublingEquationSupportBoundary_allOffsets
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) := by
  rintro ⟨boundary⟩
  exact boundary.false_of_allOffsetsSupportSubset

/-- In particular, the representation-component version is impossible by the
same all-offset obstruction. -/
theorem no_D19_actionLevelDoublingEquationSupportBoundary_allOffsets
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty
          (BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) := by
  rintro ⟨_, hboundary⟩
  exact not_actionLevelDoublingEquationSupportBoundary_allOffsets h hboundary

end

end Moore57
