import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCFinalGapReportBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionAllSupportBoundary

/-!
# All-offset endpoint obstruction for the card-two branch

This file records the global form of the card-two endpoint obstruction.  The
existing no-card-two boundary rules out `E ⊆ S_(d/2)` offset by offset.  Here we
also expose the weaker all-offset statement needed by the parallel final-gap
wiring: not every nonzero endpoint offset can have endpoint adjacency on every
A-fixing support point.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instCardTwoAllOffsetsNoCardBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instCardTwoAllOffsetsNoCardBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Global support-subset nonexistence: it is not the case that every nonzero
endpoint offset has all of the A-fixing reflection support contained in its
corresponding midpoint exception set. -/
structure NoAllOffsetsSupportSubsetBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  not_all_offsets_support_subset_exception :
    ¬ ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      labeling.aFiberReflectionSupport ⊆
        labeling.midpointExceptionSet (midpointOf d) (midpointOf_ne_zero hd)

/-- Global endpoint-adjacency obstruction: endpoint adjacency cannot hold for
every nonzero endpoint offset and every A-fixing support point. -/
structure NoAllOffsetsEndpointAdj
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  not_all_offsets_endpoint_adj :
    ¬ ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (((labeling.data.toAFiberCoordinates.coord 0 p :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a 0)}) : V))
            (((labeling.data.toAFiberCoordinates.coord
                (0 + (midpointOf d + midpointOf d))
                (labeling.midpointReflectionCoordPerm (midpointOf d) p) :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a
                    (0 + (midpointOf d + midpointOf d)))}) : V))

namespace NoAllOffsetsEndpointAdj

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The older offset-by-offset no-all-endpoint-adjacency boundary implies the
global all-offset obstruction. -/
def ofMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    (boundary :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    NoAllOffsetsEndpointAdj labeling where
  not_all_offsets_endpoint_adj := by
    intro hall
    have hd : (1 : ZMod 19) ≠ 0 := by decide
    exact boundary.not_all_support_endpoint_adj 1 hd (hall 1 hd)

/-- Endpoint non-adjacency for all offsets/support points is stronger than the
global all-offset obstruction, provided the A-fixing support is nonempty. -/
def ofEndpointPointwiseNonadj
    (boundary :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    NoAllOffsetsEndpointAdj labeling :=
  ofMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    (boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      supportCard)

/-- If all-offset endpoint adjacency is impossible, then all-offset support
containment in the midpoint exception sets is impossible as well. -/
def toNoAllOffsetsSupportSubsetBoundary
    (boundary : NoAllOffsetsEndpointAdj labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    NoAllOffsetsSupportSubsetBoundary labeling where
  not_all_offsets_support_subset_exception := by
    intro hallSubset
    exact boundary.not_all_offsets_endpoint_adj (by
      intro d hd p hp
      exact
        labeling.midpointEndpointAdj_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
          criterion (hallSubset d hd) hp)

end NoAllOffsetsEndpointAdj

namespace NoAllOffsetsSupportSubsetBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The offset-by-offset no-card-two boundary implies the global support-subset
nonexistence statement. -/
def ofMidpointExceptionAFixingSupportNoCardTwoBoundary
    (boundary : MidpointExceptionAFixingSupportNoCardTwoBoundary labeling) :
    NoAllOffsetsSupportSubsetBoundary labeling where
  not_all_offsets_support_subset_exception := by
    intro hall
    have hd : (1 : ZMod 19) ≠ 0 := by decide
    exact boundary.not_all_support_subset_exception 1 hd (hall 1 hd)

/-- A global all-offset support-subset obstruction rules out the report-level
support-subset exception field. -/
theorem not_supportSubsetExceptionIssueBoundary
    (boundary : NoAllOffsetsSupportSubsetBoundary labeling) :
    ¬ BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling := by
  intro supportSubset
  exact boundary.not_all_offsets_support_subset_exception (by
    intro d hd
    exact supportSubset.support_subset_exception
      (midpointOf d) (midpointOf_ne_zero hd))

end NoAllOffsetsSupportSubsetBoundary

namespace NoAllOffsetsEndpointAdj

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Endpoint all-offset non-adjacency rules out the report-level
support-subset exception once the midpoint criterion is available. -/
theorem not_supportSubsetExceptionIssueBoundary
    (boundary : NoAllOffsetsEndpointAdj labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    ¬ BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling :=
  (boundary.toNoAllOffsetsSupportSubsetBoundary criterion)
    |>.not_supportSubsetExceptionIssueBoundary

end NoAllOffsetsEndpointAdj

end BranchOrbitABCReflectionLabeling

end

end Moore57
