import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCDoublingReflectedAdjFromEquation
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCMinimalRemainingRefinedBoundary

/-!
# Doubling equation/support action-level boundary

This file refines the action-level minimal remaining boundary by replacing the
doubling reflected-adjacency input with an equation-style input plus the
support-subset-exception hypothesis needed to invoke the midpoint criterion.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instDoublingEquationSupportBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instDoublingEquationSupportBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Action-level package whose doubling input is equation-style and whose
midpoint criterion is supplied by support-subset-exception hypotheses. -/
structure BranchOrbitABCActionLevelDoublingEquationSupportBoundary
    (h : D19ActsOnMoore57 V Γ) where
  starCounts : ReflectionFixedNeighborStarCounts h
  labeling : BranchOrbitABCReflectionLabeling h
  middle :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarMiddleBoundary
      starCounts.toReflectionFixedStarBoundary labeling
  aFixing :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
      starCounts.toReflectionFixedStarBoundary labeling
  referenceMatching :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary labeling
  doublingFromEquation :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingMiddleReflectedAdjFromEquationBoundary
      labeling
  support_subset_exception :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      labeling.aFiberReflectionSupport ⊆
        labeling.midpointExceptionSet m hm
  endpointTargetSign :
    BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
      labeling
  endpointSignAdjacency :
    BranchOrbitABCReflectionLabeling.EndpointSignAdjacencyBoundary labeling

namespace BranchOrbitABCActionLevelDoublingEquationSupportBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the equation/support doubling package to the reflected-adjacency
refined action-level package. -/
def toActionLevelMinimalRemainingRefinedBoundary
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :
    BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  doublingReflectedAdj :=
    boundary.doublingFromEquation
      |>.toMidpointExceptionDoublingMiddleReflectedAdjBoundary_of_midpointCriterion
        boundary.referenceMatching.criterion
        boundary.support_subset_exception
  endpointTargetSign := boundary.endpointTargetSign
  endpointSignAdjacency := boundary.endpointSignAdjacency

/-- Convert the equation/support package to the previous minimal package. -/
def toActionLevelMinimalRemainingBoundary
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :
    BranchOrbitABCActionLevelMinimalRemainingBoundary h :=
  boundary.toActionLevelMinimalRemainingRefinedBoundary
    |>.toActionLevelMinimalRemainingBoundary

/-- Direct conversion to the common-neighbor reduced package. -/
def toActionLevelCommonNeighborReducedBoundary
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :
    BranchOrbitABCActionLevelCommonNeighborReducedBoundary h :=
  boundary.toActionLevelMinimalRemainingRefinedBoundary
    |>.toActionLevelCommonNeighborReducedBoundary

/-- Convert the equation/support package to the Lean-aware final boundary. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelMinimalRemainingRefinedBoundary
    |>.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCActionLevelDoublingEquationSupportBoundary

/-- No equation/support action-level package can coexist with the
representation component boundary. -/
theorem no_D19_actionLevelDoublingEquationSupportBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty
          (BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_actionLevelMinimalRemainingRefinedBoundary h
    ⟨representationComponents,
      ⟨boundary.toActionLevelMinimalRemainingRefinedBoundary⟩⟩

end

end Moore57
