import Moore57.BranchOrbitABCMinimalRemainingLocalObstructionBoundary

/-!
# Refined minimal remaining boundary with singleton fixedness supplied

The refined minimal remaining package already contains the endpoint target-sign
boundary.  Through the midpoint-equation invariance pipeline, that boundary
supplies the singleton-fixedness input used to exclude the card-one
midpoint-exception/support case.  This file records the resulting direct path
to the local obstruction package.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The endpoint target-sign field supplies singleton fixedness for the
card-one midpoint-exception/support case via midpoint-equation invariance. -/
def toMidpointExceptionAFixingSupportSingletonFixedBoundary
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
      boundary.labeling :=
  boundary.endpointTargetSign
    |>.toMidpointEquationSetAFixingInvariantBoundary
    |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary
      boundary.referenceMatching.criterion

/-- Convert the refined minimal remaining package directly to the local
midpoint-exception obstruction package. -/
def toMidpointExceptionAFixingSupportLocalObstructionBoundary'
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    MidpointExceptionAFixingSupportLocalObstructionBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toMidpointExceptionAFixingSupportLocalObstructionBoundary
    boundary.toMidpointExceptionAFixingSupportSingletonFixedBoundary

/-- Convert the refined minimal remaining package directly to the action-level
local obstruction boundary. -/
def toActionLevelLocalObstructionBoundary'
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    BranchOrbitABCActionLevelLocalObstructionBoundary h :=
  boundary.toActionLevelLocalObstructionBoundary
    boundary.toMidpointExceptionAFixingSupportSingletonFixedBoundary

/-- Convert the refined minimal remaining package directly to the action-level
case boundary. -/
def toActionLevelCaseBoundary'
    (boundary :
      BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    BranchOrbitABCActionLevelCaseBoundary h :=
  boundary.toActionLevelLocalObstructionBoundary'
    |>.toActionLevelCaseBoundary

end BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary

end

end Moore57
