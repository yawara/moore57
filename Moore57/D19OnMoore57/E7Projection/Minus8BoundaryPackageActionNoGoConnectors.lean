import Moore57.D19OnMoore57.E7Projection.Minus8BoundaryPackageNoGoConnectors
import Moore57.D19OnMoore57.LinearCharacter.NonemptyActionNoGoConnectors

/-!
# Action-level no-go connectors for packaged E7/minus-8 boundaries

This file exposes action-level no-go frontiers directly from the Type-valued
projection-character boundary packages.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace E7Minus8CharacterReflectionCountBoundary

/-- Action-level final no-go from the packaged direct character boundary. -/
theorem no_actionLevelFinalBoundary
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  no_D19_actionLevelFinalBoundary_of_nonempty_linearCharacterInput h
    boundary.nonempty_d19LinearCharacterInput

/-- Action-level local-obstruction no-go from the packaged direct character
boundary. -/
theorem no_actionLevelLocalObstructionBoundary
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) :=
  no_D19_actionLevelLocalObstructionBoundary_of_nonempty_linearCharacterInput h
    boundary.nonempty_d19LinearCharacterInput

/-- Action-level reduced-coordinate witness no-go from the packaged direct
character boundary. -/
theorem no_actionLevelReducedCoordinateWitnessBoundary
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :=
  no_D19_actionLevelReducedCoordinateWitnessBoundary_of_nonempty_linearCharacterInput h
    boundary.nonempty_d19LinearCharacterInput

/-- Action-level set-invariant witness no-go from the packaged direct character
boundary. -/
theorem no_actionLevelSetInvariantWitnessBoundary
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :=
  no_D19_actionLevelSetInvariantWitnessBoundary_of_nonempty_linearCharacterInput h
    boundary.nonempty_d19LinearCharacterInput

end E7Minus8CharacterReflectionCountBoundary

namespace E7Minus8InversePairTraceReflectionCountBoundary

/-- Action-level final no-go from the packaged inverse-pair trace boundary. -/
theorem no_actionLevelFinalBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  no_D19_actionLevelFinalBoundary_of_nonempty_linearCharacterInput h
    boundary.nonempty_d19LinearCharacterInput

/-- Action-level local-obstruction no-go from the packaged inverse-pair trace
boundary. -/
theorem no_actionLevelLocalObstructionBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) :=
  no_D19_actionLevelLocalObstructionBoundary_of_nonempty_linearCharacterInput h
    boundary.nonempty_d19LinearCharacterInput

/-- Action-level reduced-coordinate witness no-go from the packaged
inverse-pair trace boundary. -/
theorem no_actionLevelReducedCoordinateWitnessBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :=
  no_D19_actionLevelReducedCoordinateWitnessBoundary_of_nonempty_linearCharacterInput h
    boundary.nonempty_d19LinearCharacterInput

/-- Action-level set-invariant witness no-go from the packaged inverse-pair
trace boundary. -/
theorem no_actionLevelSetInvariantWitnessBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :=
  no_D19_actionLevelSetInvariantWitnessBoundary_of_nonempty_linearCharacterInput h
    boundary.nonempty_d19LinearCharacterInput

end E7Minus8InversePairTraceReflectionCountBoundary

end D19ActsOnMoore57

end

end Moore57
