import Moore57.D19LinearCharacterNonemptyNoGoConnectors
import Moore57.D19ActionLevelBoundaryNoGoConnectors

/-!
# Action-level no-go connectors from nonempty linear-character input

This file routes `Nonempty (D19LinearCharacterInput h)` into the action-level
boundary no-go wrappers that consume representation-character components.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Action-level case no-go from a nonempty linear-character input. -/
theorem no_D19_actionLevelCaseBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelCaseBoundary h) :=
  no_D19_actionLevelCaseBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level witness no-go from a nonempty linear-character input. -/
theorem no_D19_actionLevelWitnessBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelWitnessBoundary h) :=
  no_D19_actionLevelWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level coordinate-witness no-go from a nonempty linear-character
input. -/
theorem no_D19_actionLevelCoordinateWitnessBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelCoordinateWitnessBoundary h) :=
  no_D19_actionLevelCoordinateWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level final no-go from a nonempty linear-character input. -/
theorem no_D19_actionLevelFinalBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  no_D19_actionLevelFinalBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level local-obstruction no-go from a nonempty linear-character
input. -/
theorem no_D19_actionLevelLocalObstructionBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) :=
  no_D19_actionLevelLocalObstructionBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level doubling-equation/support no-go from a nonempty
linear-character input. -/
theorem no_D19_actionLevelDoublingEquationSupportBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :=
  no_D19_actionLevelDoublingEquationSupportBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level set-invariant witness no-go from a nonempty linear-character
input. -/
theorem no_D19_actionLevelSetInvariantWitnessBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :=
  no_D19_actionLevelSetInvariantWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level reduced-coordinate witness no-go from a nonempty
linear-character input. -/
theorem no_D19_actionLevelReducedCoordinateWitnessBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :=
  no_D19_actionLevelReducedCoordinateWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

end

end Moore57
