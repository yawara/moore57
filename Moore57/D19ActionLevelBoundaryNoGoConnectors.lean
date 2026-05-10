import Moore57.BranchOrbitABCActionLevelCaseBoundary
import Moore57.BranchOrbitABCActionLevelFinalBoundary
import Moore57.BranchOrbitABCActionLevelLocalObstructionBoundary
import Moore57.BranchOrbitABCActionLevelWitnessBoundary
import Moore57.BranchOrbitABCCoordinateWitnessFinalBoundary
import Moore57.BranchOrbitABCDoublingEquationSupportBoundary
import Moore57.BranchOrbitABCReducedCoordinateWitnessBoundary
import Moore57.BranchOrbitABCSetInvariantWitnessBoundary
import Moore57.D19FinalCharacterComponentConnectors
import Moore57.D19LinearCharacterMinus8K155Connectors

/-!
# Action-level boundary no-go connectors

This file only exposes delegation wrappers from existing character/K155 inputs
to existing action-level boundary no-go theorems.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19BoundaryNoGoConnectors

variable {h : D19ActsOnMoore57 V Γ}

/-- Generic component-boundary connector for no-go statements of the form
`¬ ∃ representationComponents, Nonempty Boundary`. -/
theorem no_nonempty_of_components
    {Boundary : Type*}
    (hno :
      ¬ ∃ _representationComponents :
            D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
          Nonempty Boundary)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty Boundary := by
  intro boundary
  exact hno ⟨representationComponents, boundary⟩

/-- Final-character-input connector for no-go statements of the form
`¬ ∃ representationComponents, Nonempty Boundary`. -/
theorem no_nonempty_of_finalCharacterInputs
    {Boundary : Type*}
    (hno :
      ¬ ∃ _representationComponents :
            D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
          Nonempty Boundary)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty Boundary :=
  no_nonempty_of_components hno
    character.representationCharacterComponentsBoundary

/-- K155/eigenspace-character connector for no-go statements of the form
`¬ ∃ representationComponents, Nonempty Boundary`. -/
theorem no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    {Boundary : Type*}
    (hno :
      ¬ ∃ _representationComponents :
            D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
          Nonempty Boundary)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty Boundary :=
  no_nonempty_of_components hno
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_eigenspaceCharactersAndInvolutionK155
        h alpha beta gamma A B C h7 hMinus8 hK)

end D19BoundaryNoGoConnectors

/-- Component-boundary form of the action-level case no-go. -/
theorem no_D19_actionLevelCaseBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelCaseBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_components
    (h := h) (no_D19_actionLevelCaseBoundary h) representationComponents

/-- Final-character-input form of the action-level case no-go. -/
theorem no_D19_actionLevelCaseBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCActionLevelCaseBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h) (no_D19_actionLevelCaseBoundary h) character

/-- K155/eigenspace-character form of the action-level case no-go. -/
theorem no_D19_actionLevelCaseBoundary_of_eigenspaceCharactersAndK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCActionLevelCaseBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h) (no_D19_actionLevelCaseBoundary h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Component-boundary form of the action-level witness no-go. -/
theorem no_D19_actionLevelWitnessBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelWitnessBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_components
    (h := h) (no_D19_actionLevelWitnessBoundary h) representationComponents

/-- Final-character-input form of the action-level witness no-go. -/
theorem no_D19_actionLevelWitnessBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCActionLevelWitnessBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h) (no_D19_actionLevelWitnessBoundary h) character

/-- K155/eigenspace-character form of the action-level witness no-go. -/
theorem no_D19_actionLevelWitnessBoundary_of_eigenspaceCharactersAndK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCActionLevelWitnessBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h) (no_D19_actionLevelWitnessBoundary h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Component-boundary form of the coordinate-witness no-go. -/
theorem no_D19_actionLevelCoordinateWitnessBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelCoordinateWitnessBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_components
    (h := h) (no_D19_actionLevelCoordinateWitnessBoundary h)
    representationComponents

/-- Final-character-input form of the coordinate-witness no-go. -/
theorem no_D19_actionLevelCoordinateWitnessBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCActionLevelCoordinateWitnessBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h) (no_D19_actionLevelCoordinateWitnessBoundary h) character

/-- K155/eigenspace-character form of the coordinate-witness no-go. -/
theorem no_D19_actionLevelCoordinateWitnessBoundary_of_eigenspaceCharactersAndK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCActionLevelCoordinateWitnessBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h) (no_D19_actionLevelCoordinateWitnessBoundary h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Component-boundary form of the action-level final no-go. -/
theorem no_D19_actionLevelFinalBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_components
    (h := h) (no_D19_actionLevelFinalBoundary h) representationComponents

/-- Final-character-input form of the action-level final no-go. -/
theorem no_D19_actionLevelFinalBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h) (no_D19_actionLevelFinalBoundary h) character

/-- K155/eigenspace-character form of the action-level final no-go. -/
theorem no_D19_actionLevelFinalBoundary_of_eigenspaceCharactersAndK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h) (no_D19_actionLevelFinalBoundary h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Component-boundary form of the local-obstruction no-go. -/
theorem no_D19_actionLevelLocalObstructionBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_components
    (h := h) (no_D19_actionLevelLocalObstructionBoundary h)
    representationComponents

/-- Final-character-input form of the local-obstruction no-go. -/
theorem no_D19_actionLevelLocalObstructionBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h) (no_D19_actionLevelLocalObstructionBoundary h) character

/-- K155/eigenspace-character form of the local-obstruction no-go. -/
theorem no_D19_actionLevelLocalObstructionBoundary_of_eigenspaceCharactersAndK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h) (no_D19_actionLevelLocalObstructionBoundary h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Component-boundary form of the doubling equation/support no-go. -/
theorem no_D19_actionLevelDoublingEquationSupportBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_components
    (h := h) (no_D19_actionLevelDoublingEquationSupportBoundary h)
    representationComponents

/-- Final-character-input form of the doubling equation/support no-go. -/
theorem no_D19_actionLevelDoublingEquationSupportBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h) (no_D19_actionLevelDoublingEquationSupportBoundary h) character

/-- K155/eigenspace-character form of the doubling equation/support no-go. -/
theorem no_D19_actionLevelDoublingEquationSupportBoundary_of_eigenspaceCharactersAndK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h) (no_D19_actionLevelDoublingEquationSupportBoundary h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Component-boundary form of the set-invariant witness no-go. -/
theorem no_D19_actionLevelSetInvariantWitnessBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) := by
  intro boundary
  exact no_D19_actionLevelSetInvariantWitnessBoundary h
    ⟨representationComponents, boundary⟩

/-- Final-character-input form of the set-invariant witness no-go. -/
theorem no_D19_actionLevelSetInvariantWitnessBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :=
  no_D19_actionLevelSetInvariantWitnessBoundary_of_components h
    ((D19ActsOnMoore57.D19RepresentationCharacterInput.nonempty_iff_componentsBoundary
        h).mp ⟨character.representation⟩)

/-- K155/eigenspace-character form of the set-invariant witness no-go. -/
theorem no_D19_actionLevelSetInvariantWitnessBoundary_of_eigenspaceCharactersAndK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :=
  no_D19_actionLevelSetInvariantWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_eigenspaceCharactersAndInvolutionK155
        h alpha beta gamma A B C h7 hMinus8 hK)

/-- Component-boundary form of the reduced-coordinate witness no-go. -/
theorem no_D19_actionLevelReducedCoordinateWitnessBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) := by
  intro boundary
  exact no_D19_actionLevelReducedCoordinateWitnessBoundary h
    ⟨representationComponents, boundary⟩

/-- Final-character-input form of the reduced-coordinate witness no-go. -/
theorem no_D19_actionLevelReducedCoordinateWitnessBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :=
  no_D19_actionLevelReducedCoordinateWitnessBoundary_of_components h
    ((D19ActsOnMoore57.D19RepresentationCharacterInput.nonempty_iff_componentsBoundary
        h).mp ⟨character.representation⟩)

/-- K155/eigenspace-character form of the reduced-coordinate witness no-go. -/
theorem no_D19_actionLevelReducedCoordinateWitnessBoundary_of_eigenspaceCharactersAndK155_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :=
  no_D19_actionLevelReducedCoordinateWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_eigenspaceCharactersAndInvolutionK155
        h alpha beta gamma A B C h7 hMinus8 hK)

end

end Moore57
