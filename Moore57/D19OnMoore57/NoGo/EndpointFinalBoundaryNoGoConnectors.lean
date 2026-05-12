import Moore57.D19OnMoore57.BranchOrbit.ABCEndpointObstructionFinalBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCEndpointPairedFinalBoundary
import Moore57.D19OnMoore57.NoGo.ActionLevelBoundaryNoGoConnectors

/-!
# Endpoint-final boundary no-go connectors

This file exposes direct no-go aliases for the endpoint-obstruction and
endpoint-paired final boundary packages.  The proofs only delegate through the
existing component-boundary no-go statements and the standard final-character
or K155/eigenspace-character constructors.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Component-boundary form of the action-level endpoint-obstruction no-go. -/
theorem no_D19_actionLevelEndpointObstructionBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCActionLevelEndpointObstructionBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_components
    (h := h) (no_D19_actionLevelEndpointObstructionBoundary h)
    representationComponents

/-- Final-character-input form of the action-level endpoint-obstruction
no-go. -/
theorem no_D19_actionLevelEndpointObstructionBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCActionLevelEndpointObstructionBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h) (no_D19_actionLevelEndpointObstructionBoundary h) character

/-- K155/eigenspace-character form of the action-level endpoint-obstruction
no-go. -/
theorem no_D19_actionLevelEndpointObstructionBoundary_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ Nonempty (BranchOrbitABCActionLevelEndpointObstructionBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h) (no_D19_actionLevelEndpointObstructionBoundary h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Component-boundary form of the endpoint-obstruction final no-go. -/
theorem no_D19_endpointObstructionFinalBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCEndpointObstructionFinalBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_components
    (h := h) (no_D19_endpointObstructionFinalBoundary h)
    representationComponents

/-- Final-character-input form of the endpoint-obstruction final no-go. -/
theorem no_D19_endpointObstructionFinalBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCEndpointObstructionFinalBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h) (no_D19_endpointObstructionFinalBoundary h) character

/-- K155/eigenspace-character form of the endpoint-obstruction final no-go. -/
theorem no_D19_endpointObstructionFinalBoundary_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ Nonempty (BranchOrbitABCEndpointObstructionFinalBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h) (no_D19_endpointObstructionFinalBoundary h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Component-boundary form of the endpoint-paired final no-go. -/
theorem no_D19_endpointPairedFinalBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ Nonempty (BranchOrbitABCEndpointPairedFinalBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_components
    (h := h) (no_D19_endpointPairedFinalBoundary h)
    representationComponents

/-- Final-character-input form of the endpoint-paired final no-go. -/
theorem no_D19_endpointPairedFinalBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (BranchOrbitABCEndpointPairedFinalBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h) (no_D19_endpointPairedFinalBoundary h) character

/-- K155/eigenspace-character form of the endpoint-paired final no-go. -/
theorem no_D19_endpointPairedFinalBoundary_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ Nonempty (BranchOrbitABCEndpointPairedFinalBoundary h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h) (no_D19_endpointPairedFinalBoundary h)
    alpha beta gamma A B C h7 hMinus8 hK

end

end Moore57
