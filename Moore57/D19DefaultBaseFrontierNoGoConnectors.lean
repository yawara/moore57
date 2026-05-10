import Moore57.BranchOrbitABCDefaultBaseLocalObstructionFrontier
import Moore57.BranchOrbitABCDefaultBaseReferenceFrontier
import Moore57.BranchOrbitABCSupportCardFrontier
import Moore57.D19ActionLevelBoundaryNoGoConnectors

/-!
# Default-base frontier no-go connectors

This file exposes final-character and K155/eigenspace-character aliases for
the default-base connector frontiers that already have component-boundary
no-go statements.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final-character-input form of the default-base fixed-center-leaf reference
connector no-go. -/
theorem no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (RemainingDefaultBaseFixedCenterLeafReferenceConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h) (no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_components h)
    character

/-- K155/eigenspace-character form of the default-base fixed-center-leaf
reference connector no-go. -/
theorem no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ Nonempty (RemainingDefaultBaseFixedCenterLeafReferenceConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h) (no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_components h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Final-character-input form of the midpoint-disjointness default-base
connector no-go. -/
theorem no_remainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty
        (RemainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h)
    (no_remainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector_of_components
      h)
    character

/-- K155/eigenspace-character form of the midpoint-disjointness default-base
connector no-go. -/
theorem no_remainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ Nonempty
        (RemainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h)
    (no_remainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector_of_components
      h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Final-character-input form of the local-obstruction default-base connector
no-go. -/
theorem no_remainingDefaultBaseFixedCenterLeafLocalObstructionConnector_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty
        (RemainingDefaultBaseFixedCenterLeafLocalObstructionConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h)
    (no_remainingDefaultBaseFixedCenterLeafLocalObstructionConnector_of_components
      h)
    character

/-- K155/eigenspace-character form of the local-obstruction default-base
connector no-go. -/
theorem no_remainingDefaultBaseFixedCenterLeafLocalObstructionConnector_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ Nonempty
        (RemainingDefaultBaseFixedCenterLeafLocalObstructionConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h)
    (no_remainingDefaultBaseFixedCenterLeafLocalObstructionConnector_of_components
      h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Final-character-input form of the A-fixing support-card connector no-go. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h)
    (no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_components
      h)
    character

/-- K155/eigenspace-character form of the A-fixing support-card connector
no-go. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h)
    (no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_components
      h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Final-character-input form of the fixed-star-local support-card connector
no-go. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector
          h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h)
    (no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector_of_components
      h)
    character

/-- K155/eigenspace-character form of the fixed-star-local support-card
connector no-go. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector
          h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h)
    (no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector_of_components
      h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Final-character-input form of the action-level-local support-card connector
no-go. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector
          h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h)
    (no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector_of_components
      h)
    character

/-- K155/eigenspace-character form of the action-level-local support-card
connector no-go. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector
          h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h)
    (no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector_of_components
      h)
    alpha beta gamma A B C h7 hMinus8 hK

end

end Moore57
