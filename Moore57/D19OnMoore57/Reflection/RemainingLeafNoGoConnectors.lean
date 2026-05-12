import Moore57.D19OnMoore57.Reflection.RemainingLeafConnectorBoundary
import Moore57.D19OnMoore57.NoGo.ActionLevelBoundaryNoGoConnectors

/-!
# Remaining reflection leaf no-go connectors

This file exposes final-character and K155/eigenspace-character aliases for
the remaining fixed-center local-leaf connectors that already have
component-boundary no-go statements.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final-character-input form of the remaining local-leaf reference connector
no-go. -/
theorem no_remainingNon56FixedCenterLeafReferenceConnector_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty (RemainingNon56FixedCenterLeafReferenceConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h) (no_remainingNon56FixedCenterLeafReferenceConnector_of_components h)
    character

/-- K155/eigenspace-character form of the remaining local-leaf reference
connector no-go. -/
theorem no_remainingNon56FixedCenterLeafReferenceConnector_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ Nonempty (RemainingNon56FixedCenterLeafReferenceConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h) (no_remainingNon56FixedCenterLeafReferenceConnector_of_components h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Final-character-input form of the remaining local-leaf
midpoint-disjointness connector no-go. -/
theorem no_remainingNon56FixedCenterLeafMidpointDisjointnessConnector_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty
        (RemainingNon56FixedCenterLeafMidpointDisjointnessConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h)
    (no_remainingNon56FixedCenterLeafMidpointDisjointnessConnector_of_components
      h)
    character

/-- K155/eigenspace-character form of the remaining local-leaf
midpoint-disjointness connector no-go. -/
theorem no_remainingNon56FixedCenterLeafMidpointDisjointnessConnector_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNon56FixedCenterLeafMidpointDisjointnessConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h)
    (no_remainingNon56FixedCenterLeafMidpointDisjointnessConnector_of_components
      h)
    alpha beta gamma A B C h7 hMinus8 hK

/-- Final-character-input form of the remaining local-leaf local-obstruction
connector no-go. -/
theorem no_remainingNon56FixedCenterLeafLocalObstructionConnector_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ Nonempty
        (RemainingNon56FixedCenterLeafLocalObstructionConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_finalCharacterInputs
    (h := h)
    (no_remainingNon56FixedCenterLeafLocalObstructionConnector_of_components
      h)
    character

/-- K155/eigenspace-character form of the remaining local-leaf
local-obstruction connector no-go. -/
theorem no_remainingNon56FixedCenterLeafLocalObstructionConnector_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNon56FixedCenterLeafLocalObstructionConnector h) :=
  D19BoundaryNoGoConnectors.no_nonempty_of_eigenspaceCharactersAndK155_autoRotation
    (h := h)
    (no_remainingNon56FixedCenterLeafLocalObstructionConnector_of_components
      h)
    alpha beta gamma A B C h7 hMinus8 hK

end

end Moore57
