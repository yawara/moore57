import Moore57.D19OnMoore57.NoGo.NonemptyK155NoGoConnectors
import Moore57.D19OnMoore57.Involution.FixedStarPaperBoundary

/-!
# Paper fixed-star no-go connectors

This file exposes thin wrappers from the paper-shaped fixed-star hypothesis to
the existing Prop-level `K_{1,55}` no-go connectors.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Eigenspace-character no-go with a paper-shaped `56`-vertex fixed-star
reflection hypothesis and automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndPaperFixedStar56_autoRotation
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
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndNonemptyK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hStar.nonempty_involutionK155

/-- Eigenspace-character no-go for the explicit per-reflection `K_{1,55}`
wrapper, consuming a paper-shaped `56`-vertex fixed-star reflection
hypothesis. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndPaperFixedStar56_autoRotation
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
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndNonemptyK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hStar.nonempty_involutionK155

/-- Current final-gap no-go with a paper-shaped `56`-vertex fixed-star
reflection hypothesis. -/
theorem no_D19_currentFinalGapBoundary_of_eigenspaceCharactersAndPaperFixedStar56_autoRotation
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
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_D19_currentFinalGapBoundary_of_eigenspaceCharactersAndNonemptyK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hStar.nonempty_involutionK155

/-- Endpoint-obstruction final-boundary no-go with a paper-shaped `56`-vertex
fixed-star reflection hypothesis. -/
theorem no_D19_endpointObstructionFinalBoundary_of_eigenspaceCharactersAndPaperFixedStar56_autoRotation
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
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ Nonempty (BranchOrbitABCEndpointObstructionFinalBoundary h) :=
  no_D19_endpointObstructionFinalBoundary_of_eigenspaceCharactersAndNonemptyK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hStar.nonempty_involutionK155

end

end Moore57
