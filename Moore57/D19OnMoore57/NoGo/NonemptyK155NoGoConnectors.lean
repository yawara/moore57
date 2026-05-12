import Moore57.D19OnMoore57.NoGo.CurrentGapBoundaryNoGoConnectors
import Moore57.D19OnMoore57.NoGo.EndpointFinalBoundaryNoGoConnectors
import Moore57.D19OnMoore57.NoGo.FixedCenterLeafReplacement
import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontier

/-!
# Nonempty K155 no-go connectors

This file exposes low-risk wrappers from Prop-level existence of a
`K_{1,55}` reflection witness to existing no-go surfaces that consume an
explicit `InvolutionK155` witness.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Eigenspace-character no-go with a Prop-level `K_{1,55}` reflection witness
and automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndNonemptyK155_autoRotation
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
    (hK : Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt)))) :
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) := by
  rcases hK with ⟨hK⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
      h alpha beta gamma A B C h7 hMinus8 hK

/-- Eigenspace-character no-go for the explicit per-reflection `K_{1,55}`
wrapper, consuming only Prop-level existence of one `K_{1,55}` reflection
witness. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndNonemptyK155_autoRotation
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
    (hK : Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt)))) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) := by
  rcases hK with ⟨hK⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndK155_autoRotation
      h alpha beta gamma A B C h7 hMinus8 hK

/-- Current final-gap no-go with Prop-level existence of a `K_{1,55}`
reflection witness. -/
theorem no_D19_currentFinalGapBoundary_of_eigenspaceCharactersAndNonemptyK155_autoRotation
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
    (hK : Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt)))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) := by
  rcases hK with ⟨hK⟩
  exact
    no_D19_currentFinalGapBoundary_of_eigenspaceCharactersAndK155_autoRotation
      h alpha beta gamma A B C h7 hMinus8 hK

/-- Endpoint-obstruction final-boundary no-go with Prop-level existence of a
`K_{1,55}` reflection witness. -/
theorem no_D19_endpointObstructionFinalBoundary_of_eigenspaceCharactersAndNonemptyK155_autoRotation
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
    (hK : Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt)))) :
    ¬ Nonempty (BranchOrbitABCEndpointObstructionFinalBoundary h) := by
  rcases hK with ⟨hK⟩
  exact
    no_D19_endpointObstructionFinalBoundary_of_eigenspaceCharactersAndK155_autoRotation
      h alpha beta gamma A B C h7 hMinus8 hK

end

end Moore57
