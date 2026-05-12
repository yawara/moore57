import Moore57.D19OnMoore57.NoGo.K155EndpointCombinedNoGo

/-!
# Concise K155 aliases for endpoint frontiers

This file gives short raw-action-style names to the endpoint-only `K_{1,55}`
no-go surfaces.  The proofs only delegate to the existing endpoint K155
theorems.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

abbrev RemainingEndpointNonadjWitnessFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty
    (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness h)

abbrev RemainingEndpointPointwiseNonadjFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty
    (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj h)

abbrev RemainingEndpointAdjForcesAFixingFixedFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty
    (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed
      h)

abbrev RemainingEndpointAdjForcesAFixingVertexFixedFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty
    (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed
      h)

abbrev RemainingPairEndpointNonadjFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty
    (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj h)

abbrev RemainingPairEndpointTwoCommonNeighborsFrontierAfterDefaultBase
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty
    (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors
      h)

/-- Concise endpoint-witness K155 no-go alias. -/
theorem no_remainingEndpointNonadjWitnessFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ RemainingEndpointNonadjWitnessFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_eigenspaceCharactersAndK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hK

/-- Concise pointwise endpoint K155 no-go alias. -/
theorem no_remainingEndpointPointwiseNonadjFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ RemainingEndpointPointwiseNonadjFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_eigenspaceCharactersAndK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hK

/-- Concise endpoint-forces-fixed K155 no-go alias. -/
theorem no_remainingEndpointAdjForcesAFixingFixedFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ RemainingEndpointAdjForcesAFixingFixedFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_eigenspaceCharactersAndK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hK

/-- Concise vertex-fixed endpoint-forces-fixed K155 no-go alias. -/
theorem no_remainingEndpointAdjForcesAFixingVertexFixedFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ RemainingEndpointAdjForcesAFixingVertexFixedFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_eigenspaceCharactersAndK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hK

/-- Concise pair-endpoint non-adjacency K155 no-go alias. -/
theorem no_remainingPairEndpointNonadjFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ RemainingPairEndpointNonadjFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_eigenspaceCharactersAndK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hK

/-- Concise pair common-neighbor endpoint K155 no-go alias. -/
theorem no_remainingPairEndpointTwoCommonNeighborsFrontierAfterDefaultBase_of_eigenspaceCharactersAndK155_autoRotation
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
    ¬ RemainingPairEndpointTwoCommonNeighborsFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_eigenspaceCharactersAndK155_autoRotation
    h alpha beta gamma A B C h7 hMinus8 hK

end

end Moore57
