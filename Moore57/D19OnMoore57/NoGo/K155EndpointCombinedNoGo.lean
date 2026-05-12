import Moore57.D19OnMoore57.NoGo.EndpointFrontierAutoNoGo
import Moore57.D19OnMoore57.NoGo.DefaultBaseCombinedFrontier

/-!
# K155 no-go surfaces for endpoint and combined frontiers

This file exposes `K_{1,55}` versions of the endpoint and combined-wrapper
auto-rotation no-go theorems.  Each proof only converts the explicit
`InvolutionK155` witness to `InvolutionFixedStar55` and delegates to the
existing fixed-star theorem.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Endpoint non-adjacency wrapper no-go from an explicit `K_{1,55}` reflection
witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Pointwise endpoint non-adjacency wrapper no-go from an explicit `K_{1,55}`
reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Endpoint-forces-fixed wrapper no-go from an explicit `K_{1,55}` reflection
witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Vertex-fixed endpoint-forces-fixed wrapper no-go from an explicit
`K_{1,55}` reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Pair endpoint non-adjacency wrapper no-go from an explicit `K_{1,55}`
reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Pair common-neighbor endpoint wrapper no-go from an explicit `K_{1,55}`
reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Combined lean-aware endpoint-obstruction wrapper no-go from an explicit
`K_{1,55}` reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Combined A-fixing singleton endpoint-obstruction wrapper no-go from an
explicit `K_{1,55}` reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Combined A-fixing doubling endpoint-obstruction wrapper no-go from an
explicit `K_{1,55}` reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Combined fixed-star-local singleton endpoint-obstruction wrapper no-go
from an explicit `K_{1,55}` reflection witness, with automatic rotation
counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Combined action-level singleton endpoint-obstruction wrapper no-go from an
explicit `K_{1,55}` reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

/-- Combined action-level doubling endpoint-obstruction wrapper no-go from an
explicit `K_{1,55}` reflection witness, with automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_eigenspaceCharactersAndK155_autoRotation
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
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_eigenspaceCharactersAndFixedStar55_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (InvolutionK155.toInvolutionFixedStar55 h.isMoore hK)

end

end Moore57
