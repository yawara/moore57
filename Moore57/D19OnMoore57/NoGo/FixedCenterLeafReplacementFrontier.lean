import Moore57.D19OnMoore57.Reflection.FixedCenterLeafActionFrontier
import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontierAfterDefaultBase

/-!
# Fixed-center-leaf replacement frontier

This file isolates the `fixedCenterLeaf` field of the compressed
post-default-base non-representation frontier.  The wrappers below replace
that field by upstream fixed-star packages and then project back to
`RemainingNonRepresentationFrontierAfterDefaultBase`.

No new combinatorial argument is introduced here; this is projection/wiring
only.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Compressed post-default-base frontier with `fixedCenterLeaf` replaced by
the induced fixed-star degree package. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees
    (h : D19ActsOnMoore57 V Γ) where
  fixedInducedStarDegrees : ReflectionFixedInducedStarDegrees h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedInducedStarDegrees.toReflectionFixedCenterLeafBoundary k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedInducedStarDegrees.toReflectionFixedCenterLeafBoundary k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedInducedStarDegrees.toReflectionFixedCenterLeafBoundary k
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedInducedStarDegrees.toReflectionFixedCenterLeafBoundary k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the induced-degree wrapper to the compressed post-default-base
frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf :=
    connector.fixedInducedStarDegrees.toReflectionFixedCenterLeafBoundary
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj := connector.noAllEndpointAdj

end RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees

/-- Compressed post-default-base frontier with `fixedCenterLeaf` replaced by
the action-level reflection fixed-neighbor star-count package. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts
    (h : D19ActsOnMoore57 V Γ) where
  fixedNeighborStarCounts : ReflectionFixedNeighborStarCounts h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedNeighborStarCounts.toReflectionFixedCenterLeafBoundary k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedNeighborStarCounts.toReflectionFixedCenterLeafBoundary k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedNeighborStarCounts.toReflectionFixedCenterLeafBoundary k
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedNeighborStarCounts.toReflectionFixedCenterLeafBoundary k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the fixed-neighbor star-count wrapper to the compressed
post-default-base frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf :=
    connector.fixedNeighborStarCounts.toReflectionFixedCenterLeafBoundary
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj := connector.noAllEndpointAdj

end RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts

/-- Compressed post-default-base frontier with `fixedCenterLeaf` replaced by
explicit `K_{1,55}` packages for all reflections, plus the required condition
that `rotationFixedCenter` is not the center of those stars. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155
    (h : D19ActsOnMoore57 V Γ) where
  involutionK155 :
    ∀ k : ZMod 19, InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))
  rotationFixedCenter_ne_center :
    ∀ k : ZMod 19, h.rotationFixedCenter ≠ (involutionK155 k).center
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h)
      (h.reflectionFixedCenterLeafBoundary_of_involutionK155
        involutionK155 rotationFixedCenter_ne_center)
      k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h)
      (h.reflectionFixedCenterLeafBoundary_of_involutionK155
        involutionK155 rotationFixedCenter_ne_center)
      k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h)
      (h.reflectionFixedCenterLeafBoundary_of_involutionK155
        involutionK155 rotationFixedCenter_ne_center)
      k
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h)
      (h.reflectionFixedCenterLeafBoundary_of_involutionK155
        involutionK155 rotationFixedCenter_ne_center)
      k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the explicit `K_{1,55}` wrapper to the compressed
post-default-base frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf :=
    h.reflectionFixedCenterLeafBoundary_of_involutionK155
      connector.involutionK155
      connector.rotationFixedCenter_ne_center
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj := connector.noAllEndpointAdj

end RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155

/-- Component-level no-go for the induced fixed-star degree wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees
            h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

/-- Component-level no-go for the fixed-neighbor star-count wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts
            h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

/-- Component-level no-go for the explicit per-reflection `K_{1,55}` wrapper. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155
            h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

end

end Moore57
