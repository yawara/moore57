import Moore57.D19NonRepresentationFrontierAfterDefaultBase
import Moore57.BranchOrbitABCAFixingReflectionSupportBoundary
import Moore57.BranchOrbitABCFixedStarLocalObstructionBoundary
import Moore57.BranchOrbitABCActionLevelLocalObstructionBoundary

/-!
# Support-card frontier for the non-representation default-base package

This file keeps the post-default-base non-representation frontier unchanged,
but gives stronger connector variants in which the raw
`support_card_boundary` field is supplied by the existing fixed-star/A-fixing
packages.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

namespace ReflectionFixedStarAFixingBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h}
variable {k : ZMod 19}

/-- The fixed-star A-fixing input supplies the default-base support-card
boundary. -/
def toNonRepresentationDefaultBaseSupportCardBoundary
    (boundary :
      ReflectionFixedStarAFixingBoundary star
        (nonRepresentationDefaultBaseLabeling
          (h := h) fixedCenterLeaf k)) :
    NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedCenterLeaf k :=
  boundary.toAFixingReflectionFixedNeighborCardBoundary

end ReflectionFixedStarAFixingBoundary

end BranchOrbitABCReflectionLabeling

/-- Default-base non-representation connector with the support-card field
replaced by the fixed-star A-fixing boundary. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector
    (h : D19ActsOnMoore57 V Γ) where
  star : ReflectionFixedStarBoundary h
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  aFixing :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
      star
      (BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseLabeling
        (h := h) fixedCenterLeaf k)
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedCenterLeaf k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedCenterLeaf k
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Recover the original explicit default-base non-representation frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary :=
    connector.aFixing
      |>.toNonRepresentationDefaultBaseSupportCardBoundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj := connector.noAllEndpointAdj

/-- Collapse to the default-base fixed-center-leaf reference connector. -/
def toDefaultBaseFixedCenterLeafReferenceConnector
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h) :
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h :=
  connector.toRemainingNonRepresentationFrontierAfterDefaultBase
    |>.toDefaultBaseFixedCenterLeafReferenceConnector

/-- Collapse to the public labeled-reflection matching-equation connector. -/
def toRemainingLabeledReflectionMatchingEquationConnector
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  connector.toRemainingNonRepresentationFrontierAfterDefaultBase
    |>.toRemainingLabeledReflectionMatchingEquationConnector

end RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector

/-- Fixed-star-local variant of the default-base non-representation connector.
The local package carries A-fixing, card-one exclusion, endpoint obstruction,
and reference matching; this wrapper only pins it to the default-base labeling. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector
    (h : D19ActsOnMoore57 V Γ) where
  star : ReflectionFixedStarBoundary h
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  fixedStarLocal :
    BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
      star
      (BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseLabeling
        (h := h) fixedCenterLeaf k)

namespace RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the fixed-star-local package to the A-fixing support-card frontier. -/
def toAFixingConnector
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h where
  star := connector.star
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  aFixing := connector.fixedStarLocal.localObstruction.aFixing
  referenceMatching := connector.fixedStarLocal.referenceMatching
  no_card_one := connector.fixedStarLocal.localObstruction.singletonFixed.no_card_one
  noAllEndpointAdj := connector.fixedStarLocal.localObstruction.noAllEndpointAdj

/-- Recover the original explicit default-base non-representation frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  connector.toAFixingConnector
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

end RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector

/-- Action-level-local variant of the default-base non-representation
connector, specialized to the default-base labeling.  These are the fields of
the existing action-level local-obstruction package with `labeling` fixed to
the default-base labeling. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector
    (h : D19ActsOnMoore57 V Γ) where
  starCounts : ReflectionFixedNeighborStarCounts h
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  middle :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarMiddleBoundary
      starCounts.toReflectionFixedStarBoundary
      (BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseLabeling
        (h := h) fixedCenterLeaf k)
  aFixing :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
      starCounts.toReflectionFixedStarBoundary
      (BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseLabeling
        (h := h) fixedCenterLeaf k)
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedCenterLeaf k
  exceptionDoublingGeometry :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingGeometryBoundary
      (BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseLabeling
        (h := h) fixedCenterLeaf k)
  singletonFixed :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
      (BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseLabeling
        (h := h) fixedCenterLeaf k)
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoAllEndpointAdj
        (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector

variable {h : D19ActsOnMoore57 V Γ}

/-- Rebundle the specialized fields as the existing action-level
local-obstruction package. -/
def toActionLevelLocalObstructionBoundary
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector
        h) :
    BranchOrbitABCActionLevelLocalObstructionBoundary h where
  starCounts := connector.starCounts
  labeling :=
    BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseLabeling
      (h := h) connector.fixedCenterLeaf connector.k
  middle := connector.middle
  aFixing := connector.aFixing
  referenceMatching := connector.referenceMatching
  exceptionDoublingGeometry := connector.exceptionDoublingGeometry
  singletonFixed := connector.singletonFixed
  noAllEndpointAdj := connector.noAllEndpointAdj

/-- Forget the action-level-local package to the A-fixing support-card
frontier. -/
def toAFixingConnector
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h where
  star := connector.starCounts.toReflectionFixedStarBoundary
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  aFixing := connector.aFixing
  referenceMatching := connector.referenceMatching
  no_card_one := connector.singletonFixed.no_card_one
  noAllEndpointAdj := connector.noAllEndpointAdj

/-- Recover the original explicit default-base non-representation frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  connector.toAFixingConnector
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

end RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector

/-- Component-level no-go for the A-fixing support-card connector, via the
existing non-representation default-base frontier. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector
            h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

/-- Component-level no-go for the fixed-star-local connector. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector
            h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

/-- Component-level no-go for the action-level-local connector. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector_of_components
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        Nonempty
          (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector
            h) := by
  rintro ⟨representationComponents, ⟨connector⟩⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨representationComponents,
      ⟨connector.toRemainingNonRepresentationFrontierAfterDefaultBase⟩⟩

end

end Moore57
