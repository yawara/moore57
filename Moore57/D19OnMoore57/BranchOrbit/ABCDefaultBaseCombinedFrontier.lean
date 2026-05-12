import Moore57.D19OnMoore57.BranchOrbit.ABCSupportCardFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCNoCardOneFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCNoAllEndpointAdjFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCLeanAwareDefaultBaseFrontier

/-!
# Combined default-base compressed frontier wrappers

This file adds only packaging.  It combines the field-replacement frontiers for
support-cardinality, no-card-one, endpoint obstruction, and lean-aware
default-base data into practical default-base wrappers, each with a forgetful
map to `RemainingNonRepresentationFrontierAfterDefaultBase`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- A compact endpoint-obstruction supplement for the default-base compressed
frontier.  The constructors below are exactly the existing endpoint-frontier
conversions repackaged under one stable name. -/
structure NonRepresentationDefaultBaseEndpointObstructionSupplement
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop where
  noAllEndpointAdj :
    NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedCenterLeaf k

namespace NonRepresentationDefaultBaseEndpointObstructionSupplement

variable {fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h}
variable {k : ZMod 19}

/-- Repackage an already-compressed endpoint obstruction. -/
def of_noAllEndpointAdj
    (noAllEndpointAdj :
      NonRepresentationDefaultBaseNoAllEndpointAdj
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseEndpointObstructionSupplement
      (h := h) fixedCenterLeaf k where
  noAllEndpointAdj := noAllEndpointAdj

/-- Endpoint non-adjacency witness route to the endpoint supplement. -/
def of_endpointNonadjWitness
    (boundary :
      NonRepresentationDefaultBaseEndpointNonadjWitnessBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseEndpointObstructionSupplement
      (h := h) fixedCenterLeaf k where
  noAllEndpointAdj :=
    nonRepresentationDefaultBaseNoAllEndpointAdj_of_endpointNonadjWitness
      boundary

/-- Pointwise endpoint non-adjacency route to the endpoint supplement. -/
def of_endpointPointwiseNonadj
    (supportCard :
      NonRepresentationDefaultBaseSupportCardBoundary
        (h := h) fixedCenterLeaf k)
    (boundary :
      NonRepresentationDefaultBaseEndpointPointwiseNonadjBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseEndpointObstructionSupplement
      (h := h) fixedCenterLeaf k where
  noAllEndpointAdj :=
    nonRepresentationDefaultBaseNoAllEndpointAdj_of_endpointPointwiseNonadj
      supportCard boundary

/-- Endpoint-adjacency-forces-fixed route to the endpoint supplement. -/
def of_endpointAdjForcesAFixingFixed
    (supportCard :
      NonRepresentationDefaultBaseSupportCardBoundary
        (h := h) fixedCenterLeaf k)
    (boundary :
      NonRepresentationDefaultBaseEndpointAdjForcesAFixingFixedBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseEndpointObstructionSupplement
      (h := h) fixedCenterLeaf k where
  noAllEndpointAdj :=
    nonRepresentationDefaultBaseNoAllEndpointAdj_of_endpointAdjForcesAFixingFixed
      supportCard boundary

/-- Vertex-fixed endpoint-adjacency route to the endpoint supplement. -/
def of_endpointAdjForcesAFixingVertexFixed
    (supportCard :
      NonRepresentationDefaultBaseSupportCardBoundary
        (h := h) fixedCenterLeaf k)
    (boundary :
      NonRepresentationDefaultBaseEndpointAdjForcesAFixingVertexFixedBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseEndpointObstructionSupplement
      (h := h) fixedCenterLeaf k where
  noAllEndpointAdj :=
    nonRepresentationDefaultBaseNoAllEndpointAdj_of_endpointAdjForcesAFixingVertexFixed
      supportCard boundary

/-- Pair endpoint non-adjacency route to the endpoint supplement. -/
def of_pairEndpointNonadj
    (supportCard :
      NonRepresentationDefaultBaseSupportCardBoundary
        (h := h) fixedCenterLeaf k)
    (boundary :
      NonRepresentationDefaultBasePairEndpointNonadjBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseEndpointObstructionSupplement
      (h := h) fixedCenterLeaf k where
  noAllEndpointAdj :=
    nonRepresentationDefaultBaseNoAllEndpointAdj_of_pairEndpointNonadj
      supportCard boundary

/-- Pair common-neighbor route to the endpoint supplement. -/
def of_pairEndpointTwoCommonNeighbors
    (supportCard :
      NonRepresentationDefaultBaseSupportCardBoundary
        (h := h) fixedCenterLeaf k)
    (boundary :
      NonRepresentationDefaultBasePairEndpointTwoCommonNeighborsBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseEndpointObstructionSupplement
      (h := h) fixedCenterLeaf k where
  noAllEndpointAdj :=
    nonRepresentationDefaultBaseNoAllEndpointAdj_of_pairEndpointTwoCommonNeighbors
      supportCard boundary

end NonRepresentationDefaultBaseEndpointObstructionSupplement

namespace LeanAwareFixedStarFinalBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {k : ZMod 19}

/-- Convert the fixed-center-leaf endpoint supplement to the lean-aware
compressed-frontier supplement. -/
def defaultBaseCompressedSupplement_of_endpointObstruction
    (endpointObstruction :
      NonRepresentationDefaultBaseEndpointObstructionSupplement
        (h := h) star.toReflectionFixedCenterLeafBoundary k) :
    DefaultBaseCompressedFrontierSupplement (h := h) star k where
  noAllEndpointAdj := endpointObstruction.noAllEndpointAdj

end LeanAwareFixedStarFinalBoundary

end BranchOrbitABCReflectionLabeling

/-- Lean-aware default-base data plus an endpoint-obstruction supplement
collapses to the compressed post-default-base frontier. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction
    (h : D19ActsOnMoore57 V Γ) where
  star : ReflectionFixedStarBoundary h
  k : ZMod 19
  leanAware :
    BranchOrbitABCReflectionLabeling.LeanAwareDefaultBaseFinalBoundary
      (h := h) star k
  endpointObstruction :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseEndpointObstructionSupplement
      (h := h) star.toReflectionFixedCenterLeafBoundary k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction

variable {h : D19ActsOnMoore57 V Γ}

/-- Recover the original explicit default-base non-representation frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  connector.leanAware.toRemainingNonRepresentationFrontierAfterDefaultBase
    (BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary.defaultBaseCompressedSupplement_of_endpointObstruction
      connector.endpointObstruction)

end RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction

/-- A-fixing support plus singleton-fixed no-card-one and endpoint obstruction
collapses to the compressed post-default-base frontier. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction
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
  singletonFixed :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSingletonFixedBoundary
      (h := h) fixedCenterLeaf k
  endpointObstruction :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseEndpointObstructionSupplement
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget to the existing A-fixing support-card connector. -/
def toAFixingConnector
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h where
  star := connector.star
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  aFixing := connector.aFixing
  referenceMatching := connector.referenceMatching
  no_card_one :=
    BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseNoCardOne_of_singletonFixed
        connector.singletonFixed
  noAllEndpointAdj := connector.endpointObstruction.noAllEndpointAdj

/-- Recover the original explicit default-base non-representation frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  connector.toAFixingConnector
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

end RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction

/-- A-fixing support plus doubling no-card-one and endpoint obstruction
collapses to the compressed post-default-base frontier. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction
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
  doublingNoCardOne :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseDoublingNoCardOneWitness
      (h := h) fixedCenterLeaf k
  endpointObstruction :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseEndpointObstructionSupplement
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget to the existing A-fixing support-card connector. -/
def toAFixingConnector
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h where
  star := connector.star
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  aFixing := connector.aFixing
  referenceMatching := connector.referenceMatching
  no_card_one := connector.doublingNoCardOne.no_card_one
  noAllEndpointAdj := connector.endpointObstruction.noAllEndpointAdj

/-- Recover the original explicit default-base non-representation frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  connector.toAFixingConnector
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

end RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction

/-- Fixed-star local fields with the endpoint obstruction supplied through the
combined supplement. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction
    (h : D19ActsOnMoore57 V Γ) where
  star : ReflectionFixedStarBoundary h
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  middle :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarMiddleBoundary
      star
      (BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseLabeling
        (h := h) fixedCenterLeaf k)
  aFixing :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
      star
      (BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseLabeling
        (h := h) fixedCenterLeaf k)
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedCenterLeaf k
  singletonFixed :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSingletonFixedBoundary
      (h := h) fixedCenterLeaf k
  endpointObstruction :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseEndpointObstructionSupplement
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction

variable {h : D19ActsOnMoore57 V Γ}

/-- Rebundle the split local fields as the existing fixed-star local
obstruction boundary. -/
def toFixedStarLocalObstructionBoundary
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction
        h) :
    BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
      connector.star
      (BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseLabeling
        (h := h) connector.fixedCenterLeaf connector.k) where
  middle := connector.middle
  referenceMatching := connector.referenceMatching
  localObstruction :=
    { aFixing := connector.aFixing
      singletonFixed := connector.singletonFixed
      noAllEndpointAdj := connector.endpointObstruction.noAllEndpointAdj }

/-- Forget to the combined A-fixing/singleton/endpoint wrapper. -/
def toAFixingSingletonEndpointObstruction
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction
      h where
  star := connector.star
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  aFixing := connector.aFixing
  referenceMatching := connector.referenceMatching
  singletonFixed := connector.singletonFixed
  endpointObstruction := connector.endpointObstruction

/-- Recover the original explicit default-base non-representation frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  connector.toAFixingSingletonEndpointObstruction
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

end RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction

/-- Action-level local fields, specialized to the default-base labeling, with
the endpoint obstruction supplied through the combined supplement. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction
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
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSingletonFixedBoundary
      (h := h) fixedCenterLeaf k
  endpointObstruction :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseEndpointObstructionSupplement
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction

variable {h : D19ActsOnMoore57 V Γ}

/-- Rebundle the split fields as the existing action-level local obstruction
boundary. -/
def toActionLevelLocalObstructionBoundary
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction
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
  noAllEndpointAdj := connector.endpointObstruction.noAllEndpointAdj

/-- Forget to the combined A-fixing/singleton/endpoint wrapper. -/
def toAFixingSingletonEndpointObstruction
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction
      h where
  star := connector.starCounts.toReflectionFixedStarBoundary
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  aFixing := connector.aFixing
  referenceMatching := connector.referenceMatching
  singletonFixed := connector.singletonFixed
  endpointObstruction := connector.endpointObstruction

/-- Recover the original explicit default-base non-representation frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  connector.toAFixingSingletonEndpointObstruction
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

end RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction

/-- Action-level support with geometric doubling, one nonzero cardinality
witness, and endpoint obstruction. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction
    (h : D19ActsOnMoore57 V Γ) where
  starCounts : ReflectionFixedNeighborStarCounts h
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
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
  base : ZMod 19
  hbase : base ≠ 0
  base_card_ne_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseBaseCardNeOne
      (h := h) fixedCenterLeaf k base hbase
  endpointObstruction :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseEndpointObstructionSupplement
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction

variable {h : D19ActsOnMoore57 V Γ}

/-- Package the action-level geometric doubling field as the default-base
doubling no-card-one witness. -/
def toDoublingNoCardOneWitness
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction
        h) :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseDoublingNoCardOneWitness
      (h := h) connector.fixedCenterLeaf connector.k where
  doubling := connector.exceptionDoublingGeometry.toMidpointExceptionDoublingBoundary
  base := connector.base
  hbase := connector.hbase
  base_card_ne_one := connector.base_card_ne_one

/-- Forget to the combined A-fixing/doubling/endpoint wrapper. -/
def toAFixingDoublingEndpointObstruction
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction
      h where
  star := connector.starCounts.toReflectionFixedStarBoundary
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  aFixing := connector.aFixing
  referenceMatching := connector.referenceMatching
  doublingNoCardOne := connector.toDoublingNoCardOneWitness
  endpointObstruction := connector.endpointObstruction

/-- Recover the original explicit default-base non-representation frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  connector.toAFixingDoublingEndpointObstruction
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

end RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction

end

end Moore57
