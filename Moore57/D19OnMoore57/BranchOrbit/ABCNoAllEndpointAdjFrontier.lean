import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontierAfterDefaultBase
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionEndpointWitnessBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionEndpointPointwiseBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCEndpointCommonNeighborBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCSupportPairEndpointBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCSupportPairCommonNeighborBoundary

/-!
# Default-base no-all-endpoint-adjacency frontier

This file isolates the `noAllEndpointAdj` field of the compressed
post-default-base non-representation frontier and records stable default-base
conversions from the existing endpoint-obstruction packages.

No new combinatorial proof is introduced here.  The conversions are
specializations of the already available witness, pointwise, endpoint-forces-
fixed, pair non-adjacency, and pair common-neighbor connectors to the
default-base fixed-center-leaf labeling.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Stable alias for the endpoint non-adjacency witness boundary at the
default-base labeling. -/
abbrev NonRepresentationDefaultBaseEndpointNonadjWitnessBoundary
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary
    (nonRepresentationDefaultBaseLabeling (h := h) fixedCenterLeaf k)

/-- Stable alias for pointwise endpoint non-adjacency at the default-base
labeling. -/
abbrev NonRepresentationDefaultBaseEndpointPointwiseNonadjBoundary
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
    (nonRepresentationDefaultBaseLabeling (h := h) fixedCenterLeaf k)

/-- Stable alias for the endpoint-adjacency-implies-A-fixing-fixedness
boundary at the default-base labeling. -/
abbrev NonRepresentationDefaultBaseEndpointAdjForcesAFixingFixedBoundary
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  MidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    (nonRepresentationDefaultBaseLabeling (h := h) fixedCenterLeaf k)

/-- Stable alias for the vertex-fixed spelling of the endpoint-adjacency
common-neighbor contradiction at the default-base labeling. -/
abbrev NonRepresentationDefaultBaseEndpointAdjForcesAFixingVertexFixedBoundary
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  MidpointExceptionEndpointAdjForcesAFixingVertexFixedBoundary
    (nonRepresentationDefaultBaseLabeling (h := h) fixedCenterLeaf k)

/-- Stable alias for pair endpoint non-adjacency at the default-base labeling. -/
abbrev NonRepresentationDefaultBasePairEndpointNonadjBoundary
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  MidpointExceptionAFixingSupportPairEndpointNonadjBoundary
    (nonRepresentationDefaultBaseLabeling (h := h) fixedCenterLeaf k)

/-- Stable alias for the pair common-neighbor endpoint obstruction at the
default-base labeling. -/
abbrev NonRepresentationDefaultBasePairEndpointTwoCommonNeighborsBoundary
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  MidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary
    (nonRepresentationDefaultBaseLabeling (h := h) fixedCenterLeaf k)

/-- The existing default-base no-all-endpoint-adjacency package is exactly the
compressed frontier's `noAllEndpointAdj` field. -/
theorem nonRepresentationDefaultBaseNoAllEndpointAdj_of_noAllEndpointAdjBoundary
    {fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h}
    {k : ZMod 19}
    (boundary :
      NonRepresentationDefaultBaseNoAllEndpointAdj
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedCenterLeaf k :=
  boundary

/-- An endpoint non-adjacency witness supplies the compressed frontier's
default-base `noAllEndpointAdj` field. -/
theorem nonRepresentationDefaultBaseNoAllEndpointAdj_of_endpointNonadjWitness
    {fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h}
    {k : ZMod 19}
    (boundary :
      NonRepresentationDefaultBaseEndpointNonadjWitnessBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedCenterLeaf k :=
  boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary

/-- Pointwise endpoint non-adjacency, together with the existing support-card
boundary, supplies the compressed frontier's default-base
`noAllEndpointAdj` field. -/
theorem nonRepresentationDefaultBaseNoAllEndpointAdj_of_endpointPointwiseNonadj
    {fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h}
    {k : ZMod 19}
    (supportCard :
      NonRepresentationDefaultBaseSupportCardBoundary
        (h := h) fixedCenterLeaf k)
    (boundary :
      NonRepresentationDefaultBaseEndpointPointwiseNonadjBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedCenterLeaf k :=
  boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    supportCard

/-- The contradiction-style endpoint boundary supplies the compressed
frontier's default-base `noAllEndpointAdj` field once the support-card
boundary is available. -/
theorem nonRepresentationDefaultBaseNoAllEndpointAdj_of_endpointAdjForcesAFixingFixed
    {fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h}
    {k : ZMod 19}
    (supportCard :
      NonRepresentationDefaultBaseSupportCardBoundary
        (h := h) fixedCenterLeaf k)
    (boundary :
      NonRepresentationDefaultBaseEndpointAdjForcesAFixingFixedBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedCenterLeaf k :=
  boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    supportCard

/-- The vertex-fixed endpoint boundary supplies the compressed frontier's
default-base `noAllEndpointAdj` field once the support-card boundary is
available. -/
theorem nonRepresentationDefaultBaseNoAllEndpointAdj_of_endpointAdjForcesAFixingVertexFixed
    {fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h}
    {k : ZMod 19}
    (supportCard :
      NonRepresentationDefaultBaseSupportCardBoundary
        (h := h) fixedCenterLeaf k)
    (boundary :
      NonRepresentationDefaultBaseEndpointAdjForcesAFixingVertexFixedBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedCenterLeaf k :=
  boundary.toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    |>.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      supportCard

/-- Pair endpoint non-adjacency supplies the compressed frontier's
default-base `noAllEndpointAdj` field in the card-two support package. -/
theorem nonRepresentationDefaultBaseNoAllEndpointAdj_of_pairEndpointNonadj
    {fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h}
    {k : ZMod 19}
    (supportCard :
      NonRepresentationDefaultBaseSupportCardBoundary
        (h := h) fixedCenterLeaf k)
    (boundary :
      NonRepresentationDefaultBasePairEndpointNonadjBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedCenterLeaf k :=
  boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    supportCard

/-- The pair common-neighbor endpoint obstruction supplies the compressed
frontier's default-base `noAllEndpointAdj` field in the card-two support
package. -/
theorem nonRepresentationDefaultBaseNoAllEndpointAdj_of_pairEndpointTwoCommonNeighbors
    {fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h}
    {k : ZMod 19}
    (supportCard :
      NonRepresentationDefaultBaseSupportCardBoundary
        (h := h) fixedCenterLeaf k)
    (boundary :
      NonRepresentationDefaultBasePairEndpointTwoCommonNeighborsBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedCenterLeaf k :=
  boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    supportCard

end BranchOrbitABCReflectionLabeling

/-- Compressed post-default-base frontier with `noAllEndpointAdj` replaced by
the existing endpoint non-adjacency witness package. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness
    (h : D19ActsOnMoore57 V Γ) where
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedCenterLeaf k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedCenterLeaf k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedCenterLeaf k
  endpointNonadjWitness :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseEndpointNonadjWitnessBoundary
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the endpoint-witness diagnostic wrapper to the compressed
post-default-base frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj :=
    BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseNoAllEndpointAdj_of_endpointNonadjWitness
      connector.endpointNonadjWitness

end RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness

/-- Compressed post-default-base frontier with `noAllEndpointAdj` replaced by
the existing pointwise endpoint non-adjacency package. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj
    (h : D19ActsOnMoore57 V Γ) where
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedCenterLeaf k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedCenterLeaf k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedCenterLeaf k
  endpointPointwiseNonadj :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseEndpointPointwiseNonadjBoundary
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the pointwise endpoint diagnostic wrapper to the compressed
post-default-base frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj :=
    BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseNoAllEndpointAdj_of_endpointPointwiseNonadj
      connector.support_card_boundary connector.endpointPointwiseNonadj

end RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj

/-- Compressed post-default-base frontier with `noAllEndpointAdj` replaced by
the contradiction-style endpoint-forces-fixed package. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed
    (h : D19ActsOnMoore57 V Γ) where
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedCenterLeaf k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedCenterLeaf k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedCenterLeaf k
  endpointAdjForcesAFixingFixed :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseEndpointAdjForcesAFixingFixedBoundary
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the endpoint-forces-fixed diagnostic wrapper to the compressed
post-default-base frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj :=
    BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseNoAllEndpointAdj_of_endpointAdjForcesAFixingFixed
      connector.support_card_boundary connector.endpointAdjForcesAFixingFixed

end RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed

/-- Compressed post-default-base frontier with `noAllEndpointAdj` replaced by
the vertex-fixed spelling of the endpoint-forces-fixed package. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed
    (h : D19ActsOnMoore57 V Γ) where
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedCenterLeaf k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedCenterLeaf k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedCenterLeaf k
  endpointAdjForcesAFixingVertexFixed :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseEndpointAdjForcesAFixingVertexFixedBoundary
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the vertex-fixed endpoint diagnostic wrapper to the compressed
post-default-base frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj :=
    BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseNoAllEndpointAdj_of_endpointAdjForcesAFixingVertexFixed
      connector.support_card_boundary
      connector.endpointAdjForcesAFixingVertexFixed

end RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed

/-- Compressed post-default-base frontier with `noAllEndpointAdj` replaced by
the existing pair endpoint non-adjacency package. -/
structure RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj
    (h : D19ActsOnMoore57 V Γ) where
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedCenterLeaf k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedCenterLeaf k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedCenterLeaf k
  pairEndpointNonadj :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBasePairEndpointNonadjBoundary
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the pair endpoint diagnostic wrapper to the compressed
post-default-base frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj :=
    BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseNoAllEndpointAdj_of_pairEndpointNonadj
      connector.support_card_boundary connector.pairEndpointNonadj

end RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj

/-- Compressed post-default-base frontier with `noAllEndpointAdj` replaced by
the pair common-neighbor endpoint obstruction. -/
structure RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors
    (h : D19ActsOnMoore57 V Γ) where
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedCenterLeaf k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedCenterLeaf k
  no_card_one :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedCenterLeaf k
  pairEndpointTwoCommonNeighbors :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBasePairEndpointTwoCommonNeighborsBoundary
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the pair common-neighbor diagnostic wrapper to the compressed
post-default-base frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors
        h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.no_card_one
  noAllEndpointAdj :=
    BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseNoAllEndpointAdj_of_pairEndpointTwoCommonNeighbors
      connector.support_card_boundary
      connector.pairEndpointTwoCommonNeighbors

end RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors

end

end Moore57
