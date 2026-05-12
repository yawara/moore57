import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontier
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCardOneBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionDoublingBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionEndpointWitnessBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionEndpointPointwiseBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCEndpointCommonNeighborBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCSupportPairEndpointBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCSupportPairCommonNeighborBoundary

/-!
# Default-base no-card-one and no-all-endpoint-adjacency frontiers

This file unifies the `no_card_one` and `noAllEndpointAdj` field connectors of
the compressed post-default-base non-representation frontier.  Two themes are
covered:

* The `no_card_one` field, with conversions from the existing singleton-fixed
  and doubling packages.
* The `noAllEndpointAdj` field, with conversions from the existing endpoint
  witness, pointwise, endpoint-forces-fixed (object and vertex variants), pair
  non-adjacency, and pair common-neighbor packages.

No new mathematical input is introduced: the conversions are specializations
of already available boundary packages to the default-base fixed-center-leaf
labeling.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instNoCardOneFrontierPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instNoCardOneFrontierDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-! ## `no_card_one` connectors -/

/-- Stable alias for the no-singleton boundary at the default-base labeling. -/
abbrev NonRepresentationDefaultBaseNoCardOneBoundary
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  MidpointExceptionAFixingSupportNoCardOneBoundary
    (nonRepresentationDefaultBaseLabeling (h := h) fixedCenterLeaf k)

/-- Stable alias for singleton-fixedness at the default-base labeling. -/
abbrev NonRepresentationDefaultBaseSingletonFixedBoundary
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  MidpointExceptionAFixingSupportSingletonFixedBoundary
    (nonRepresentationDefaultBaseLabeling (h := h) fixedCenterLeaf k)

/-- Stable alias for doubling propagation at the default-base labeling. -/
abbrev NonRepresentationDefaultBaseDoublingBoundary
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) : Prop :=
  MidpointExceptionDoublingBoundary
    (nonRepresentationDefaultBaseLabeling (h := h) fixedCenterLeaf k)

/-- Stable alias for a single default-base nonzero cardinality witness used by
the doubling package to propagate `card ≠ 1` to every offset. -/
abbrev NonRepresentationDefaultBaseBaseCardNeOne
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19)
    (base : ZMod 19) (hbase : base ≠ 0) : Prop :=
  ((nonRepresentationDefaultBaseLabeling
      (h := h) fixedCenterLeaf k).midpointExceptionAFixingSupportIntersection
    base hbase).card ≠ 1

/-- A default-base no-singleton boundary supplies the `no_card_one` field of
the compressed frontier. -/
theorem nonRepresentationDefaultBaseNoCardOne_of_noCardOneBoundary
    {fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h}
    {k : ZMod 19}
    (boundary :
      NonRepresentationDefaultBaseNoCardOneBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedCenterLeaf k :=
  boundary.no_card_one

/-- Singleton-fixedness supplies the `no_card_one` field of the compressed
default-base frontier. -/
theorem nonRepresentationDefaultBaseNoCardOne_of_singletonFixed
    {fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h}
    {k : ZMod 19}
    (boundary :
      NonRepresentationDefaultBaseSingletonFixedBoundary
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedCenterLeaf k :=
  boundary.no_card_one

/-- Doubling propagation plus one nonzero `card ≠ 1` witness supplies the
`no_card_one` field of the compressed default-base frontier. -/
theorem nonRepresentationDefaultBaseNoCardOne_of_doubling_card_ne_one
    {fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h}
    {k : ZMod 19}
    (doubling :
      NonRepresentationDefaultBaseDoublingBoundary
        (h := h) fixedCenterLeaf k)
    {base : ZMod 19} (hbase : base ≠ 0)
    (hne_one :
      NonRepresentationDefaultBaseBaseCardNeOne
        (h := h) fixedCenterLeaf k base hbase) :
    NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedCenterLeaf k :=
  doubling.no_card_one_of_card_ne_one hbase hne_one

/-- Data package for the doubling route to the default-base `no_card_one`
field.  The `base` field is intentionally explicit because doubling only
propagates an already-known nonzero cardinality exclusion. -/
structure NonRepresentationDefaultBaseDoublingNoCardOneWitness
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (k : ZMod 19) where
  doubling :
    NonRepresentationDefaultBaseDoublingBoundary
      (h := h) fixedCenterLeaf k
  base : ZMod 19
  hbase : base ≠ 0
  base_card_ne_one :
    NonRepresentationDefaultBaseBaseCardNeOne
      (h := h) fixedCenterLeaf k base hbase

namespace NonRepresentationDefaultBaseDoublingNoCardOneWitness

variable {fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h}
variable {k : ZMod 19}

/-- Collapse the doubling witness package to the compressed frontier's
`no_card_one` field. -/
theorem no_card_one
    (witness :
      NonRepresentationDefaultBaseDoublingNoCardOneWitness
        (h := h) fixedCenterLeaf k) :
    NonRepresentationDefaultBaseNoCardOne
      (h := h) fixedCenterLeaf k :=
  nonRepresentationDefaultBaseNoCardOne_of_doubling_card_ne_one
    witness.doubling witness.hbase witness.base_card_ne_one

end NonRepresentationDefaultBaseDoublingNoCardOneWitness

/-! ## `noAllEndpointAdj` connectors -/

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

/-! ## Compressed-frontier wrappers (singleton-fixed and doubling) -/

/-- Compressed post-default-base frontier with `no_card_one` replaced by the
existing singleton-fixed package. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseSingletonFixed
    (h : D19ActsOnMoore57 V Γ) where
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedCenterLeaf k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedCenterLeaf k
  singletonFixed :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSingletonFixedBoundary
      (h := h) fixedCenterLeaf k
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseSingletonFixed

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the singleton-fixed diagnostic wrapper to the compressed
post-default-base frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseSingletonFixed h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one :=
    BranchOrbitABCReflectionLabeling.nonRepresentationDefaultBaseNoCardOne_of_singletonFixed
      connector.singletonFixed
  noAllEndpointAdj := connector.noAllEndpointAdj

/-- Rebundle the singleton-fixed wrapper as the finite midpoint-disjointness
diagnostic package. -/
def toMidpointDisjointnessBoundary
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseSingletonFixed h) :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseMidpointDisjointnessBoundary
      (h := h) connector.fixedCenterLeaf connector.k :=
  connector.toRemainingNonRepresentationFrontierAfterDefaultBase
    |>.toMidpointDisjointnessBoundary

end RemainingNonRepresentationFrontierAfterDefaultBaseSingletonFixed

/-- Compressed post-default-base frontier with `no_card_one` replaced by the
existing doubling package plus one nonzero cardinality witness. -/
structure RemainingNonRepresentationFrontierAfterDefaultBaseDoubling
    (h : D19ActsOnMoore57 V Γ) where
  fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h
  k : ZMod 19
  referenceMatching :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseReferenceMatching
      (h := h) fixedCenterLeaf k
  support_card_boundary :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseSupportCardBoundary
      (h := h) fixedCenterLeaf k
  doublingNoCardOne :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseDoublingNoCardOneWitness
      (h := h) fixedCenterLeaf k
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) fixedCenterLeaf k

namespace RemainingNonRepresentationFrontierAfterDefaultBaseDoubling

variable {h : D19ActsOnMoore57 V Γ}

/-- Collapse the doubling diagnostic wrapper to the compressed
post-default-base frontier. -/
def toRemainingNonRepresentationFrontierAfterDefaultBase
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseDoubling h) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf := connector.fixedCenterLeaf
  k := connector.k
  referenceMatching := connector.referenceMatching
  support_card_boundary := connector.support_card_boundary
  no_card_one := connector.doublingNoCardOne.no_card_one
  noAllEndpointAdj := connector.noAllEndpointAdj

/-- Rebundle the doubling wrapper as the finite midpoint-disjointness
diagnostic package. -/
def toMidpointDisjointnessBoundary
    (connector :
      RemainingNonRepresentationFrontierAfterDefaultBaseDoubling h) :
    BranchOrbitABCReflectionLabeling.NonRepresentationDefaultBaseMidpointDisjointnessBoundary
      (h := h) connector.fixedCenterLeaf connector.k :=
  connector.toRemainingNonRepresentationFrontierAfterDefaultBase
    |>.toMidpointDisjointnessBoundary

end RemainingNonRepresentationFrontierAfterDefaultBaseDoubling

/-! ## Compressed-frontier wrappers (endpoint-non-adjacency variants) -/

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
