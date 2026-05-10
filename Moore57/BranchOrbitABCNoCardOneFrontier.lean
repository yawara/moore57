import Moore57.D19NonRepresentationFrontierAfterDefaultBase
import Moore57.BranchOrbitABCExceptionCardOneBoundary
import Moore57.BranchOrbitABCExceptionDoublingBoundary

/-!
# Default-base no-card-one frontier

This file isolates the `no_card_one` field of the compressed
post-default-base non-representation frontier and records stable default-base
conversions from the existing singleton-fixed and doubling packages.

It adds no new mathematical input: the conversions are specializations of
`MidpointExceptionAFixingSupportSingletonFixedBoundary.no_card_one` and
`MidpointExceptionDoublingBoundary.no_card_one_of_card_ne_one` to the
default-base fixed-center-leaf labeling.
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

end BranchOrbitABCReflectionLabeling

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

end

end Moore57
