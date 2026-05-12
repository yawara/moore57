import Moore57.D19OnMoore57.BranchOrbit.ABCLeanAwareFinalBoundary
import Moore57.D19OnMoore57.NoGo.NonRepresentationFrontier

/-!
# Lean-aware default-base frontier

This diagnostic file compares the current lean-aware fixed-star final package
with the compressed non-representation frontier after the default-base
reductions.

The lean-aware package already supplies the reference-matching pipeline and the
finite midpoint-exception case fields.  The compressed frontier still asks for
the endpoint-adjacency obstruction `noAllEndpointAdj` rather than the derived
`no_card_two` field, so that field remains explicit below.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Default-base labeling attached to the fixed-center-leaf boundary induced by
a fixed-star boundary. -/
noncomputable abbrev leanAwareDefaultBaseLabeling
    (star : ReflectionFixedStarBoundary h)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling h :=
  nonRepresentationDefaultBaseLabeling
    (h := h) star.toReflectionFixedCenterLeafBoundary k

/-- The lean-aware final boundary specialized to the default-base labeling
coming from the fixed star. -/
abbrev LeanAwareDefaultBaseFinalBoundary
    (star : ReflectionFixedStarBoundary h)
    (k : ZMod 19) : Prop :=
  LeanAwareFixedStarFinalBoundary star
    (leanAwareDefaultBaseLabeling (h := h) star k)

namespace LeanAwareFixedStarFinalBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The lean-aware fixed-star package already contains the generic
reference-matching pipeline: the midpoint middle boundary supplies the
criterion and support-cardinality fields, and vertex-fixed reference solutions
supply the reference-to-midpoint field. -/
noncomputable def toReferenceMatchingPipelineBoundary
    (boundary : LeanAwareFixedStarFinalBoundary star labeling) :
    ReferenceMatchingPipelineBoundary labeling :=
  (FixedStarReferenceMatchingPipelineBoundary.of_vertexFixed
    boundary.middle boundary.referenceSolutionVertexFixed)
      |>.toReferenceMatchingPipelineBoundary

/-- Repackage the lean-aware finite case fields in the midpoint-disjointness
diagnostic shape once the endpoint-adjacency obstruction is supplied. -/
noncomputable def toReferenceFiberMatchingEquationMidpointDisjointnessBoundary
    (boundary : LeanAwareFixedStarFinalBoundary star labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    ReferenceFiberMatchingEquationMidpointDisjointnessBoundary labeling where
  referenceMatching := boundary.toReferenceMatchingPipelineBoundary
  support_card_boundary :=
    boundary.midpointExceptionAFixingSupportCase.support_card_boundary
  no_card_one := boundary.midpointExceptionAFixingSupportCase.no_card_one
  noAllEndpointAdj := noAllEndpointAdj

/-- Lean-aware default-base data alone reaches the older default-base
reference frontier: the finite case package gives raw disjointness. -/
noncomputable def toRemainingDefaultBaseFixedCenterLeafReferenceConnector
    {k : ZMod 19}
    (boundary : LeanAwareDefaultBaseFinalBoundary (h := h) star k) :
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h where
  fixedCenterLeaf := star.toReflectionFixedCenterLeafBoundary
  k := k
  referenceMatching := boundary.toReferenceMatchingPipelineBoundary
  midpointExceptionDisjoint :=
    boundary.midpointExceptionAFixingSupportCase
      |>.toMidpointExceptionDisjointAFixingSupportBoundary

/-- The single extra field needed to turn a lean-aware default-base package
into the compressed non-representation frontier.  `referenceMatching`,
`support_card_boundary`, and `no_card_one` are formal consequences of the
lean-aware package. -/
structure DefaultBaseCompressedFrontierSupplement
    (star : ReflectionFixedStarBoundary h)
    (k : ZMod 19) : Prop where
  noAllEndpointAdj :
    NonRepresentationDefaultBaseNoAllEndpointAdj
      (h := h) star.toReflectionFixedCenterLeafBoundary k

namespace DefaultBaseCompressedFrontierSupplement

variable {k : ZMod 19}

/-- View the compressed-frontier supplement on the specialized default-base
labeling. -/
def toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    (supplement :
      DefaultBaseCompressedFrontierSupplement (h := h) star k) :
    MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      (leanAwareDefaultBaseLabeling (h := h) star k) :=
  supplement.noAllEndpointAdj

end DefaultBaseCompressedFrontierSupplement

/-- Lean-aware default-base package plus the endpoint-adjacency obstruction
matches the compressed post-default-base non-representation frontier. -/
noncomputable def toRemainingNonRepresentationFrontierAfterDefaultBase
    {k : ZMod 19}
    (boundary : LeanAwareDefaultBaseFinalBoundary (h := h) star k)
    (supplement :
      DefaultBaseCompressedFrontierSupplement (h := h) star k) :
    RemainingNonRepresentationFrontierAfterDefaultBase h where
  fixedCenterLeaf := star.toReflectionFixedCenterLeafBoundary
  k := k
  referenceMatching := boundary.toReferenceMatchingPipelineBoundary
  support_card_boundary :=
    boundary.midpointExceptionAFixingSupportCase.support_card_boundary
  no_card_one := boundary.midpointExceptionAFixingSupportCase.no_card_one
  noAllEndpointAdj := supplement.noAllEndpointAdj

end LeanAwareFixedStarFinalBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
