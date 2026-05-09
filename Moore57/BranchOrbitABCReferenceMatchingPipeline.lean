import Moore57.BranchOrbitABCReferenceSolutionFixedBoundary
import Moore57.BranchOrbitABCReflectionFixedStarBoundary

/-!
# Branch-orbit reference matching pipeline

This file contains only wiring lemmas: it packages the existing midpoint
reflection boundaries into the reference matching exception-set boundary, then
feeds that boundary to the full A-fiber cardinality constructor.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instReferenceMatchingPipelinePFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instReferenceMatchingPipelineDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The current midpoint/reflection hypotheses needed to build the reference
matching exception-set boundary for the labeled branch data. -/
structure ReferenceMatchingPipelineBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  criterion : MidpointReflectionCriterionBoundary labeling
  midpointSupportCardTwo : MidpointMiddleSupportCardTwoBoundary labeling
  referenceToMidpoint : ReferenceRotationToMidpointReflectionBoundary labeling

namespace ReferenceMatchingPipelineBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Collapse the midpoint/reflection boundary package to the existing reference
matching exception-set boundary for `labeling.data.toAFiberRotationEquivariance`. -/
noncomputable def toReferenceFiberMatchingExceptionSetTwo
    (boundary : ReferenceMatchingPipelineBoundary labeling) :
    ReferenceFiberMatchingExceptionSetTwo
      labeling.data.toAFiberRotationEquivariance :=
  ReferenceFiberMatchingExceptionSetTwo.of_midpointReflectionBoundary
    labeling boundary.criterion boundary.midpointSupportCardTwo
    boundary.referenceToMidpoint

end ReferenceMatchingPipelineBoundary

/-- Direct convenience wrapper for the common unbundled inputs. -/
noncomputable def toReferenceFiberMatchingExceptionSetTwo
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (cardTwo : MidpointMiddleSupportCardTwoBoundary labeling)
    (rhs : ReferenceRotationToMidpointReflectionBoundary labeling) :
    ReferenceFiberMatchingExceptionSetTwo
      labeling.data.toAFiberRotationEquivariance :=
  ReferenceFiberMatchingExceptionSetTwo.of_midpointReflectionBoundary
    labeling criterion cardTwo rhs

/-- Fixed-star/reflection inputs in the form that now feeds the reference
matching pipeline.  The remaining geometric content is explicit:
the midpoint middle A-vertex is the fixed-star center, and reference solutions
are fixed by the A-fixing reflection. -/
structure FixedStarReferenceMatchingPipelineBoundary
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  middle : ReflectionFixedStarMiddleBoundary star labeling
  referenceSolutionFixed : ReferenceRotationEquationAFixingFixedBoundary labeling

namespace FixedStarReferenceMatchingPipelineBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Build the fixed-star reference matching package from the more geometric
statement that reference matching solutions are fixed as vertices in the
reference A-fiber. -/
noncomputable def of_vertexFixed
    (middle : ReflectionFixedStarMiddleBoundary star labeling)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling) :
    FixedStarReferenceMatchingPipelineBoundary star labeling where
  middle := middle
  referenceSolutionFixed :=
    referenceSolutionVertexFixed.toReferenceRotationEquationAFixingFixedBoundary

/-- Convert the fixed-star version of the midpoint/reflection inputs to the
generic reference matching pipeline boundary. -/
noncomputable def toReferenceMatchingPipelineBoundary
    (boundary : FixedStarReferenceMatchingPipelineBoundary star labeling) :
    ReferenceMatchingPipelineBoundary labeling where
  criterion :=
    labeling.midpointReflectionCriterionBoundary_of_fixedCenterLeaf
      star.toReflectionFixedCenterLeafBoundary
  midpointSupportCardTwo :=
    boundary.middle.toMidpointMiddleFixedNeighborCardBoundary
      |>.toMidpointMiddleSupportCardTwoBoundary
  referenceToMidpoint :=
    ReferenceRotationToMidpointReflectionBoundary.of_aFixingFixed
      boundary.referenceSolutionFixed

/-- The fixed-star inputs give the two-point reference exception-set boundary. -/
noncomputable def toReferenceFiberMatchingExceptionSetTwo
    (boundary : FixedStarReferenceMatchingPipelineBoundary star labeling) :
    ReferenceFiberMatchingExceptionSetTwo
      labeling.data.toAFiberRotationEquivariance :=
  boundary.toReferenceMatchingPipelineBoundary
    |>.toReferenceFiberMatchingExceptionSetTwo

end FixedStarReferenceMatchingPipelineBoundary

/-- Pipeline inputs for the full A-fiber cardinality boundary.  The final
`supportCompl_sum_ge` field is the lower-bound input required by
`AFiberCardinality38Boundary.of_allFibers_referenceMatchingExceptionSetTwo_of_sum_ge`. -/
structure ReferenceMatchingCardinalityPipelineBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  referenceMatching : ReferenceMatchingPipelineBoundary labeling
  supportCompl_sum_ge :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      38 ≤
        ∑ i ∈ (Finset.univ : Finset (ZMod 19)),
          (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
            d i hd).supportᶜ.card

namespace ReferenceMatchingCardinalityPipelineBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Expose the intermediate reference matching exception-set boundary from the
cardinality pipeline package. -/
noncomputable def toReferenceFiberMatchingExceptionSetTwo
    (boundary : ReferenceMatchingCardinalityPipelineBoundary labeling) :
    ReferenceFiberMatchingExceptionSetTwo
      labeling.data.toAFiberRotationEquivariance :=
  boundary.referenceMatching.toReferenceFiberMatchingExceptionSetTwo

/-- Feed the packaged reference matching exception-set boundary and sum lower
bound into the existing full-A-fiber cardinality constructor. -/
noncomputable def toAFiberCardinality38Boundary
    (boundary : ReferenceMatchingCardinalityPipelineBoundary labeling) :
  AFiberCardinality38Boundary h labeling.data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  AFiberCardinality38Boundary.of_allFibers_referenceMatchingExceptionSetTwo_of_sum_ge
    labeling.data.toAFiberRotationEquivariance
    boundary.toReferenceFiberMatchingExceptionSetTwo
    boundary.supportCompl_sum_ge

end ReferenceMatchingCardinalityPipelineBoundary

/-- Direct convenience wrapper from the current midpoint/reflection boundary
assumptions plus the support-complement sum lower bound to the full A-fiber
cardinality boundary. -/
noncomputable def toAFiberCardinality38Boundary_of_referenceMatching
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (cardTwo : MidpointMiddleSupportCardTwoBoundary labeling)
    (rhs : ReferenceRotationToMidpointReflectionBoundary labeling)
    (hsum_ge :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        38 ≤
          ∑ i ∈ (Finset.univ : Finset (ZMod 19)),
            (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
              d i hd).supportᶜ.card) :
  AFiberCardinality38Boundary h labeling.data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  AFiberCardinality38Boundary.of_allFibers_referenceMatchingExceptionSetTwo_of_sum_ge
    labeling.data.toAFiberRotationEquivariance
    (labeling.toReferenceFiberMatchingExceptionSetTwo criterion cardTwo rhs)
    hsum_ge

/-- Fixed-star version of the full cardinality pipeline: fixed-star/midpoint
inputs produce the reference two-exception boundary, and the support-complement
sum lower bound feeds the existing A-fiber cardinality constructor. -/
structure FixedStarReferenceMatchingCardinalityPipelineBoundary
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  referenceMatching : FixedStarReferenceMatchingPipelineBoundary star labeling
  supportCompl_sum_ge :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      38 ≤
        ∑ i ∈ (Finset.univ : Finset (ZMod 19)),
          (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
            d i hd).supportᶜ.card

namespace FixedStarReferenceMatchingCardinalityPipelineBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Build the fixed-star cardinality pipeline from vertex-fixed reference
solutions and the support-complement sum lower bound. -/
noncomputable def of_vertexFixed
    (middle : ReflectionFixedStarMiddleBoundary star labeling)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
    (supportCompl_sum_ge :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        38 ≤
          ∑ i ∈ (Finset.univ : Finset (ZMod 19)),
            (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
              d i hd).supportᶜ.card) :
    FixedStarReferenceMatchingCardinalityPipelineBoundary star labeling where
  referenceMatching :=
    FixedStarReferenceMatchingPipelineBoundary.of_vertexFixed
      middle referenceSolutionVertexFixed
  supportCompl_sum_ge := supportCompl_sum_ge

/-- Forget the fixed-star packaging after deriving the generic reference
matching inputs. -/
noncomputable def toReferenceMatchingCardinalityPipelineBoundary
    (boundary :
      FixedStarReferenceMatchingCardinalityPipelineBoundary star labeling) :
    ReferenceMatchingCardinalityPipelineBoundary labeling where
  referenceMatching :=
    boundary.referenceMatching.toReferenceMatchingPipelineBoundary
  supportCompl_sum_ge := boundary.supportCompl_sum_ge

/-- Final A-fiber cardinality boundary obtained from fixed-star packaged inputs. -/
noncomputable def toAFiberCardinality38Boundary
    (boundary :
      FixedStarReferenceMatchingCardinalityPipelineBoundary star labeling) :
  AFiberCardinality38Boundary h labeling.data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  boundary.toReferenceMatchingCardinalityPipelineBoundary
    |>.toAFiberCardinality38Boundary

end FixedStarReferenceMatchingCardinalityPipelineBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
