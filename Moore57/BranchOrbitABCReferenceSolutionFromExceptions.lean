import Moore57.BranchOrbitABCExceptionCaseBoundary
import Moore57.BranchOrbitABCReferenceSolutionGeometryBoundary

/-!
# Reference solution support-complement boundary from midpoint exceptions

This file wires two existing boundary packages together.  The reference
matching pipeline puts reference matching solutions inside the midpoint
exception set, while the exception-disjoint boundary says that midpoint
exception set is disjoint from the A-fixing reflection support.  Therefore the
reference matching solutions lie in `aFiberReflectionSupportᶜ`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instReferenceSolutionFromExceptionsPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instReferenceSolutionFromExceptionsDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}
variable {labeling : BranchOrbitABCReflectionLabeling h}

namespace MidpointExceptionDisjointAFixingSupportBoundary

/-- Build the reference-solution support-complement boundary from the reference
matching exception-set pipeline and disjointness of midpoint exceptions from
the A-fixing support. -/
noncomputable def toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    (boundary : MidpointExceptionDisjointAFixingSupportBoundary labeling)
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling where
  reference_matching_solution_subset_aFiberReflectionSupport_compl := by
    intro d hd p hp
    have hpFilter :
        p ∈ ((Finset.univ : Finset labeling.data.toAFiberCoordinates.P).filter
          fun p =>
            AFiberCoordinates.matchingEquiv h.isMoore
                labeling.data.toAFiberCoordinates 0 (0 + d)
                (index_ne_add_of_ne_zero hd) p =
              labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) := by
      simpa [BranchOrbitABCReflectionLabeling.referenceMatchingSolutionSet]
        using hp
    have hpException :
        p ∈ labeling.midpointExceptionSet (midpointOf d)
          (midpointOf_ne_zero hd) := by
      simpa [ReferenceMatchingPipelineBoundary.toReferenceFiberMatchingExceptionSetTwo,
        ReferenceFiberMatchingExceptionSetTwo.of_midpointReflectionBoundary]
        using
          (referenceMatching.toReferenceFiberMatchingExceptionSetTwo
            |>.reference_matching_subset_exception d hd hpFilter)
    exact
      Finset.mem_compl.mpr
        (boundary.not_mem_aFiberReflectionSupport_of_mem_midpointException
          hd hpException)

end MidpointExceptionDisjointAFixingSupportBoundary

namespace MidpointExceptionAFixingSupportCaseBoundary

/-- Build the reference-solution support-complement boundary from the finite
case boundary by first deriving midpoint-exception disjointness. -/
noncomputable def toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    (boundary : MidpointExceptionAFixingSupportCaseBoundary labeling)
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling :=
  boundary.toMidpointExceptionDisjointAFixingSupportBoundary
    |>.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
      referenceMatching

end MidpointExceptionAFixingSupportCaseBoundary

namespace ReferenceRotationMatchingSolutionAFixingSupportComplBoundary

/-- Constructor spelling with the target boundary as the namespace: reference
solutions are contained in the two-point midpoint exception set, and that set
is disjoint from the A-fixing support. -/
noncomputable def of_referenceMatchingPipeline_midpointExceptionDisjoint
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling)
    (disjoint : MidpointExceptionDisjointAFixingSupportBoundary labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling :=
  disjoint.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    referenceMatching

/-- Constructor spelling from the finite midpoint-exception case boundary. -/
noncomputable def of_referenceMatchingPipeline_midpointExceptionCase
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling)
    (caseBoundary : MidpointExceptionAFixingSupportCaseBoundary labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling :=
  caseBoundary.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    referenceMatching

end ReferenceRotationMatchingSolutionAFixingSupportComplBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
