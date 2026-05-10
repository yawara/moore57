import Moore57.BranchOrbitABCFinalGapReportBoundary

/-!
# Current final-gap support subset contradiction

The current final-gap report still carries the all-support exception
`E ⊆ S_m`.  Together with the endpoint obstruction already present in the same
report, this is exactly the positive card-two case excluded in the
natural-language proof: a support point would both satisfy and fail the
midpoint endpoint adjacency.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instFinalGapSupportSubsetContradictionPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instFinalGapSupportSubsetContradictionDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCCurrentFinalGapBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The endpoint obstruction in the current final-gap report says no A-fixing
support point can satisfy the midpoint endpoint adjacency. -/
def endpointPointwiseNonadj
    (boundary : BranchOrbitABCCurrentFinalGapBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
      boundary.labeling :=
  boundary.endpointSignAdjacency
    |>.toEndpointSignAdjacencyBoundary
    |>.toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    |>.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

/-- A current final-gap report is internally inconsistent: `E ⊆ S_m` and the
midpoint criterion give endpoint adjacency on a nonempty support point, while
the endpoint obstruction denies exactly that adjacency. -/
theorem false_of_supportSubset_endpointObstruction
    (boundary : BranchOrbitABCCurrentFinalGapBoundary h) : False := by
  classical
  let supportCard :=
    boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary
  rcases supportCard.exists_mem_aFiberReflectionSupport with ⟨p, hpSupport⟩
  have hd : (1 : ZMod 19) ≠ 0 := by decide
  have hsubset :
      boundary.labeling.aFiberReflectionSupport ⊆
        boundary.labeling.midpointExceptionSet
          (midpointOf (1 : ZMod 19)) (midpointOf_ne_zero hd) :=
    boundary.supportSubsetException.support_subset_exception
      (midpointOf (1 : ZMod 19)) (midpointOf_ne_zero hd)
  have hadj :
      Γ.Adj
        (((boundary.labeling.data.toAFiberCoordinates.coord 0 p :
          {x : V // x ∈
            branchFiber Γ boundary.labeling.data.toAFiberCoordinates.u
              (boundary.labeling.data.toAFiberCoordinates.a 0)}) : V))
        (((boundary.labeling.data.toAFiberCoordinates.coord
            (0 + (midpointOf (1 : ZMod 19) + midpointOf (1 : ZMod 19)))
            (boundary.labeling.midpointReflectionCoordPerm
              (midpointOf (1 : ZMod 19)) p) :
          {x : V // x ∈
            branchFiber Γ boundary.labeling.data.toAFiberCoordinates.u
              (boundary.labeling.data.toAFiberCoordinates.a
                (0 + (midpointOf (1 : ZMod 19) +
                  midpointOf (1 : ZMod 19))))}) : V)) :=
    boundary.labeling.midpointEndpointAdj_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
      boundary.doublingReflectedEquation.midpointCriterion hsubset hpSupport
  exact
    (boundary.endpointPointwiseNonadj.endpoint_nonadj_of_mem_support
      1 hd p hpSupport) hadj

end BranchOrbitABCCurrentFinalGapBoundary

/-- No current final-gap report exists, independently of the representation
component boundary.  This records that its `supportSubsetException` field is
the excluded card-two branch rather than a remaining compatible input. -/
theorem not_currentFinalGapBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) := by
  rintro ⟨boundary⟩
  exact boundary.false_of_supportSubset_endpointObstruction

end

end Moore57
