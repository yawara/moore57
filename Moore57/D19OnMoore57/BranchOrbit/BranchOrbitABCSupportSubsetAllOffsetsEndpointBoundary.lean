import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionAllSupportBoundary

/-!
# Endpoint adjacency from global support-subset exceptions

A global hypothesis `E ⊆ S_m` for every nonzero midpoint `m`, together with
the midpoint-reflection criterion, gives endpoint adjacency for every nonzero
endpoint offset and every A-fixing reflection-support coordinate.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instSupportSubsetAllOffsetsEndpointBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instSupportSubsetAllOffsetsEndpointBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- A global support-subset exception hypothesis, plus the midpoint-reflection
criterion, supplies endpoint adjacency at every nonzero offset on every
A-fixing reflection-support coordinate. -/
theorem all_offsets_endpoint_adj_of_support_subset_midpointExceptionSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (support_subset_exception :
      ∀ m : ZMod 19, ∀ hm : m ≠ 0,
        labeling.aFiberReflectionSupport ⊆
          labeling.midpointExceptionSet m hm) :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (((labeling.data.toAFiberCoordinates.coord 0 p :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a 0)}) : V))
            (((labeling.data.toAFiberCoordinates.coord
                (0 + (midpointOf d + midpointOf d))
                (labeling.midpointReflectionCoordPerm (midpointOf d) p) :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a
                    (0 + (midpointOf d + midpointOf d)))}) : V)) := by
  intro d hd p hpSupport
  exact
    labeling.midpointEndpointAdj_of_mem_aFiberReflectionSupport_of_subset_midpointExceptionSet
      criterion
      (support_subset_exception (midpointOf d) (midpointOf_ne_zero hd))
      hpSupport

end BranchOrbitABCReflectionLabeling

end

end Moore57
