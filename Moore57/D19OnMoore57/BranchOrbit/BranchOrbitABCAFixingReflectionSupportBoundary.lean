import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCReflectionFixedStarBoundary

/-!
# A-fixing reflection support boundary

This file packages the fixed-star input at the A-fixing reflection.  It is the
reference-fiber analogue of `MidpointMiddleFixedNeighborCardBoundary`: if the
A-branch vertex fixed by the chosen reflection is the center of the reflection
fixed star, then the A-fixing reflection moves exactly two coordinates in the
reference A-fiber.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instAFixingReflectionSupportBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instAFixingReflectionSupportBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The reference A-branch vertex fixed by the A-fixing reflection, viewed in the
corresponding reflection fixed subtype. -/
def aFixingFixedVertex
    (labeling : BranchOrbitABCReflectionLabeling h) :
    reflectionFixedVertex h labeling.aFixingReflectionIndex :=
  ⟨labeling.data.toAFiberCoordinates.a 0, by
    simpa [BranchOrbitABCFromCenter.toAFiberCoordinates_a] using
      labeling.aFixingReflectionIndex_spec⟩

/-- Boundary form of the fixed-star input at the chosen A-fixing reflection. -/
structure ReflectionFixedStarAFixingBoundary
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFixing_is_center :
    IsReflectionFixedStarCenter h labeling.aFixingReflectionIndex
      (labeling.aFixingFixedVertex)

/-- Boundary form of the fixed-neighbor count needed on the reference A-branch:
among neighbors of `a0`, exactly `55` are fixed by the A-fixing reflection. -/
structure AFixingReflectionFixedNeighborCardBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  fixed_reference_neighbor_card :
    ((Γ.neighborFinset (labeling.data.toAFiberCoordinates.a 0)).filter
      fun y =>
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) y =
          y).card = 55

namespace ReflectionFixedStarAFixingBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The fixed-star A-center identification gives the fixed-neighbor count for
the reference A-branch. -/
def toAFixingReflectionFixedNeighborCardBoundary
    (boundary : ReflectionFixedStarAFixingBoundary star labeling) :
    AFixingReflectionFixedNeighborCardBoundary labeling where
  fixed_reference_neighbor_card := by
    have hdegree :
        (h.fixedInducedGraph
            (DihedralGroup.sr labeling.aFixingReflectionIndex)).degree
          (labeling.aFixingFixedVertex) = 55 :=
      boundary.aFixing_is_center.1
    have hcard :=
      h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
        (DihedralGroup.sr labeling.aFixingReflectionIndex)
        (labeling.aFixingFixedVertex)
    rw [hcard] at hdegree
    exact hdegree

end ReflectionFixedStarAFixingBoundary

namespace AFixingReflectionFixedNeighborCardBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Fixed coordinates of the A-fixing reflection are the fixed vertices in the
reference A-fiber. -/
theorem aFiberReflectionCoordPerm_support_compl_card_eq_fixed_reference_fiber_card
    (labeling : BranchOrbitABCReflectionLabeling h) :
    (labeling.aFiberReflectionCoordPerm.supportᶜ).card =
      ((labeling.data.toAFiberCoordinates.fiber 0).filter fun y =>
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) y =
          y).card := by
  classical
  let coords := labeling.data.toAFiberCoordinates
  let σ := labeling.aFiberReflectionCoordPerm
  let ref := labeling.toAFiberReflectionEquivariance
  change σ.supportᶜ.card =
    ((coords.fiber 0).filter fun y =>
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) y =
        y).card
  refine Finset.card_bij'
    (fun p _hp =>
      ((coords.coord 0 p :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
    (fun y hy =>
      (coords.coord 0).symm
        ⟨y, (Finset.mem_filter.mp hy).1⟩)
    ?hi ?hj ?left_inv ?right_inv
  · intro p hp
    have hpfix : σ p = p := by
      exact (Equiv.Perm.notMem_support).1 (Finset.mem_compl.mp hp)
    have hraw :
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (((coords.coord 0 p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) :
              V)) =
          ((coords.coord (-0) (σ p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (-0))}) : V) :=
      (AFiberReflectionEquivariance.coord_coordPerm_apply_val
        (ref := ref) (i := 0) (p := p)).symm
    simp only [hpfix] at hraw
    rw [Finset.mem_filter]
    exact ⟨by
      simpa [AFiberCoordinates.fiber, coords] using
        coords.coord_mem 0 p,
      hraw⟩
  · intro y hy
    have hyfix :
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) y = y :=
      (Finset.mem_filter.mp hy).2
    have hperm :
        σ ((coords.coord 0).symm
            ⟨y, (Finset.mem_filter.mp hy).1⟩) =
          (coords.coord 0).symm
            ⟨y, (Finset.mem_filter.mp hy).1⟩ := by
      have hcoord :
          ((coords.coord 0
              ((coords.coord 0).symm
                ⟨y, (Finset.mem_filter.mp hy).1⟩) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) :
            V) = y :=
        congrArg Subtype.val
          ((coords.coord 0).apply_symm_apply
            ⟨y, (Finset.mem_filter.mp hy).1⟩)
      apply
        (AFiberReflectionEquivariance.coordPerm_eq_iff
          (ref := ref) (i := 0)
          ((coords.coord 0).symm
            ⟨y, (Finset.mem_filter.mp hy).1⟩)
          ((coords.coord 0).symm
            ⟨y, (Finset.mem_filter.mp hy).1⟩)).2
      change
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (((coords.coord 0
              ((coords.coord 0).symm
                ⟨y, (Finset.mem_filter.mp hy).1⟩) :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) =
          (((coords.coord 0
              ((coords.coord 0).symm
                ⟨y, (Finset.mem_filter.mp hy).1⟩) :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
      rw [hcoord]
      exact hyfix
    exact Finset.mem_compl.mpr ((Equiv.Perm.notMem_support).2 hperm)
  · intro p hp
    exact (coords.coord 0).symm_apply_apply p
  · intro y hy
    exact
      congrArg Subtype.val
        ((coords.coord 0).apply_symm_apply
          ⟨y, (Finset.mem_filter.mp hy).1⟩)

/-- The fixed vertices in the reference A-fiber are exactly the fixed neighbors
of `a0`, except for the rotation-fixed center `u`. -/
theorem fixed_reference_fiber_card_eq_fiftyFour
    (boundary : AFixingReflectionFixedNeighborCardBoundary labeling) :
    ((labeling.data.toAFiberCoordinates.fiber 0).filter fun y =>
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) y =
        y).card = 54 := by
  classical
  let coords := labeling.data.toAFiberCoordinates
  let fixedNeighborSet : Finset V :=
    (Γ.neighborFinset (coords.a 0)).filter fun y =>
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) y = y
  have hu_fixed :
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) coords.u =
        coords.u :=
    labeling.toAFiberReflectionEquivariance.reflection_u
  have hu_mem : coords.u ∈ fixedNeighborSet := by
    rw [Finset.mem_filter]
    exact ⟨by
      simpa [SimpleGraph.mem_neighborFinset] using
        (coords.hub 0).symm,
      hu_fixed⟩
  have hfilter :
      ((coords.fiber 0).filter fun y =>
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) y =
          y) =
        fixedNeighborSet.erase coords.u := by
    ext y
    simp [fixedNeighborSet, AFiberCoordinates.fiber, branchFiber,
      SimpleGraph.mem_neighborFinset, and_assoc]
  calc
    ((labeling.data.toAFiberCoordinates.fiber 0).filter fun y =>
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) y =
        y).card =
        (fixedNeighborSet.erase coords.u).card := by
          simpa [coords] using congrArg Finset.card hfilter
    _ = fixedNeighborSet.card - 1 := by
          rw [Finset.card_erase_of_mem hu_mem]
    _ = 54 := by
          rw [boundary.fixed_reference_neighbor_card]

/-- The A-fixing reflection moves exactly two reference A-fiber coordinates. -/
theorem aFiberReflectionSupport_card_two
    (boundary : AFixingReflectionFixedNeighborCardBoundary labeling) :
    labeling.aFiberReflectionSupport.card = 2 := by
  classical
  letI := labeling.data.toAFiberCoordinates.P_fintype
  let σ := labeling.aFiberReflectionCoordPerm
  have hcompl : σ.supportᶜ.card = 54 := by
    calc
      σ.supportᶜ.card =
          ((labeling.data.toAFiberCoordinates.fiber 0).filter fun y =>
            h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) y =
              y).card :=
            aFiberReflectionCoordPerm_support_compl_card_eq_fixed_reference_fiber_card
              labeling
      _ = 54 := boundary.fixed_reference_fiber_card_eq_fiftyFour
  have hP : Fintype.card labeling.data.toAFiberCoordinates.P = 56 :=
    labeling.data.toAFiberCoordinates.card_P h.isMoore
  have hsum :
      σ.support.card + σ.supportᶜ.card =
        Fintype.card labeling.data.toAFiberCoordinates.P :=
    Finset.card_add_card_compl σ.support
  have hsupport : σ.support.card = 2 := by
    omega
  simpa [aFiberReflectionSupport, aFiberReflectionCoordPerm,
    AFiberReflectionEquivariance.supportAt, σ] using hsupport

end AFixingReflectionFixedNeighborCardBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
