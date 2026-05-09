import Moore57.BranchOrbitABCMidpointReflection

/-!
# Reference exception sets from midpoint reflections

This file connects the midpoint-reflection criterion to the existing reference
matching exception-set boundary.  The only remaining non-formal input is the
comparison between the reference rotation equation and the midpoint reflection
equation.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instMidpointExceptionSetBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instMidpointExceptionSetBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- The midpoint index for an offset `d`, using that `2` is invertible in
`ZMod 19`. -/
noncomputable def midpointOf (d : ZMod 19) : ZMod 19 :=
  (2 : ZMod 19)⁻¹ * d

theorem two_mul_midpointOf (d : ZMod 19) :
    (2 : ZMod 19) * midpointOf d = d := by
  dsimp [midpointOf]
  rw [← mul_assoc, mul_inv_cancel₀ two_ne_zero_zmod19, one_mul]

theorem midpointOf_add_self (d : ZMod 19) :
    midpointOf d + midpointOf d = d := by
  rw [← two_mul, two_mul_midpointOf]

theorem midpointOf_ne_zero {d : ZMod 19} (hd : d ≠ 0) :
    midpointOf d ≠ 0 := by
  intro hm
  apply hd
  rw [← two_mul_midpointOf d, hm, mul_zero]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Boundary saying the midpoint reflection has a two-point moving support on
each nonzero middle A-fiber. -/
structure MidpointMiddleSupportCardTwoBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  midpointMiddleSupport_card_two :
    ∀ m : ZMod 19, ∀ _hm : m ≠ 0,
      (labeling.midpointMiddleSupport m).card = 2

namespace MidpointMiddleSupportCardTwoBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

theorem midpointExceptionSet_card_two
    (cardTwo : MidpointMiddleSupportCardTwoBoundary labeling)
    (m : ZMod 19) (hm : m ≠ 0) :
    (labeling.midpointExceptionSet m hm).card = 2 := by
  calc
    (labeling.midpointExceptionSet m hm).card =
        (labeling.midpointMiddleSupport m).card :=
          labeling.midpointExceptionSet_card_eq_midpointMiddleSupport_card m hm
    _ = 2 := cardTwo.midpointMiddleSupport_card_two m hm

end MidpointMiddleSupportCardTwoBoundary

/-- Boundary form of the fixed-star count needed on the middle A-branch: among
neighbors of the middle branch vertex, exactly `55` are fixed by the midpoint
reflection.  Since the center `u` is one of them, this leaves `54` fixed points
inside the middle branch fiber and hence a two-point moving support. -/
structure MidpointMiddleFixedNeighborCardBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  fixed_middle_neighbor_card :
    ∀ m : ZMod 19, ∀ _hm : m ≠ 0,
      ((Γ.neighborFinset (labeling.data.toAFiberCoordinates.a (0 + m))).filter
        fun y =>
          h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) y =
            y).card = 55

namespace MidpointMiddleFixedNeighborCardBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

theorem midpointMiddleCoordPerm_support_compl_card_eq_fixed_middle_fiber_card
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) :
    (labeling.midpointMiddleCoordPerm m).supportᶜ.card =
      ((labeling.data.toAFiberCoordinates.fiber (0 + m)).filter fun y =>
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) y =
          y).card := by
  classical
  let coords := labeling.data.toAFiberCoordinates
  let σ := labeling.midpointMiddleCoordPerm m
  let ref := labeling.toAFiberMidpointReflectionEquivariance m
  have hidx : (2 : ZMod 19) * m - (0 + m) = 0 + m := by
    ring
  change σ.supportᶜ.card =
    ((coords.fiber (0 + m)).filter fun y =>
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) y =
        y).card
  refine Finset.card_bij'
    (fun p _hp =>
      ((coords.coord (0 + m) p :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V))
    (fun y hy =>
      (coords.coord (0 + m)).symm
        ⟨y, (Finset.mem_filter.mp hy).1⟩)
    ?hi ?hj ?left_inv ?right_inv
  · intro p hp
    have hpfix : σ p = p := by
      exact (Equiv.Perm.notMem_support).1 (Finset.mem_compl.mp hp)
    have hraw :
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
            (((coords.coord (0 + m) p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) :
              V)) =
          ((coords.coord ((2 : ZMod 19) * m - (0 + m)) (σ p) :
            {x : V // x ∈
              branchFiber Γ coords.u
                (coords.a ((2 : ZMod 19) * m - (0 + m)))}) : V) :=
      (AFiberReflectionEquivariance.coord_coordPerm_apply_val
        (ref := ref) (i := 0 + m) (p := p)).symm
    rw [hidx, hpfix] at hraw
    rw [Finset.mem_filter]
    exact ⟨by
      simpa [AFiberCoordinates.fiber, coords] using
        coords.coord_mem (0 + m) p,
      hraw⟩
  · intro y hy
    have hyfix :
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) y = y :=
      (Finset.mem_filter.mp hy).2
    have hperm :
        σ ((coords.coord (0 + m)).symm
            ⟨y, (Finset.mem_filter.mp hy).1⟩) =
          (coords.coord (0 + m)).symm
            ⟨y, (Finset.mem_filter.mp hy).1⟩ := by
      have hcoord :
          ((coords.coord (0 + m)
              ((coords.coord (0 + m)).symm
                ⟨y, (Finset.mem_filter.mp hy).1⟩) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) :
            V) = y :=
        congrArg Subtype.val
          ((coords.coord (0 + m)).apply_symm_apply
            ⟨y, (Finset.mem_filter.mp hy).1⟩)
      apply
        (AFiberReflectionEquivariance.coordPerm_eq_iff
          (ref := ref) (i := 0 + m)
          ((coords.coord (0 + m)).symm
            ⟨y, (Finset.mem_filter.mp hy).1⟩)
          ((coords.coord (0 + m)).symm
            ⟨y, (Finset.mem_filter.mp hy).1⟩)).2
      rw [hidx]
      change
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
            (((coords.coord (0 + m)
              ((coords.coord (0 + m)).symm
                ⟨y, (Finset.mem_filter.mp hy).1⟩) :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V)) =
          (((coords.coord (0 + m)
              ((coords.coord (0 + m)).symm
                ⟨y, (Finset.mem_filter.mp hy).1⟩) :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V))
      rw [hcoord]
      exact hyfix
    exact Finset.mem_compl.mpr ((Equiv.Perm.notMem_support).2 hperm)
  · intro p hp
    exact (coords.coord (0 + m)).symm_apply_apply p
  · intro y hy
    exact
      congrArg Subtype.val
        ((coords.coord (0 + m)).apply_symm_apply
          ⟨y, (Finset.mem_filter.mp hy).1⟩)

theorem fixed_middle_fiber_card_eq_fiftyFour
    (boundary : MidpointMiddleFixedNeighborCardBoundary labeling)
    (m : ZMod 19) (hm : m ≠ 0) :
    ((labeling.data.toAFiberCoordinates.fiber (0 + m)).filter fun y =>
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) y =
        y).card = 54 := by
  classical
  let coords := labeling.data.toAFiberCoordinates
  let fixedNeighborSet : Finset V :=
    (Γ.neighborFinset (coords.a (0 + m))).filter fun y =>
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) y = y
  have hu_fixed :
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) coords.u =
        coords.u :=
    (labeling.toAFiberMidpointReflectionEquivariance m).reflection_u
  have hu_mem : coords.u ∈ fixedNeighborSet := by
    rw [Finset.mem_filter]
    exact ⟨by
      simpa [SimpleGraph.mem_neighborFinset] using
        (coords.hub (0 + m)).symm,
      hu_fixed⟩
  have hfilter :
      ((coords.fiber (0 + m)).filter fun y =>
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) y =
          y) =
        fixedNeighborSet.erase coords.u := by
    ext y
    simp [fixedNeighborSet, AFiberCoordinates.fiber, branchFiber,
      SimpleGraph.mem_neighborFinset, and_assoc]
  calc
    ((labeling.data.toAFiberCoordinates.fiber (0 + m)).filter fun y =>
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) y =
        y).card =
        (fixedNeighborSet.erase coords.u).card := by
          simpa [coords] using congrArg Finset.card hfilter
    _ = fixedNeighborSet.card - 1 := by
          rw [Finset.card_erase_of_mem hu_mem]
    _ = 54 := by
          rw [boundary.fixed_middle_neighbor_card m hm]

theorem midpointMiddleSupport_card_two
    (boundary : MidpointMiddleFixedNeighborCardBoundary labeling)
    (m : ZMod 19) (hm : m ≠ 0) :
    (labeling.midpointMiddleSupport m).card = 2 := by
  classical
  letI := labeling.data.toAFiberCoordinates.P_fintype
  let σ := labeling.midpointMiddleCoordPerm m
  have hcompl : σ.supportᶜ.card = 54 := by
    calc
      σ.supportᶜ.card =
          ((labeling.data.toAFiberCoordinates.fiber (0 + m)).filter fun y =>
            h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) y =
              y).card :=
            midpointMiddleCoordPerm_support_compl_card_eq_fixed_middle_fiber_card
              labeling m
      _ = 54 := boundary.fixed_middle_fiber_card_eq_fiftyFour m hm
  have hP : Fintype.card labeling.data.toAFiberCoordinates.P = 56 :=
    labeling.data.toAFiberCoordinates.card_P h.isMoore
  have hsum :
      σ.support.card + σ.supportᶜ.card =
        Fintype.card labeling.data.toAFiberCoordinates.P :=
    Finset.card_add_card_compl σ.support
  have hsupport : σ.support.card = 2 := by
    omega
  simpa [midpointMiddleSupport, midpointMiddleCoordPerm,
    AFiberReflectionEquivariance.supportAt, σ] using hsupport

/-- The middle fixed-neighbor count boundary supplies the two-point moving
support boundary consumed by the reference exception-set bridge. -/
noncomputable def toMidpointMiddleSupportCardTwoBoundary
    (boundary : MidpointMiddleFixedNeighborCardBoundary labeling) :
    MidpointMiddleSupportCardTwoBoundary labeling where
  midpointMiddleSupport_card_two :=
    boundary.midpointMiddleSupport_card_two

end MidpointMiddleFixedNeighborCardBoundary

/-- Boundary comparing the existing reference rotation equation with the
midpoint reflection equation at `midpointOf d`. -/
structure ReferenceRotationToMidpointReflectionBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  reference_matching_subset_midpoint_equation :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((Finset.univ : Finset labeling.data.toAFiberCoordinates.P).filter fun p =>
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) ⊆
        labeling.midpointEquationSet (midpointOf d) (midpointOf_ne_zero hd)

theorem midpointReflection_smul_eq_rotation_aFixingReflection_smul
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (x : V) :
    h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) x =
      h.rotation (m + m)
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) x) := by
  change h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) x =
    h.smul (DihedralGroup.r (m + m))
      (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) x)
  rw [← h.mul_smul]
  congr 1
  rw [DihedralGroup.r_mul_sr]
  congr 1
  simp [BranchOrbitABCReflectionLabeling.midpointReflectionIndex]
  ring

theorem midpointReflectionCoordPerm_eq_rotationCoordPerm_aFiberReflectionCoordPerm
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) :
    labeling.midpointReflectionCoordPerm m p =
      labeling.data.toAFiberRotationEquivariance.coordPerm (m + m) 0
        (labeling.aFiberReflectionCoordPerm p) := by
  classical
  let coords := labeling.data.toAFiberCoordinates
  apply (coords.coord (0 + (m + m))).injective
  ext
  have hmid :
      ((coords.coord (0 + (m + m))
          (labeling.midpointReflectionCoordPerm m p) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (m + m)))}) :
        V) =
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
    have hidx : (2 : ZMod 19) * m - 0 = 0 + (m + m) := by
      ring
    have hraw :
        ((coords.coord ((2 : ZMod 19) * m - 0)
            (labeling.midpointReflectionCoordPerm m p) :
          {x : V // x ∈ branchFiber Γ coords.u
            (coords.a ((2 : ZMod 19) * m - 0))}) : V) =
          h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
            (((coords.coord 0 p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
      simpa [coords, midpointReflectionCoordPerm] using
        AFiberReflectionEquivariance.coord_coordPerm_apply_val
          (ref := labeling.toAFiberMidpointReflectionEquivariance m)
          (i := 0) (p := p)
    rw [hidx] at hraw
    simpa [coords] using hraw
  have href :
      ((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V) =
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
    simpa [coords] using labeling.coord_aFiberReflectionCoordPerm_apply_val p
  have hrot :
      ((coords.coord (0 + (m + m))
          (labeling.data.toAFiberRotationEquivariance.coordPerm (m + m) 0
            (labeling.aFiberReflectionCoordPerm p)) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (m + m)))}) :
        V) =
        h.rotation (m + m)
          (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
    simpa [coords] using
      AFiberRotationEquivariance.coord_coordPerm_apply_val
        (rot := labeling.data.toAFiberRotationEquivariance)
        (d := m + m) (i := 0)
        (p := labeling.aFiberReflectionCoordPerm p)
  calc
    ((coords.coord (0 + (m + m))
        (labeling.midpointReflectionCoordPerm m p) :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (m + m)))}) :
      V)
        = h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
            (((coords.coord 0 p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := hmid
    _ = h.rotation (m + m)
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) ) := by
          rw [labeling.midpointReflection_smul_eq_rotation_aFixingReflection_smul]
    _ = h.rotation (m + m)
        (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
          rw [← href]
    _ = ((coords.coord (0 + (m + m))
        (labeling.data.toAFiberRotationEquivariance.coordPerm (m + m) 0
          (labeling.aFiberReflectionCoordPerm p)) :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (m + m)))}) :
      V) := hrot.symm

theorem rotationCoordPerm_eq_midpointReflectionCoordPerm_iff_aFiberReflection_fixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) :
    labeling.data.toAFiberRotationEquivariance.coordPerm (m + m) 0 p =
      labeling.midpointReflectionCoordPerm m p ↔
        labeling.aFiberReflectionCoordPerm p = p := by
  rw [labeling.midpointReflectionCoordPerm_eq_rotationCoordPerm_aFiberReflectionCoordPerm
    m p]
  constructor
  · intro hp
    exact
      ((labeling.data.toAFiberRotationEquivariance.coordPerm (m + m) 0).injective
        hp).symm
  · intro hp
    rw [hp]

theorem rotationCoordPerm_eq_midpointReflectionCoordPerm_midpointOf_iff
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) :
    labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p =
      labeling.midpointReflectionCoordPerm (midpointOf d) p ↔
        labeling.aFiberReflectionCoordPerm p = p := by
  have hdd : midpointOf d + midpointOf d = d := midpointOf_add_self d
  simpa [hdd] using
    labeling.rotationCoordPerm_eq_midpointReflectionCoordPerm_iff_aFiberReflection_fixed
      (midpointOf d) p

/-- Boundary saying every solution of the reference rotation equation is fixed
by the A-fixing reflection on the reference coordinate fiber. -/
structure ReferenceRotationEquationAFixingFixedBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  reference_solution_fixed :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p →
        labeling.aFiberReflectionCoordPerm p = p

namespace ReferenceRotationToMidpointReflectionBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The A-fixing fixedness boundary implies the direct RHS-comparison boundary
used by the reference exception-set constructor. -/
noncomputable def of_aFixingFixed
    (fixed : ReferenceRotationEquationAFixingFixedBoundary labeling) :
    ReferenceRotationToMidpointReflectionBoundary labeling where
  reference_matching_subset_midpoint_equation := by
    intro d hd p hp
    rw [mem_midpointEquationSet]
    have hmatch :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p :=
      (Finset.mem_filter.mp hp).2
    have hfixed : labeling.aFiberReflectionCoordPerm p = p :=
      fixed.reference_solution_fixed d hd p hmatch
    have hrhs :
        labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p =
          labeling.midpointReflectionCoordPerm (midpointOf d) p :=
      (labeling.rotationCoordPerm_eq_midpointReflectionCoordPerm_midpointOf_iff
        d p).2 hfixed
    have hdd : midpointOf d + midpointOf d = d := midpointOf_add_self d
    simpa [hdd] using hmatch.trans hrhs

end ReferenceRotationToMidpointReflectionBoundary

end BranchOrbitABCReflectionLabeling

namespace ReferenceFiberMatchingExceptionSetTwo

variable {h : D19ActsOnMoore57 V Γ}

/-- Build the existing reference two-point exception-set boundary from the
midpoint-reflection criterion, the two-point midpoint support bound, and the
comparison from the reference rotation equation to the midpoint equation. -/
noncomputable def of_midpointReflectionBoundary
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion :
      BranchOrbitABCReflectionLabeling.MidpointReflectionCriterionBoundary
        labeling)
    (cardTwo :
      BranchOrbitABCReflectionLabeling.MidpointMiddleSupportCardTwoBoundary
        labeling)
    (rhs :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        labeling) :
    ReferenceFiberMatchingExceptionSetTwo
      labeling.data.toAFiberRotationEquivariance where
  exceptionSet d hd :=
    labeling.midpointExceptionSet (midpointOf d) (midpointOf_ne_zero hd)
  exception_card_two d hd :=
    cardTwo.midpointExceptionSet_card_two (midpointOf d) (midpointOf_ne_zero hd)
  reference_matching_subset_exception d hd := by
    intro p hp
    have hpEq :
        p ∈ labeling.midpointEquationSet
          (midpointOf d) (midpointOf_ne_zero hd) :=
      rhs.reference_matching_subset_midpoint_equation d hd hp
    exact
      (criterion.midpoint_equation_iff_exception
        (midpointOf d) (midpointOf_ne_zero hd) p).1 hpEq

/-- Variant of `of_midpointReflectionBoundary` using the more geometric
A-fixing fixedness boundary for reference-equation solutions. -/
noncomputable def of_midpointReflection_aFixingFixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion :
      BranchOrbitABCReflectionLabeling.MidpointReflectionCriterionBoundary
        labeling)
    (cardTwo :
      BranchOrbitABCReflectionLabeling.MidpointMiddleSupportCardTwoBoundary
        labeling)
    (fixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationEquationAFixingFixedBoundary
        labeling) :
    ReferenceFiberMatchingExceptionSetTwo
      labeling.data.toAFiberRotationEquivariance :=
  of_midpointReflectionBoundary labeling criterion cardTwo
    (BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary.of_aFixingFixed
      (labeling := labeling) fixed)

end ReferenceFiberMatchingExceptionSetTwo

end

end Moore57
