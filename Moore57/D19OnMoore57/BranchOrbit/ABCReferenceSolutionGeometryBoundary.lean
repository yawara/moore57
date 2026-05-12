import Moore57.D19OnMoore57.BranchOrbit.ABCReferenceSolutionFixedBoundary
import Moore57.Moore57Graph.AFiber.MatchingPermAdjacency
import Moore57.D19OnMoore57.BranchOrbit.ABCSupportPairBoundary

/-!
# Geometry connectors for reference matching solution fixedness

This file adds thin boundary connectors for the geometric statement that
reference matching-equation solutions lie in the fixed part of the A-fixing
reflection.  The target boundary is
`ReferenceRotationMatchingSolutionVertexFixedBoundary`; the hypotheses here are
more Finset-oriented, or are stated on the underlying reference-fiber vertices.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instReferenceSolutionGeometryBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instReferenceSolutionGeometryBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The reference matching-equation solution set for the offset `d`. -/
noncomputable def referenceMatchingSolutionSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0) :
    Finset labeling.data.toAFiberCoordinates.P :=
  (Finset.univ : Finset labeling.data.toAFiberCoordinates.P).filter fun p =>
    AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + d)
        (index_ne_add_of_ne_zero hd) p =
      labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p

@[simp] theorem mem_referenceMatchingSolutionSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    p ∈ labeling.referenceMatchingSolutionSet d hd ↔
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates 0 (0 + d)
          (index_ne_add_of_ne_zero hd) p =
        labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p := by
  simp [referenceMatchingSolutionSet]

/-- Membership in the reference matching solution set is exactly adjacency
from the reference A-fiber coordinate to the rotated target coordinate. -/
theorem mem_referenceMatchingSolutionSet_iff_adj_rotationTarget
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    p ∈ labeling.referenceMatchingSolutionSet d hd ↔
      Γ.Adj
        (((labeling.data.toAFiberCoordinates.coord 0 p :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a 0)}) : V))
        (((labeling.data.toAFiberCoordinates.coord (0 + d)
            (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a (0 + d))}) : V)) := by
  constructor
  · intro hp
    exact
      (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore
        labeling.data.toAFiberCoordinates (index_ne_add_of_ne_zero hd) p
        (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p)).2
        ((labeling.mem_referenceMatchingSolutionSet d hd p).1 hp)
  · intro hpAdj
    exact
      (labeling.mem_referenceMatchingSolutionSet d hd p).2
        ((AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore
          labeling.data.toAFiberCoordinates (index_ne_add_of_ne_zero hd) p
          (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p)).1
          hpAdj)

/-- A reference matching solution at offset `d` is also a solution at offset
`-d`.  Geometrically, it is an edge from the reference fiber to its `d`-rotate;
reversing the edge and rotating by `-d` gives the same reference coordinate as
a solution at offset `-d`. -/
theorem mem_referenceMatchingSolutionSet_neg
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    p ∈ labeling.referenceMatchingSolutionSet d hd →
      p ∈ labeling.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd) := by
  intro hp
  let coords := labeling.data.toAFiberCoordinates
  let rot := labeling.data.toAFiberRotationEquivariance
  have hpAdj :
        Γ.Adj
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
          (((coords.coord (0 + d) (rot.coordPerm d 0 p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) :=
      (labeling.mem_referenceMatchingSolutionSet_iff_adj_rotationTarget
        d hd p).1 hp
  have hAdj_rot :
        Γ.Adj
          (h.rotation (-d)
            (((coords.coord (0 + d) (rot.coordPerm d 0 p) :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)))
          (h.rotation (-d)
            (((coords.coord 0 p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))) := by
      simpa [D19ActsOnMoore57.rotation] using
        (h.smul_adj (DihedralGroup.r (-d))
          (((coords.coord (0 + d) (rot.coordPerm d 0 p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V))
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))).mp
          hpAdj.symm
  have htarget_d :
        (((coords.coord (0 + d) (rot.coordPerm d 0 p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) =
          h.rotation d
            (((coords.coord 0 p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
      simpa [coords, rot] using
        AFiberRotationEquivariance.coord_coordPerm_apply_val
          (rot := labeling.data.toAFiberRotationEquivariance)
          (d := d) (i := 0) (p := p)
  have hleft :
        h.rotation (-d)
          (((coords.coord (0 + d) (rot.coordPerm d 0 p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) =
        (((coords.coord 0 p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
      rw [htarget_d]
      calc
        h.rotation (-d)
            (h.rotation d
              (((coords.coord 0 p :
                {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)))
            =
          (h.rotation (-d) * h.rotation d)
              (((coords.coord 0 p :
                {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
              simp [Equiv.Perm.mul_apply]
        _ =
          h.rotation ((-d) + d)
              (((coords.coord 0 p :
                {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
              rw [← h.rotation_add]
        _ = (((coords.coord 0 p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
              simp
  have htarget_neg :
        (((coords.coord (0 + (-d)) (rot.coordPerm (-d) 0 p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (-d)))}) : V)) =
          h.rotation (-d)
            (((coords.coord 0 p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
      simpa [coords, rot] using
        AFiberRotationEquivariance.coord_coordPerm_apply_val
          (rot := labeling.data.toAFiberRotationEquivariance)
          (d := -d) (i := 0) (p := p)
  have hpAdj_neg :
        Γ.Adj
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
          (((coords.coord (0 + (-d)) (rot.coordPerm (-d) 0 p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (-d)))}) : V)) := by
      rw [hleft, ← htarget_neg] at hAdj_rot
      exact hAdj_rot
  exact
      (labeling.mem_referenceMatchingSolutionSet_iff_adj_rotationTarget
        (-d) (neg_ne_zero.mpr hd) p).2
        (by simpa [coords, rot] using hpAdj_neg)

/-- The reference matching solution set is invariant under changing the offset
sign. -/
theorem referenceMatchingSolutionSet_neg_iff
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    p ∈ labeling.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd) ↔
      p ∈ labeling.referenceMatchingSolutionSet d hd := by
  constructor
  · intro hpneg
    have hback :=
      labeling.mem_referenceMatchingSolutionSet_neg (-d)
        (neg_ne_zero.mpr hd) p hpneg
    simpa using hback
  · exact labeling.mem_referenceMatchingSolutionSet_neg d hd p

/-- A point in the A-fixing moving support gives two distinct reference-fiber
vertices: the original coordinate and its A-reflection. -/
theorem aFiberReflectionSupport_reflectedReferenceVertex_ne
    (labeling : BranchOrbitABCReflectionLabeling h)
    {p : labeling.data.toAFiberCoordinates.P}
    (hpSupport : p ∈ labeling.aFiberReflectionSupport) :
    (((labeling.data.toAFiberCoordinates.coord 0
        (labeling.aFiberReflectionCoordPerm p) :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a 0)}) : V)) ≠
      (((labeling.data.toAFiberCoordinates.coord 0 p :
        {x : V // x ∈
          branchFiber Γ labeling.data.toAFiberCoordinates.u
            (labeling.data.toAFiberCoordinates.a 0)}) : V)) := by
  intro hvertex
  have hpFixed :
      labeling.aFiberReflectionCoordPerm p = p := by
    exact (labeling.data.toAFiberCoordinates.coord 0).injective
      (Subtype.ext hvertex)
  exact ((labeling.mem_aFiberReflectionSupport p).1 hpSupport) hpFixed

/-- The original reference coordinate and its A-reflection are non-adjacent;
they lie in the same A-side branch fiber. -/
theorem not_adj_reference_reflectedReference
    (labeling : BranchOrbitABCReflectionLabeling h)
    (p : labeling.data.toAFiberCoordinates.P) :
    ¬ Γ.Adj
      (((labeling.data.toAFiberCoordinates.coord 0 p :
        {x : V // x ∈
          branchFiber Γ labeling.data.toAFiberCoordinates.u
            (labeling.data.toAFiberCoordinates.a 0)}) : V))
      (((labeling.data.toAFiberCoordinates.coord 0
          (labeling.aFiberReflectionCoordPerm p) :
        {x : V // x ∈
          branchFiber Γ labeling.data.toAFiberCoordinates.u
            (labeling.data.toAFiberCoordinates.a 0)}) : V)) :=
  AFiberCoordinates.not_adj_same_coord h.isMoore
    labeling.data.toAFiberCoordinates 0 p
    (labeling.aFiberReflectionCoordPerm p)

/-- Reflecting the rotated target of a reference coordinate changes the offset
from `d` to `-d` and reflects the source coordinate. -/
theorem aFiberReflection_rotationCoordPerm_vertex_eq
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) :
    h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
        (((labeling.data.toAFiberCoordinates.coord (0 + d)
            (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a (0 + d))}) : V)) =
      (((labeling.data.toAFiberCoordinates.coord (0 + (-d))
          (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
            (labeling.aFiberReflectionCoordPerm p)) :
        {x : V // x ∈
          branchFiber Γ labeling.data.toAFiberCoordinates.u
            (labeling.data.toAFiberCoordinates.a (0 + (-d)))}) : V)) := by
  let coords := labeling.data.toAFiberCoordinates
  have htarget :
      (((coords.coord (0 + d)
          (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) =
        h.rotation d
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
    simpa [coords] using
      AFiberRotationEquivariance.coord_coordPerm_apply_val
        (rot := labeling.data.toAFiberRotationEquivariance)
        (d := d) (i := 0) (p := p)
  have hsource_reflect :
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) =
        (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
    simpa [coords] using (labeling.coord_aFiberReflectionCoordPerm_apply_val p).symm
  have hneg_target :
      (((coords.coord (0 + (-d))
          (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
            (labeling.aFiberReflectionCoordPerm p)) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (-d)))}) : V)) =
        h.rotation (-d)
          (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
    simpa [coords] using
      AFiberRotationEquivariance.coord_coordPerm_apply_val
        (rot := labeling.data.toAFiberRotationEquivariance)
        (d := -d) (i := 0)
        (p := labeling.aFiberReflectionCoordPerm p)
  calc
    h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
        (((coords.coord (0 + d)
            (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V))
        = h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (h.rotation d
              (((coords.coord 0 p :
                {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))) := by
              rw [htarget]
    _ = h.rotation (-d)
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))) := by
          rw [h.reflection_smul_rotation]
    _ = h.rotation (-d)
        (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
          rw [hsource_reflect]
    _ = (((coords.coord (0 + (-d))
          (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
            (labeling.aFiberReflectionCoordPerm p)) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (-d)))}) : V)) :=
          hneg_target.symm

/-- The exact non-circular consequence of A-fixing reflection symmetry:
reference matching solutions at offset `d` are transported to reference
matching solutions at offset `-d`. -/
theorem aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet_neg
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    p ∈ labeling.referenceMatchingSolutionSet d hd →
      labeling.aFiberReflectionCoordPerm p ∈
        labeling.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd) := by
  intro hp
  let coords := labeling.data.toAFiberCoordinates
  have hpAdj :
      Γ.Adj
        (((coords.coord 0 p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
        (((coords.coord (0 + d)
            (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) :=
    (labeling.mem_referenceMatchingSolutionSet_iff_adj_rotationTarget
      d hd p).1 hp
  have hpAdj_reflected :
      Γ.Adj
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)))
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord (0 + d)
              (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V))) :=
    (h.smul_adj (DihedralGroup.sr labeling.aFixingReflectionIndex)
      (((coords.coord 0 p :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
      (((coords.coord (0 + d)
          (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V))).mp
      hpAdj
  have hsource :
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) =
        (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
    simpa [coords] using (labeling.coord_aFiberReflectionCoordPerm_apply_val p).symm
  have htarget :
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord (0 + d)
              (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) =
        (((coords.coord (0 + (-d))
            (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0
              (labeling.aFiberReflectionCoordPerm p)) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (-d)))}) : V)) := by
    simpa [coords] using
      labeling.aFiberReflection_rotationCoordPerm_vertex_eq d p
  rw [hsource, htarget] at hpAdj_reflected
  exact
    (labeling.mem_referenceMatchingSolutionSet_iff_adj_rotationTarget
      (-d) (neg_ne_zero.mpr hd) (labeling.aFiberReflectionCoordPerm p)).2
      (by simpa [coords] using hpAdj_reflected)

/-- Combining A-fixing reflection transport with the sign symmetry of the
reference solution set gives same-offset closure under the A-fixing coordinate
reflection. -/
theorem aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    p ∈ labeling.referenceMatchingSolutionSet d hd →
      labeling.aFiberReflectionCoordPerm p ∈
        labeling.referenceMatchingSolutionSet d hd := by
  intro hp
  exact
    (labeling.referenceMatchingSolutionSet_neg_iff d hd
      (labeling.aFiberReflectionCoordPerm p)).1
      (labeling.aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet_neg
        d hd p hp)

/-- The underlying reference-fiber vertex represented by a coordinate. -/
def referenceFiberVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (p : labeling.data.toAFiberCoordinates.P) : V :=
  ((labeling.data.toAFiberCoordinates.coord 0 p :
    {x : V // x ∈
      branchFiber Γ labeling.data.toAFiberCoordinates.u
        (labeling.data.toAFiberCoordinates.a 0)}) : V)

/-- The underlying reference-fiber vertices represented by solutions of the
reference matching equation. -/
noncomputable def referenceMatchingSolutionVertexSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0) : Finset V :=
  (labeling.referenceMatchingSolutionSet d hd).image
    (labeling.referenceFiberVertex)

@[simp] theorem mem_referenceMatchingSolutionVertexSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0) (x : V) :
    x ∈ labeling.referenceMatchingSolutionVertexSet d hd ↔
      ∃ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.referenceMatchingSolutionSet d hd ∧
          labeling.referenceFiberVertex p = x := by
  simp [referenceMatchingSolutionVertexSet]

/-- The fixed vertices in the underlying reference A-fiber for the A-fixing
reflection. -/
noncomputable def aFiberReflectionFixedReferenceVertexSet
    (labeling : BranchOrbitABCReflectionLabeling h) : Finset V :=
  (labeling.data.toAFiberCoordinates.fiber 0).filter fun x =>
    h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) x = x

@[simp] theorem mem_aFiberReflectionFixedReferenceVertexSet
    (labeling : BranchOrbitABCReflectionLabeling h) (x : V) :
    x ∈ labeling.aFiberReflectionFixedReferenceVertexSet ↔
      x ∈ labeling.data.toAFiberCoordinates.fiber 0 ∧
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) x = x := by
  simp [aFiberReflectionFixedReferenceVertexSet]

/-- The named solution set is the support complement of the reference
matching-rotation permutation. -/
theorem referenceMatchingSolutionSet_eq_matchingRotationPerm_support_compl
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0) :
    labeling.referenceMatchingSolutionSet d hd =
      (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
        d 0 hd).supportᶜ := by
  ext p
  rw [mem_referenceMatchingSolutionSet,
    AFiberRotationEquivariance.mem_matchingRotationPerm_support_compl_iff]

/-- Boundary form: the reference matching solution set is contained in the
fixed-coordinate part of the A-fixing reflection. -/
structure ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  reference_matching_solution_subset_aFiberReflectionSupport_compl :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      labeling.referenceMatchingSolutionSet d hd ⊆
        labeling.aFiberReflectionSupportᶜ

/-- Boundary form closer to the label-exchange proof target: a point of the
A-fixing reflection moving support cannot solve the reference matching equation.
This is equivalent to the support-complement formulation above, but avoids
starting a natural proof from a Finset-complement inclusion. -/
structure ReferenceRotationMovingSolutionExclusionBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  no_moving_reference_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          p ∉ labeling.referenceMatchingSolutionSet d hd

/-- The missing same-target label-exchange input for the reference side:
when a moving A-fixing coordinate solves the reference matching equation at
offset `d`, the reflected source coordinate solves the same equation with the
same rotated target. -/
structure ReferenceMatchingAFixingSourceExchangeBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  source_exchange :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd) p =
            labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd)
              (labeling.aFiberReflectionCoordPerm p) =
            labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p

/-- Adjacency form of the same-target source exchange: from a reference
solution at a moving source coordinate, the reflected source coordinate is also
adjacent to the same rotated target vertex. -/
structure ReferenceMatchingAFixingCrossAdjacencyBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  cross_adj_of_reference_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          p ∈ labeling.referenceMatchingSolutionSet d hd →
            Γ.Adj
              (((labeling.data.toAFiberCoordinates.coord 0
                  (labeling.aFiberReflectionCoordPerm p) :
                {x : V // x ∈
                  branchFiber Γ labeling.data.toAFiberCoordinates.u
                    (labeling.data.toAFiberCoordinates.a 0)}) : V))
              (((labeling.data.toAFiberCoordinates.coord (0 + d)
                  (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
                {x : V // x ∈
                  branchFiber Γ labeling.data.toAFiberCoordinates.u
                    (labeling.data.toAFiberCoordinates.a (0 + d))}) : V))

/-- Same-offset mate-closure of reference matching solutions on the A-fixing
moving support.  This is deliberately separated from the raw reflection
transport, which only gives the proven `d` to `-d` statement. -/
structure ReferenceMatchingAFixingSupportMateBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  reflected_solution_of_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          p ∈ labeling.referenceMatchingSolutionSet d hd →
            labeling.aFiberReflectionCoordPerm p ∈
              labeling.referenceMatchingSolutionSet d hd

/-- Support-pair exclusion form suggested by the label-exchange direction:
the whole two-point A-fixing moving support cannot lie in one reference
matching solution set.  By itself this is weaker than pointwise
support-complement; converting it to pointwise exclusion also needs the
same-offset mate-closure boundary above. -/
structure ReferenceMatchingAFixingSupportNoAllBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  not_all_support_reference_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ¬ ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.aFiberReflectionSupport →
            p ∈ labeling.referenceMatchingSolutionSet d hd

/-- Primitive paired-solution exclusion aligned with the theorem-level
reflection transport: a support point cannot solve the `d` reference equation
while its A-reflection solves the `-d` reference equation. -/
structure ReferenceMatchingAFixingNoPairedSolutionBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  no_paired_reference_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          ¬ (p ∈ labeling.referenceMatchingSolutionSet d hd ∧
              labeling.aFiberReflectionCoordPerm p ∈
                labeling.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd))

/-- The same-offset mate-closure is now a theorem-level consequence of
reflection transport plus the `d` to `-d` sign symmetry of reference matching
solution sets. -/
def referenceMatchingAFixingSupportMateBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) :
    ReferenceMatchingAFixingSupportMateBoundary labeling where
  reflected_solution_of_solution d hd p _hpSupport hpSolution :=
    labeling.aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet d hd p
      hpSolution

namespace ReferenceRotationMatchingSolutionVertexFixedBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Constructor from a pointwise Finset-membership version of the geometric
fixedness statement. -/
noncomputable def of_referenceMatchingSolutionSet_vertex_fixed
    (hfixed :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.referenceMatchingSolutionSet d hd →
            h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
                (labeling.referenceFiberVertex p) =
              labeling.referenceFiberVertex p) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling where
  reference_solution_vertex_fixed := by
    intro d hd p hmatch
    exact hfixed d hd p ((labeling.mem_referenceMatchingSolutionSet d hd p).2 hmatch)

/-- Constructor from inclusion of each solution vertex set into the underlying
fixed reference-fiber vertex set. -/
noncomputable def of_referenceMatchingSolutionVertexSet_subset_fixedReferenceVertexSet
    (hsubset :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        labeling.referenceMatchingSolutionVertexSet d hd ⊆
          labeling.aFiberReflectionFixedReferenceVertexSet) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling :=
  of_referenceMatchingSolutionSet_vertex_fixed (labeling := labeling) (by
    intro d hd p hp
    have hv :
        labeling.referenceFiberVertex p ∈
          labeling.referenceMatchingSolutionVertexSet d hd := by
      exact (labeling.mem_referenceMatchingSolutionVertexSet d hd
        (labeling.referenceFiberVertex p)).2 ⟨p, hp, rfl⟩
    have hmem :
        labeling.referenceFiberVertex p ∈
          labeling.aFiberReflectionFixedReferenceVertexSet :=
      hsubset d hd hv
    exact (labeling.mem_aFiberReflectionFixedReferenceVertexSet
      (labeling.referenceFiberVertex p)).1 hmem |>.2)

/-- Constructor from containment of reference matching solutions in
`aFiberReflectionSupportᶜ`. -/
noncomputable def of_referenceMatchingSolutionSet_subset_aFiberReflectionSupport_compl
    (hsubset :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        labeling.referenceMatchingSolutionSet d hd ⊆
          labeling.aFiberReflectionSupportᶜ) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling :=
  of_referenceMatchingSolutionSet_vertex_fixed (labeling := labeling) (by
    intro d hd p hp
    have hpFixed : p ∈ labeling.aFiberReflectionSupportᶜ := hsubset d hd hp
    have hpNotSupport : p ∉ labeling.aFiberReflectionSupport :=
      Finset.mem_compl.mp hpFixed
    have hpCoordFixed : labeling.aFiberReflectionCoordPerm p = p := by
      by_contra hmove
      exact hpNotSupport ((labeling.mem_aFiberReflectionSupport p).2 hmove)
    exact (labeling.aFiberReflectionCoordPerm_fixed_iff_vertex_fixed p).1
      hpCoordFixed)

/-- Constructor from containment of the matching-rotation fixed coordinates in
the A-fixing reflection fixed-coordinate part. -/
noncomputable def of_matchingRotationPerm_support_compl_subset_aFiberReflectionSupport_compl
    (hsubset :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
          d 0 hd).supportᶜ ⊆
          labeling.aFiberReflectionSupportᶜ) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling :=
  of_referenceMatchingSolutionSet_subset_aFiberReflectionSupport_compl
    (labeling := labeling) (by
      intro d hd p hp
      exact hsubset d hd
        (by
          simpa [labeling.referenceMatchingSolutionSet_eq_matchingRotationPerm_support_compl
            d hd] using hp))

end ReferenceRotationMatchingSolutionVertexFixedBoundary

namespace ReferenceRotationMatchingSolutionAFixingSupportComplBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Rephrase the support-complement target as exclusion of moving-support
reference solutions. -/
def toReferenceRotationMovingSolutionExclusionBoundary
    (boundary :
      ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling) :
    ReferenceRotationMovingSolutionExclusionBoundary labeling where
  no_moving_reference_solution d hd p hpSupport hpSolution := by
    have hpCompl :
        p ∈ labeling.aFiberReflectionSupportᶜ :=
      boundary.reference_matching_solution_subset_aFiberReflectionSupport_compl
        d hd hpSolution
    exact (Finset.mem_compl.mp hpCompl) hpSupport

/-- Collapse the support-complement boundary to the geometric vertex-fixed
boundary. -/
noncomputable def toReferenceRotationMatchingSolutionVertexFixedBoundary
    (boundary :
      ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling :=
  ReferenceRotationMatchingSolutionVertexFixedBoundary.of_referenceMatchingSolutionSet_subset_aFiberReflectionSupport_compl
      (labeling := labeling)
      boundary.reference_matching_solution_subset_aFiberReflectionSupport_compl

/-- Collapse the support-complement boundary to the coordinate fixedness
boundary for reference matching solutions. -/
noncomputable def toReferenceRotationEquationAFixingFixedBoundary
    (boundary :
      ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling) :
    ReferenceRotationEquationAFixingFixedBoundary labeling :=
  boundary.toReferenceRotationMatchingSolutionVertexFixedBoundary
    |>.toReferenceRotationEquationAFixingFixedBoundary

/-- Direct route from the support-complement form to the
reference-to-midpoint comparison boundary. -/
noncomputable def toReferenceRotationToMidpointReflectionBoundary
    (boundary :
      ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling) :
    ReferenceRotationToMidpointReflectionBoundary labeling :=
  ReferenceRotationToMidpointReflectionBoundary.of_aFixingFixed
    boundary.toReferenceRotationEquationAFixingFixedBoundary

/-- Support-complement immediately forbids the paired `d`/`-d` reference
solution pattern on the A-fixing moving support. -/
def toReferenceMatchingAFixingNoPairedSolutionBoundary
    (boundary :
      ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling) :
    ReferenceMatchingAFixingNoPairedSolutionBoundary labeling where
  no_paired_reference_solution d hd p hpSupport hpair := by
    have hpCompl :
        p ∈ labeling.aFiberReflectionSupportᶜ :=
      boundary.reference_matching_solution_subset_aFiberReflectionSupport_compl
        d hd hpair.1
    exact (Finset.mem_compl.mp hpCompl) hpSupport

end ReferenceRotationMatchingSolutionAFixingSupportComplBoundary

namespace ReferenceRotationMovingSolutionExclusionBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Constructor from the direct support-exclusion form: every reference
matching solution lies outside the A-fixing moving support. -/
def of_referenceMatchingSolution_not_mem_aFiberReflectionSupport
    (hnot :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.referenceMatchingSolutionSet d hd →
            p ∉ labeling.aFiberReflectionSupport) :
    ReferenceRotationMovingSolutionExclusionBoundary labeling where
  no_moving_reference_solution d hd p hpSupport hpSolution := by
    exact hnot d hd p hpSolution hpSupport

/-- Constructor from a direct inequality form of the reference matching
equation on the A-fixing moving support. -/
def of_no_matching_equation
    (hno :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.aFiberReflectionSupport →
            AFiberCoordinates.matchingEquiv h.isMoore
                labeling.data.toAFiberCoordinates 0 (0 + d)
                (index_ne_add_of_ne_zero hd) p ≠
              labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
    ReferenceRotationMovingSolutionExclusionBoundary labeling where
  no_moving_reference_solution d hd p hpSupport hpSolution := by
    exact hno d hd p hpSupport
      ((labeling.mem_referenceMatchingSolutionSet d hd p).1 hpSolution)

/-- Moving-support exclusion is the pointwise form of the support-complement
reference-side boundary. -/
def toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    (boundary : ReferenceRotationMovingSolutionExclusionBoundary labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling where
  reference_matching_solution_subset_aFiberReflectionSupport_compl := by
    intro d hd p hpSolution
    exact Finset.mem_compl.mpr (by
      intro hpSupport
      exact boundary.no_moving_reference_solution d hd p hpSupport hpSolution)

/-- Moving-support exclusion fixes all reference matching solution vertices
under the A-fixing reflection. -/
noncomputable def toReferenceRotationMatchingSolutionVertexFixedBoundary
    (boundary : ReferenceRotationMovingSolutionExclusionBoundary labeling) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling :=
  boundary.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    |>.toReferenceRotationMatchingSolutionVertexFixedBoundary

/-- Moving-support exclusion gives the direct reference-to-midpoint comparison
boundary through the existing support-complement route. -/
noncomputable def toReferenceRotationToMidpointReflectionBoundary
    (boundary : ReferenceRotationMovingSolutionExclusionBoundary labeling) :
    ReferenceRotationToMidpointReflectionBoundary labeling :=
  boundary.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    |>.toReferenceRotationToMidpointReflectionBoundary

/-- Moving-support exclusion is also the direct paired-solution exclusion:
the first component of a paired solution is already impossible. -/
def toReferenceMatchingAFixingNoPairedSolutionBoundary
    (boundary : ReferenceRotationMovingSolutionExclusionBoundary labeling) :
    ReferenceMatchingAFixingNoPairedSolutionBoundary labeling where
  no_paired_reference_solution d hd p hpSupport hpair :=
    boundary.no_moving_reference_solution d hd p hpSupport hpair.1

end ReferenceRotationMovingSolutionExclusionBoundary

namespace ReferenceMatchingAFixingSourceExchangeBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Same-target source exchange rules out moving-support reference solutions:
the matching permutation is injective, so two sources with the same target
must be equal, contradicting membership in the A-fixing moving support. -/
def toReferenceRotationMovingSolutionExclusionBoundary
    (boundary : ReferenceMatchingAFixingSourceExchangeBoundary labeling) :
    ReferenceRotationMovingSolutionExclusionBoundary labeling where
  no_moving_reference_solution d hd p hpSupport hpSolution := by
    have hpMatch :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p :=
      (labeling.mem_referenceMatchingSolutionSet d hd p).1 hpSolution
    have hApMatch :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd)
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p :=
      boundary.source_exchange d hd p hpSupport hpMatch
    have hsame :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd)
            (labeling.aFiberReflectionCoordPerm p) =
          AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p :=
      hApMatch.trans hpMatch.symm
    have hfixed : labeling.aFiberReflectionCoordPerm p = p :=
      (AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + d)
        (index_ne_add_of_ne_zero hd)).injective hsame
    exact ((labeling.mem_aFiberReflectionSupport p).1 hpSupport) hfixed

/-- Same-target source exchange gives the support-complement reference-side
boundary. -/
def toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    (boundary : ReferenceMatchingAFixingSourceExchangeBoundary labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling :=
  boundary.toReferenceRotationMovingSolutionExclusionBoundary
    |>.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary

/-- Same-target source exchange is equivalent to the same-target adjacency
form: once `p` is a reference solution, the exchanged matching equation says
that the reflected source is adjacent to the same rotated target. -/
def toReferenceMatchingAFixingCrossAdjacencyBoundary
    (boundary : ReferenceMatchingAFixingSourceExchangeBoundary labeling) :
    ReferenceMatchingAFixingCrossAdjacencyBoundary labeling where
  cross_adj_of_reference_solution := by
    intro d hd p hpSupport hpSolution
    have hpMatch :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p :=
      (labeling.mem_referenceMatchingSolutionSet d hd p).1 hpSolution
    have hApMatch :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd)
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p :=
      boundary.source_exchange d hd p hpSupport hpMatch
    exact
      (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore
        labeling.data.toAFiberCoordinates
        (index_ne_add_of_ne_zero hd)
        (labeling.aFiberReflectionCoordPerm p)
        (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p)).2
        hApMatch

/-- Same-target source exchange gives the reference-to-midpoint boundary
through the support-complement route. -/
noncomputable def toReferenceRotationToMidpointReflectionBoundary
    (boundary : ReferenceMatchingAFixingSourceExchangeBoundary labeling) :
    ReferenceRotationToMidpointReflectionBoundary labeling :=
  boundary.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    |>.toReferenceRotationToMidpointReflectionBoundary

/-- Same-target source exchange also supplies the paired-solution exclusion
form through moving-support exclusion. -/
def toReferenceMatchingAFixingNoPairedSolutionBoundary
    (boundary : ReferenceMatchingAFixingSourceExchangeBoundary labeling) :
    ReferenceMatchingAFixingNoPairedSolutionBoundary labeling :=
  boundary.toReferenceRotationMovingSolutionExclusionBoundary
    |>.toReferenceMatchingAFixingNoPairedSolutionBoundary

end ReferenceMatchingAFixingSourceExchangeBoundary

namespace ReferenceMatchingAFixingNoPairedSolutionBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Paired-solution exclusion is the exact primitive needed with the existing
reflection transport theorem to rule out moving-support reference solutions. -/
def toReferenceRotationMovingSolutionExclusionBoundary
    (boundary : ReferenceMatchingAFixingNoPairedSolutionBoundary labeling) :
    ReferenceRotationMovingSolutionExclusionBoundary labeling where
  no_moving_reference_solution d hd p hpSupport hpSolution := by
    exact
      boundary.no_paired_reference_solution d hd p hpSupport
        ⟨hpSolution,
          labeling.aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet_neg
            d hd p hpSolution⟩

/-- Paired-solution exclusion gives the standard support-complement boundary. -/
def toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    (boundary : ReferenceMatchingAFixingNoPairedSolutionBoundary labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling :=
  boundary.toReferenceRotationMovingSolutionExclusionBoundary
    |>.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary

end ReferenceMatchingAFixingNoPairedSolutionBoundary

namespace ReferenceMatchingAFixingSupportNoAllBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- A support-pair no-all statement plus same-offset mate-closure gives the
pointwise moving-support exclusion.  The support has exactly two points, so any
single support solution and its reflected mate would make the whole support a
solution set, contradicting `not_all_support_reference_solution`. -/
def toReferenceRotationMovingSolutionExclusionBoundary
    (boundary : ReferenceMatchingAFixingSupportNoAllBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (mate : ReferenceMatchingAFixingSupportMateBoundary labeling) :
    ReferenceRotationMovingSolutionExclusionBoundary labeling where
  no_moving_reference_solution d hd p hpSupport hpSolution := by
    have hApSolution :
        labeling.aFiberReflectionCoordPerm p ∈
          labeling.referenceMatchingSolutionSet d hd :=
      mate.reflected_solution_of_solution d hd p hpSupport hpSolution
    have hall :
        ∀ q : labeling.data.toAFiberCoordinates.P,
          q ∈ labeling.aFiberReflectionSupport →
            q ∈ labeling.referenceMatchingSolutionSet d hd := by
      intro q hq
      rcases
          (supportCard.mem_aFiberReflectionSupport_iff_eq_or_eq_reflection_of_mem
            hpSupport).1 hq with hqeq | hqeq
      · simpa [hqeq] using hpSolution
      · simpa [hqeq] using hApSolution
    exact boundary.not_all_support_reference_solution d hd hall

/-- Support-pair no-all plus same-offset mate-closure gives the standard
support-complement boundary. -/
def toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    (boundary : ReferenceMatchingAFixingSupportNoAllBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (mate : ReferenceMatchingAFixingSupportMateBoundary labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling :=
  (boundary.toReferenceRotationMovingSolutionExclusionBoundary supportCard mate)
    |>.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary

/-- Since same-offset mate-closure is now a theorem, the support-pair no-all
boundary plus the two-point support-card input gives pointwise moving-support
exclusion. -/
def toReferenceRotationMovingSolutionExclusionBoundary_of_reflectionSignSymmetry
    (boundary : ReferenceMatchingAFixingSupportNoAllBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    ReferenceRotationMovingSolutionExclusionBoundary labeling :=
  boundary.toReferenceRotationMovingSolutionExclusionBoundary supportCard
    labeling.referenceMatchingAFixingSupportMateBoundary

/-- Support-pair no-all plus the theorem-level same-offset mate-closure gives
the standard support-complement boundary. -/
def toReferenceRotationMatchingSolutionAFixingSupportComplBoundary_of_reflectionSignSymmetry
    (boundary : ReferenceMatchingAFixingSupportNoAllBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling :=
  boundary.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    supportCard labeling.referenceMatchingAFixingSupportMateBoundary

/-- Support-pair no-all plus same-offset mate closure also gives the paired
`d`/`-d` exclusion form. -/
def toReferenceMatchingAFixingNoPairedSolutionBoundary
    (boundary : ReferenceMatchingAFixingSupportNoAllBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (mate : ReferenceMatchingAFixingSupportMateBoundary labeling) :
    ReferenceMatchingAFixingNoPairedSolutionBoundary labeling :=
  (boundary.toReferenceRotationMovingSolutionExclusionBoundary supportCard mate)
    |>.toReferenceMatchingAFixingNoPairedSolutionBoundary

/-- Since same-offset mate closure is theorem-level, support-pair no-all plus
the two-point support-card input gives paired-solution exclusion. -/
def toReferenceMatchingAFixingNoPairedSolutionBoundary_of_reflectionSignSymmetry
    (boundary : ReferenceMatchingAFixingSupportNoAllBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    ReferenceMatchingAFixingNoPairedSolutionBoundary labeling :=
  boundary.toReferenceMatchingAFixingNoPairedSolutionBoundary supportCard
    labeling.referenceMatchingAFixingSupportMateBoundary

end ReferenceMatchingAFixingSupportNoAllBoundary

namespace ReferenceMatchingAFixingCrossAdjacencyBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Cross-adjacency gives the same-target source-exchange equation by the
branch-fiber matching criterion. -/
def toReferenceMatchingAFixingSourceExchangeBoundary
    (boundary : ReferenceMatchingAFixingCrossAdjacencyBoundary labeling) :
    ReferenceMatchingAFixingSourceExchangeBoundary labeling where
  source_exchange := by
    intro d hd p hpSupport hpMatch
    have hpSolution : p ∈ labeling.referenceMatchingSolutionSet d hd :=
      (labeling.mem_referenceMatchingSolutionSet d hd p).2 hpMatch
    exact
      AFiberCoordinates.matchingEquiv_eq_of_adj h.isMoore
        labeling.data.toAFiberCoordinates
        (index_ne_add_of_ne_zero hd)
        (boundary.cross_adj_of_reference_solution d hd p hpSupport hpSolution)

/-- Cross-adjacency rules out moving-support reference solutions. -/
def toReferenceRotationMovingSolutionExclusionBoundary
    (boundary : ReferenceMatchingAFixingCrossAdjacencyBoundary labeling) :
    ReferenceRotationMovingSolutionExclusionBoundary labeling :=
  boundary.toReferenceMatchingAFixingSourceExchangeBoundary
    |>.toReferenceRotationMovingSolutionExclusionBoundary

/-- Cross-adjacency gives the support-complement reference-side boundary. -/
def toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    (boundary : ReferenceMatchingAFixingCrossAdjacencyBoundary labeling) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling :=
  boundary.toReferenceMatchingAFixingSourceExchangeBoundary
    |>.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary

/-- Cross-adjacency gives the paired-solution exclusion through source
exchange and moving-support exclusion. -/
def toReferenceMatchingAFixingNoPairedSolutionBoundary
    (boundary : ReferenceMatchingAFixingCrossAdjacencyBoundary labeling) :
    ReferenceMatchingAFixingNoPairedSolutionBoundary labeling :=
  boundary.toReferenceMatchingAFixingSourceExchangeBoundary
    |>.toReferenceMatchingAFixingNoPairedSolutionBoundary

end ReferenceMatchingAFixingCrossAdjacencyBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
