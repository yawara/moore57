import Moore57.D19OnMoore57.BranchOrbit.ABCReflectionLabeling
import Moore57.D19OnMoore57.BranchOrbit.ABCMidpointReflection
import Moore57.D19OnMoore57.BranchOrbit.ABCMidpointExceptionSetBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionDoublingVertexPullbackBoundary

/-!
# Midpoint-middle support and the A-fixing support via rotation transport

The midpoint reflection on the middle fiber is the rotation conjugate of the
A-fixing reflection on the reference fiber: in the dihedral group `D₁₉`,
`t_m = r^m · t_0 · r^{-m}`.  In coordinates, this gives the bridge

  `p ∈ midpointMiddleSupport m ↔ (rot.coordPerm m 0).symm p ∈ aFiberReflectionSupport`

which translates the natural-language convention "$\theta$ is the same on all
fibers via rotation pull-back" into Lean's coordinate-system-independent form.
This file proves the bridge.

All vertex equalities are stated with the `(0 + m)` chart index to match the
existing infrastructure (`coord_coordPerm_apply_val`, `midpointMiddleCoordPerm_eq_iff`).
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Vertex-level dihedral identity: `t_m x = r^m (t_0 (r^{-m} x))`. -/
theorem midpointReflection_smul_eq_rotation_aFixingReflection_rotation_smul
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (x : V) :
    h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) x =
      h.rotation m
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (h.rotation (-m) x)) := by
  change h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) x =
    h.smul (DihedralGroup.r m)
      (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
        (h.smul (DihedralGroup.r (-m)) x))
  rw [← h.mul_smul, ← h.mul_smul]
  congr 1
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
  congr 1
  simp [BranchOrbitABCReflectionLabeling.midpointReflectionIndex]
  ring

/-- Vertex fixedness equivalence: `t_m` fixes `x` iff `t_0` fixes
`r^{-m} x`. -/
theorem midpointReflection_fixes_iff_aFixing_fixes_rotation_neg
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (x : V) :
    h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) x = x ↔
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (h.rotation (-m) x) = h.rotation (-m) x := by
  rw [labeling.midpointReflection_smul_eq_rotation_aFixingReflection_rotation_smul m x]
  constructor
  · intro hfix
    -- hfix: r^m (t_0 (r^{-m} x)) = x.  Apply r^{-m} to both sides.
    have h1 : h.rotation (-m) (h.rotation m
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (h.rotation (-m) x))) =
        h.rotation (-m) x :=
      congrArg (h.rotation (-m)) hfix
    have h2 : h.rotation (-m) (h.rotation m
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (h.rotation (-m) x))) =
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (h.rotation (-m) x) := by
      rw [show (h.rotation (-m) (h.rotation m
          (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (h.rotation (-m) x)))) =
          h.rotation ((-m) + m)
            (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
              (h.rotation (-m) x)) from by
        rw [h.rotation_add]; rfl]
      simp
    exact h2.symm.trans h1
  · intro hfix
    -- hfix: t_0 (r^{-m} x) = r^{-m} x.  Apply r^m to both sides.
    have h1 :
        h.rotation m (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (h.rotation (-m) x)) =
          h.rotation m (h.rotation (-m) x) :=
      congrArg (h.rotation m) hfix
    rw [show (h.rotation m (h.rotation (-m) x)) =
        h.rotation (m + (-m)) x from by
      rw [h.rotation_add]; rfl] at h1
    simpa using h1

/-- Bridge: a coordinate `p` is in `midpointMiddleSupport m` iff its
rotation pre-image `(rot.coordPerm m 0).symm p` is in `aFiberReflectionSupport`. -/
theorem mem_midpointMiddleSupport_iff_rotationCoordPerm_symm_mem_aFiberReflectionSupport
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) :
    p ∈ labeling.midpointMiddleSupport m ↔
      (labeling.data.toAFiberRotationEquivariance.coordPerm m 0).symm p ∈
        labeling.aFiberReflectionSupport := by
  classical
  let coords := labeling.data.toAFiberCoordinates
  let rot := labeling.data.toAFiberRotationEquivariance
  set q := (rot.coordPerm m 0).symm p with hq_def
  have hq_apply : rot.coordPerm m 0 q = p := by simp [q]
  -- Chart relation: coord (0 + m) p = h.rotation m (coord 0 q).
  have hp_vertex_eq :
      ((coords.coord (0 + m) p :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V) =
        h.rotation m
          (((coords.coord 0 q :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
    have hthm :=
      AFiberRotationEquivariance.coord_coordPerm_apply_val
        (rot := rot) (d := m) (i := 0) (p := q)
    rw [hq_apply] at hthm
    exact hthm
  -- Inverse chart relation: coord 0 q = h.rotation (-m) (coord (0+m) p).
  have hq_vertex_eq :
      ((coords.coord 0 q :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V) =
        h.rotation (-m)
          (((coords.coord (0 + m) p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V)) := by
    apply (h.rotation m).injective
    rw [← hp_vertex_eq]
    rw [show h.rotation m (h.rotation (-m)
          (((coords.coord (0 + m) p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V))) =
          h.rotation (m + (-m))
            (((coords.coord (0 + m) p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V)) from by
      rw [h.rotation_add]; rfl]
    simp
  -- Unfold the LHS and RHS support memberships to coord-perm inequalities.
  rw [labeling.mem_midpointMiddleSupport m p,
    labeling.mem_aFiberReflectionSupport q]
  -- LHS: midpointMiddleCoordPerm m p ≠ p
  -- RHS: aFiberReflectionCoordPerm q ≠ q
  -- Bridge: both reduce to vertex (in)equalities related by `hq_vertex_eq`.
  constructor
  · intro hp_moved hq_fixed
    -- hq_fixed: aFiberReflectionCoordPerm q = q
    apply hp_moved
    -- Goal: midpointMiddleCoordPerm m p = p
    have hq_fixed_vertex :
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (((coords.coord 0 q :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) =
          (((coords.coord 0 q :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
      have hraw := labeling.coord_aFiberReflectionCoordPerm_apply_val q
      rw [hq_fixed] at hraw
      exact hraw.symm
    rw [hq_vertex_eq] at hq_fixed_vertex
    have hp_fixed_vertex :
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
            (((coords.coord (0 + m) p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V)) =
          (((coords.coord (0 + m) p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V)) :=
      (labeling.midpointReflection_fixes_iff_aFixing_fixes_rotation_neg m _).mpr
        hq_fixed_vertex
    exact (labeling.midpointMiddleCoordPerm_eq_iff m p p).mpr hp_fixed_vertex
  · intro hq_moved hp_fixed
    -- hp_fixed: midpointMiddleCoordPerm m p = p
    apply hq_moved
    have hp_fixed_vertex :
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
            (((coords.coord (0 + m) p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V)) =
          (((coords.coord (0 + m) p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V)) :=
      (labeling.midpointMiddleCoordPerm_eq_iff m p p).mp hp_fixed
    have hq_fixed_vertex :
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (h.rotation (-m)
              (((coords.coord (0 + m) p :
                {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V))) =
          h.rotation (-m)
            (((coords.coord (0 + m) p :
              {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + m))}) : V)) :=
      (labeling.midpointReflection_fixes_iff_aFixing_fixes_rotation_neg m _).mp
        hp_fixed_vertex
    rw [← hq_vertex_eq] at hq_fixed_vertex
    -- Now hq_fixed_vertex: h.smul (sr aFixing) (coord 0 q) = coord 0 q.
    -- Want: aFiberReflectionCoordPerm q = q
    have hcoord_eq :
        ((coords.coord 0 (labeling.aFiberReflectionCoordPerm q) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V) =
          (((coords.coord 0 q :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
      rw [labeling.coord_aFiberReflectionCoordPerm_apply_val]
      exact hq_fixed_vertex
    exact (coords.coord 0).injective (Subtype.ext hcoord_eq)

end BranchOrbitABCReflectionLabeling

end

end Moore57
