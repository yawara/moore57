import Moore57.BranchOrbitABCFromCenterBBase
import Moore57.BranchOrbitABCReflectionLabeling
import Moore57.Foundations.GroupAction.BranchFiberAction
import Moore57.RotationFixedCenter

set_option maxRecDepth 1000

/-!
# Reflection avoidance for the B-base orbit selection

For a reflection-compatible labeling `BranchOrbitABCReflectionLabeling h`, the
B-base orbit selection input has the avoidance property: every reflected
base vertex lands outside the B-fiber union.

This follows from:
* `reflection_b0_eq_c0`: `sr k · b0 = c0` (from the labeling),
* `smul_mem_branchFiber_iff`: reflection takes branch fibers to branch
  fibers over the reflected center-neighbor,
* `branchFiber_disjoint_of_ne`: branch fibers over distinct neighbors of
  the center are disjoint (Moore57 μ=1),
* `c0_not_mem_rotationOrbit_b0`: `c0` is not in the rotation orbit of `b0`
  (B-orbit and C-orbit are disjoint).
-/

namespace Moore57

open Finset

namespace BranchOrbitABCReflectionLabeling

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {h : D19ActsOnMoore57 V Γ}

/-- The B-base orbit selection input from a reflection-compatible labeling. -/
noncomputable def toOrbitBaseSelectionInputB
    (labeling : BranchOrbitABCReflectionLabeling h) :
    OrbitBaseSelectionInput h :=
  labeling.data.toOrbitBaseSelectionInputB

/-- The orbit base from B is in the base B-fiber. -/
theorem base_mem_branchFiber_b0
    (labeling : BranchOrbitABCReflectionLabeling h) (r : Fin 56) :
    labeling.toOrbitBaseSelectionInputB.base r ∈
      branchFiber Γ labeling.data.u labeling.data.b0 := by
  classical
  -- Use coord_mem then rewrite under `mem_branchFiber`.
  have hprop : labeling.toOrbitBaseSelectionInputB.base r ∈
      branchFiber Γ labeling.data.toAFiberCoordinatesB.u
        (labeling.data.toAFiberCoordinatesB.a 0) := by
    unfold toOrbitBaseSelectionInputB
      BranchOrbitABCFromCenter.toOrbitBaseSelectionInputB
      AFiberCoordinates.ofRotationOrbitOfMoved_toOrbitBaseSelectionInput
      AFiberCoordinates.toOrbitBaseSelectionInputOfMoore
    exact labeling.data.toAFiberCoordinatesB.coord_mem 0
      ((AFiberCoordinates.fin56EquivOfMoore
        (coords := labeling.data.toAFiberCoordinatesB) h.isMoore) r)
  rw [mem_branchFiber] at hprop ⊢
  refine ⟨hprop.1, ?_⟩
  have ha : labeling.data.toAFiberCoordinatesB.a 0 = labeling.data.b0 := by
    show h.rotation 0 labeling.data.b0 = labeling.data.b0
    simp
  rw [ha] at hprop
  exact hprop.2

/-- The reflection avoidance condition: every B-base reflection sends the
base vertex to a C-fiber, which is disjoint from the B-fiber union. -/
theorem reflection_not_mem_orbitFamilyUnionB
    (labeling : BranchOrbitABCReflectionLabeling h) :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr labeling.k)
          (labeling.toOrbitBaseSelectionInputB.base r) ∉
        labeling.toOrbitBaseSelectionInputB.orbitFamilyUnion := by
  intro r hmem
  -- Step 1: orbitFamilyUnion = allFibers (= union of B-fibers).
  have hfam :=
    labeling.data.toOrbitBaseSelectionInputB_orbitFamilyUnion_eq_allFibers
  -- Rewrite via unfold; note `toOrbitBaseSelectionInputB` is defined the
  -- same way in both namespaces.
  unfold toOrbitBaseSelectionInputB at hmem
  rw [hfam] at hmem
  rw [labeling.data.toAFiberCoordinatesB.mem_allFibers_iff] at hmem
  obtain ⟨i, hi⟩ := hmem
  -- hi : sr k · base r ∈ branchFiber u (a i) where a i = h.rotation i b0
  have hai : labeling.data.toAFiberCoordinatesB.a i = h.rotation i labeling.data.b0 := by
    show h.rotation i labeling.data.b0 = h.rotation i labeling.data.b0
    rfl
  have hu' : labeling.data.toAFiberCoordinatesB.u = labeling.data.u := rfl
  rw [hu', hai] at hi
  -- hi : sr k · base r ∈ branchFiber u (h.rotation i b0)
  -- Step 2: base r ∈ branchFiber u b0 (from base_mem_branchFiber_b0).
  have hbase := labeling.base_mem_branchFiber_b0 r
  -- Step 3: sr k fixes u.
  have hu_smul :
      h.smul (DihedralGroup.sr labeling.k) labeling.data.u = labeling.data.u := by
    rw [labeling.data.u_eq_rotationFixedCenter]
    exact h.reflection_smul_rotationFixedCenter labeling.k
  -- Step 4: sr k · b0 = c0.
  have hsmul_b0 :
      h.smul (DihedralGroup.sr labeling.k) labeling.data.b0 = labeling.data.c0 :=
    labeling.reflection_b0_eq_c0
  -- Step 5: sr k · base r ∈ branchFiber u c0.
  have hmemc :
      h.smul (DihedralGroup.sr labeling.k)
          (labeling.toOrbitBaseSelectionInputB.base r) ∈
        branchFiber Γ labeling.data.u labeling.data.c0 := by
    rw [← hsmul_b0]
    exact (h.smul_mem_branchFiber_iff (DihedralGroup.sr labeling.k)
      (b := labeling.data.b0)
      (x := labeling.toOrbitBaseSelectionInputB.base r) hu_smul).mpr hbase
  -- Step 6: hi gives sr k · base r ∈ branchFiber u (h.rotation i b0).
  -- Combined with hmemc (in branchFiber u c0), branch fiber disjointness
  -- forces h.rotation i b0 = c0, contradicting c0_not_mem_rotationOrbit_b0.
  by_cases hne : h.rotation i labeling.data.b0 = labeling.data.c0
  · exact labeling.data.c0_not_mem_rotationOrbit_b0 i hne
  · -- The two branchFibers are disjoint; hi and hmemc give a common element.
    have hadj_i : Γ.Adj labeling.data.u (h.rotation i labeling.data.b0) := by
      -- Rotation preserves edges and fixes u.
      have := (h.smul_adj (DihedralGroup.r i) labeling.data.u labeling.data.b0).mp
        labeling.data.b0_adj
      rwa [show h.smul (DihedralGroup.r i) labeling.data.u = labeling.data.u from
        labeling.data.u_fixed i,
        show h.smul (DihedralGroup.r i) labeling.data.b0 = h.rotation i labeling.data.b0
          from rfl] at this
    have hadj_c : Γ.Adj labeling.data.u labeling.data.c0 := labeling.data.c0_adj
    have hdisj := h.isMoore.branchFiber_disjoint_of_ne hadj_i hadj_c hne
    exact Finset.disjoint_left.mp hdisj hi hmemc

end BranchOrbitABCReflectionLabeling

end Moore57
