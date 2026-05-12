import Moore57.D19OnMoore57.BranchOrbit.ABCReflectionLabeling
import Moore57.D19OnMoore57.AFiber.MatchingExceptionSetBoundary
import Moore57.D19OnMoore57.AFiber.MidpointReflectionCriterion
import Moore57.D19OnMoore57.Reflection.FixedCenterLeafBoundary

/-!
# Midpoint reflections, exception sets, and reference bridge

This file unifies two thematic layers:

* **Midpoint reflection machinery**: the reflection with parameter `k - 2*m`
  centered at A-branch `m` (`midpointReflectionIndex`,
  `toAFiberMidpointReflectionEquivariance`,
  `midpointReflectionCoordPerm`/`midpointMiddleCoordPerm`,
  `midpointMiddleSupport`), the midpoint-equation and midpoint-exception sets,
  and the midpoint-reflection criterion (`MidpointReflectionCriterionBoundary`)
  with its constructors from fixed-common-neighbor and fixed-center-leaf
  boundaries.
* **Reference exception-set bridge**: `midpointOf`, the
  `MidpointMiddleSupportCardTwoBoundary` and
  `MidpointMiddleFixedNeighborCardBoundary` packages, the comparison between
  the reference rotation equation and the midpoint reflection equation
  (`ReferenceRotationToMidpointReflectionBoundary`,
  `ReferenceRotationEquationAFixingFixedBoundary`), and the constructor of
  `ReferenceFiberMatchingExceptionSetTwo` from the midpoint inputs.
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

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-! ## Midpoint reflection machinery -/

/-- The reflection parameter whose axis is centered at the A-branch index
`m`.  If `aFixingReflectionIndex` acts by `i ↦ -i`, this one acts by
`i ↦ 2 * m - i`. -/
noncomputable def midpointReflectionIndex
    (labeling : BranchOrbitABCReflectionLabeling h) (m : ZMod 19) :
    ZMod 19 :=
  labeling.aFixingReflectionIndex - (2 : ZMod 19) * m

/-- The midpoint reflection sends A-branch index `i` to `2 * m - i`. -/
noncomputable def toAFiberMidpointReflectionEquivariance
    (labeling : BranchOrbitABCReflectionLabeling h) (m : ZMod 19) :
    AFiberReflectionEquivariance h labeling.data.toAFiberCoordinates
      (labeling.midpointReflectionIndex m)
      (fun i : ZMod 19 => (2 : ZMod 19) * m - i) where
  reflection_u := by
    rw [BranchOrbitABCFromCenter.toAFiberCoordinates_u,
      labeling.data.u_eq_rotationFixedCenter]
    exact h.reflection_smul_rotationFixedCenter
      (labeling.midpointReflectionIndex m)
  reflection_a := by
    intro i
    have hgroup :
        DihedralGroup.sr (labeling.midpointReflectionIndex m + i) =
          DihedralGroup.r ((2 : ZMod 19) * m - i) *
            DihedralGroup.sr labeling.aFixingReflectionIndex := by
      rw [DihedralGroup.r_mul_sr]
      congr 1
      simp [midpointReflectionIndex]
      ring
    calc
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
          (labeling.data.toAFiberCoordinates.a i)
          = h.smul
              (DihedralGroup.sr (labeling.midpointReflectionIndex m))
              (h.smul (DihedralGroup.r i) labeling.data.a0) := by
                rfl
      _ = h.smul
            (DihedralGroup.sr (labeling.midpointReflectionIndex m) *
              DihedralGroup.r i) labeling.data.a0 := by
              rw [← h.mul_smul]
      _ = h.smul
            (DihedralGroup.sr (labeling.midpointReflectionIndex m + i))
            labeling.data.a0 := by
              rw [DihedralGroup.sr_mul_r]
      _ = h.smul
            (DihedralGroup.r ((2 : ZMod 19) * m - i) *
              DihedralGroup.sr labeling.aFixingReflectionIndex)
            labeling.data.a0 := by
              rw [hgroup]
      _ = h.rotation ((2 : ZMod 19) * m - i)
            (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
              labeling.data.a0) := by
              rw [h.mul_smul]
              rfl
      _ = h.rotation ((2 : ZMod 19) * m - i) labeling.data.a0 := by
              rw [labeling.aFixingReflectionIndex_spec]
      _ = labeling.data.toAFiberCoordinates.a ((2 : ZMod 19) * m - i) := by
              rfl

/-- The coordinate permutation induced by the midpoint reflection from the
reference A-fiber `0` to the A-fiber `2 * m`. -/
noncomputable def midpointReflectionCoordPerm
    (labeling : BranchOrbitABCReflectionLabeling h) (m : ZMod 19) :
    Equiv.Perm labeling.data.toAFiberCoordinates.P :=
  (labeling.toAFiberMidpointReflectionEquivariance m).coordPerm 0

/-- The coordinate permutation induced by the midpoint reflection on its
fixed middle A-fiber `m`. -/
noncomputable def midpointMiddleCoordPerm
    (labeling : BranchOrbitABCReflectionLabeling h) (m : ZMod 19) :
    Equiv.Perm labeling.data.toAFiberCoordinates.P :=
  (labeling.toAFiberMidpointReflectionEquivariance m).coordPerm (0 + m)

/-- The support of the midpoint reflection on the fixed middle A-fiber.  This
is the Lean analogue of the exceptional set `E` at midpoint `m`. -/
noncomputable def midpointMiddleSupport
    (labeling : BranchOrbitABCReflectionLabeling h) (m : ZMod 19) :
    Finset labeling.data.toAFiberCoordinates.P := by
  classical
  letI := labeling.data.toAFiberCoordinates.P_fintype
  exact (labeling.toAFiberMidpointReflectionEquivariance m).supportAt (0 + m)

@[simp] theorem mem_midpointMiddleSupport
    (labeling : BranchOrbitABCReflectionLabeling h) (m : ZMod 19)
    (p : labeling.data.toAFiberCoordinates.P) :
    p ∈ labeling.midpointMiddleSupport m ↔
      labeling.midpointMiddleCoordPerm m p ≠ p := by
  classical
  letI := labeling.data.toAFiberCoordinates.P_fintype
  simp [midpointMiddleSupport, midpointMiddleCoordPerm,
    AFiberReflectionEquivariance.supportAt]

/-- Reading the target chart after the midpoint reflection coordinate
permutation gives the reflected reference-fiber vertex. -/
@[simp] theorem coord_midpointReflectionCoordPerm_apply_val
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) :
    ((labeling.data.toAFiberCoordinates.coord ((2 : ZMod 19) * m - 0)
        (labeling.midpointReflectionCoordPerm m p) :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a ((2 : ZMod 19) * m - 0))}) : V) =
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
        (((labeling.data.toAFiberCoordinates.coord 0 p :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a 0)}) : V)) := by
  simpa [midpointReflectionCoordPerm] using
    AFiberReflectionEquivariance.coord_coordPerm_apply_val
      (ref := labeling.toAFiberMidpointReflectionEquivariance m)
      (i := 0) (p := p)

/-- Coordinate equality for the midpoint reflection is equivalent to equality
of the reflected reference-fiber representative with the target representative
in the `2 * m` fiber. -/
theorem midpointReflectionCoordPerm_eq_iff
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (p q : labeling.data.toAFiberCoordinates.P) :
    labeling.midpointReflectionCoordPerm m p = q ↔
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
          (((labeling.data.toAFiberCoordinates.coord 0 p :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a 0)}) : V)) =
        (((labeling.data.toAFiberCoordinates.coord ((2 : ZMod 19) * m - 0) q :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a ((2 : ZMod 19) * m - 0))}) : V)) := by
  simpa [midpointReflectionCoordPerm] using
    AFiberReflectionEquivariance.coordPerm_eq_iff
      (ref := labeling.toAFiberMidpointReflectionEquivariance m)
      (i := 0) p q

/-- Reading the middle chart after the midpoint reflection coordinate
permutation gives the reflected middle-fiber vertex. -/
@[simp] theorem coord_midpointMiddleCoordPerm_apply_val
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) :
    ((labeling.data.toAFiberCoordinates.coord ((2 : ZMod 19) * m - (0 + m))
        (labeling.midpointMiddleCoordPerm m p) :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a
            ((2 : ZMod 19) * m - (0 + m)))}) : V) =
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
        (((labeling.data.toAFiberCoordinates.coord (0 + m) p :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a (0 + m))}) : V)) := by
  simpa [midpointMiddleCoordPerm] using
    AFiberReflectionEquivariance.coord_coordPerm_apply_val
      (ref := labeling.toAFiberMidpointReflectionEquivariance m)
      (i := 0 + m) (p := p)

theorem zero_ne_of_ne_zero {m : ZMod 19} (hm : m ≠ 0) : (0 : ZMod 19) ≠ m := by
  intro h0
  exact hm h0.symm

theorem zero_ne_two_mul_sub_zero_of_ne_zero {m : ZMod 19} (hm : m ≠ 0) :
    (0 : ZMod 19) ≠ (2 : ZMod 19) * m - 0 := by
  simpa using (two_mul_ne_zero_zmod19 hm).symm

/-- The midpoint-equation solution set from natural-language Lemma 6.1:
the matching from `L_0` to `L_{2m}` agrees with the midpoint reflection image. -/
noncomputable def midpointEquationSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0) :
    Finset labeling.data.toAFiberCoordinates.P := by
  classical
  letI := labeling.data.toAFiberCoordinates.P_fintype
  exact
    (Finset.univ : Finset labeling.data.toAFiberCoordinates.P).filter fun p =>
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates 0 (0 + (m + m))
          (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)) p =
        labeling.midpointReflectionCoordPerm m p

@[simp] theorem mem_midpointEquationSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    p ∈ labeling.midpointEquationSet m hm ↔
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates 0 (0 + (m + m))
          (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)) p =
        labeling.midpointReflectionCoordPerm m p := by
  classical
  letI := labeling.data.toAFiberCoordinates.P_fintype
  simp [midpointEquationSet]

/-- The midpoint-exception set `S_m`: reference coordinates whose matched
point in the middle fiber lies in the moving support of the midpoint
reflection on that middle fiber. -/
noncomputable def midpointExceptionSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0) :
    Finset labeling.data.toAFiberCoordinates.P := by
  classical
  letI := labeling.data.toAFiberCoordinates.P_fintype
  exact
    (Finset.univ : Finset labeling.data.toAFiberCoordinates.P).filter fun p =>
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates 0 (0 + m)
          (index_ne_add_of_ne_zero hm) p ∈
        labeling.midpointMiddleSupport m

@[simp] theorem mem_midpointExceptionSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    p ∈ labeling.midpointExceptionSet m hm ↔
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates 0 (0 + m)
          (index_ne_add_of_ne_zero hm) p ∈
        labeling.midpointMiddleSupport m := by
  classical
  letI := labeling.data.toAFiberCoordinates.P_fintype
  simp [midpointExceptionSet]

/-- Natural-language midpoint criterion, forward direction: every solution of
the endpoint matching equation maps to the moving support on the midpoint
fiber. -/
theorem midpointEquationSet_subset_midpointExceptionSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0) :
    labeling.midpointEquationSet m hm ⊆
      labeling.midpointExceptionSet m hm := by
  classical
  letI := labeling.data.toAFiberCoordinates.P_fintype
  intro p hp
  rw [mem_midpointExceptionSet]
  exact
    AFiberReflectionEquivariance.midpoint_matching_eq_reflection_imp_midpoint_mate_mem_support
      (ref := labeling.toAFiberMidpointReflectionEquivariance m)
      (m := m) (hm := hm)
      (hsigma0 := by ring)
      (hsigmam := by ring)
      p
      ((labeling.mem_midpointEquationSet m hm p).1 hp)

/-- The geometric midpoint input follows from a center-neighbor fixed-branch
classification: if the midpoint reflection fixes only the middle A-branch
among center-neighbors, then any fixed common neighbor of the reflected endpoint
pair lies in the middle A-fiber. -/
theorem midpoint_fixedCommon_mem_middle_of_fixed_center_neighbor_eq_middle
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (hfixedBranch :
      ∀ {b : V},
        Γ.Adj labeling.data.toAFiberCoordinates.u b →
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) b = b →
        b = labeling.data.toAFiberCoordinates.a (0 + m))
    (p : labeling.data.toAFiberCoordinates.P) {w : V}
    (hwfix :
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) w = w)
    (hxw :
      Γ.Adj
        (((labeling.data.toAFiberCoordinates.coord 0 p :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a 0)}) : V)) w)
    (hyw :
      Γ.Adj
        (((labeling.data.toAFiberCoordinates.coord (0 + (m + m))
            (labeling.midpointReflectionCoordPerm m p) :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a (0 + (m + m)))}) : V)) w) :
    w ∈ labeling.data.toAFiberCoordinates.fiber (0 + m) := by
  let coords := labeling.data.toAFiberCoordinates
  let x : V :=
    ((coords.coord 0 p :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)
  let y : V :=
    ((coords.coord (0 + (m + m)) (labeling.midpointReflectionCoordPerm m p) :
      {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (m + m)))}) : V)
  have hxmem : x ∈ branchFiber Γ coords.u (coords.a 0) := by
    exact coords.coord_mem 0 p
  have hx_ne_u : x ≠ coords.u := (mem_branchFiber.mp hxmem).1
  have hx_not_adj_u : ¬ Γ.Adj coords.u x :=
    h.isMoore.not_adj_center_of_mem_branchFiber (coords.hub 0) hxmem
  have hw_ne_u : w ≠ coords.u := by
    intro hwu
    exact hx_not_adj_u (by simpa [x, coords, hwu] using hxw.symm)
  have hw_not_adj_u : ¬ Γ.Adj coords.u w := by
    intro huw
    have hx_branch_over_w :
        x ∈ branchFiber Γ coords.u w := by
      rw [mem_branchFiber]
      exact ⟨hx_ne_u, hxw.symm⟩
    rcases h.isMoore.existsUnique_branch_of_not_adj_center
        hx_ne_u.symm hx_not_adj_u with
      ⟨b, hb, huniq⟩
    have hw_eq_a0 : w = coords.a 0 :=
      (huniq w ⟨huw, hx_branch_over_w⟩).trans
        (huniq (coords.a 0) ⟨coords.hub 0, hxmem⟩).symm
    have hymem :
        y ∈ branchFiber Γ coords.u (coords.a (0 + (m + m))) := by
      simpa [y, coords] using
        coords.coord_mem (0 + (m + m)) (labeling.midpointReflectionCoordPerm m p)
    have hy_not_adj_a0 :
        ¬ Γ.Adj y (coords.a 0) :=
      h.isMoore.not_adj_other_branch_of_mem_branchFiber
        (coords.hub (0 + (m + m))) (coords.hub 0)
        (coords.a_ne (by
          intro hidx
          exact (add_self_ne_zero_zmod19 hm) (by simpa using hidx)))
        hymem
    exact hy_not_adj_a0 (by simpa [y, coords, hw_eq_a0] using hyw)
  rcases h.isMoore.existsUnique_branch_of_not_adj_center
      hw_ne_u.symm hw_not_adj_u with
    ⟨b, hb, huniq⟩
  have href_u :
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
          coords.u = coords.u :=
    (labeling.toAFiberMidpointReflectionEquivariance m).reflection_u
  have hb_ref_adj :
      Γ.Adj coords.u
        (h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) b) := by
    have hAdj :=
      (h.smul_adj (DihedralGroup.sr (labeling.midpointReflectionIndex m))
        coords.u b).mp hb.1
    simpa [href_u] using hAdj
  have hb_ref_mem :
      w ∈ branchFiber Γ coords.u
        (h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) b) := by
    have hmem :
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) w ∈
          branchFiber Γ coords.u
            (h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) b) :=
      (h.smul_mem_branchFiber_iff
        (DihedralGroup.sr (labeling.midpointReflectionIndex m))
        (u := coords.u) (b := b) (x := w) href_u).2 hb.2
    simpa [hwfix] using hmem
  have hb_fixed :
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) b = b :=
    huniq _ ⟨hb_ref_adj, hb_ref_mem⟩
  have hb_middle : b = coords.a (0 + m) :=
    hfixedBranch hb.1 (by simpa [coords] using hb_fixed)
  simpa [AFiberCoordinates.fiber, coords, hb_middle] using hb.2

/-- If the midpoint reflection has at most one fixed center-neighbor, then any
fixed center-neighbor is the middle A-branch. -/
theorem midpoint_fixed_center_neighbor_eq_middle_of_fixedCenterNeighbors_card_le_one
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19)
    (hfixedCenterNeighbors_le_one :
      ((Γ.neighborFinset labeling.data.toAFiberCoordinates.u).filter fun b =>
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) b = b).card ≤ 1)
    {b : V}
    (hb_adj : Γ.Adj labeling.data.toAFiberCoordinates.u b)
    (hb_fixed :
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) b = b) :
    b = labeling.data.toAFiberCoordinates.a (0 + m) := by
  classical
  let coords := labeling.data.toAFiberCoordinates
  have hb_mem :
      b ∈ (Γ.neighborFinset coords.u).filter fun c =>
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) c = c := by
    rw [Finset.mem_filter]
    exact ⟨by simpa [SimpleGraph.mem_neighborFinset] using hb_adj, hb_fixed⟩
  have hmid_fixed :
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
          (coords.a (0 + m)) =
        coords.a (0 + m) := by
    have hraw :=
      (labeling.toAFiberMidpointReflectionEquivariance m).reflection_a (0 + m)
    have hidx : (2 : ZMod 19) * m - m = m := by
      ring
    simpa [coords, hidx] using hraw
  have hmid_mem :
      coords.a (0 + m) ∈
        (Γ.neighborFinset coords.u).filter fun c =>
          h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) c = c := by
    rw [Finset.mem_filter]
    exact
      ⟨by
        simpa [SimpleGraph.mem_neighborFinset] using coords.hub (0 + m),
        hmid_fixed⟩
  exact
    (Finset.card_le_one_iff.mp hfixedCenterNeighbors_le_one)
      hb_mem hmid_mem

/-- The fixed-star leaf boundary supplies the fixed center-neighbor uniqueness
needed to identify the middle A-branch. -/
theorem midpoint_fixed_center_neighbor_eq_middle_of_fixedCenterLeaf
    (labeling : BranchOrbitABCReflectionLabeling h)
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h)
    (m : ZMod 19) {b : V}
    (hb_adj : Γ.Adj labeling.data.toAFiberCoordinates.u b)
    (hb_fixed :
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) b = b) :
    b = labeling.data.toAFiberCoordinates.a (0 + m) := by
  have hle :
      ((Γ.neighborFinset labeling.data.toAFiberCoordinates.u).filter fun b =>
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) b = b).card ≤
        1 := by
    rw [BranchOrbitABCFromCenter.toAFiberCoordinates_u,
      labeling.data.u_eq_rotationFixedCenter]
    exact fixedCenterLeaf.fixed_center_neighbors_card_le_one
      (labeling.midpointReflectionIndex m)
  exact
    labeling.midpoint_fixed_center_neighbor_eq_middle_of_fixedCenterNeighbors_card_le_one
      m hle hb_adj hb_fixed

/-- Reverse midpoint criterion after isolating the remaining geometric input:
any fixed common neighbor of the reflected endpoint pair must lie in the
middle A-fiber. -/
theorem midpointExceptionSet_subset_midpointEquationSet_of_fixedCommon_mem_middle
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (hfixedCommon_mem_middle :
      ∀ p : labeling.data.toAFiberCoordinates.P, ∀ {w : V},
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) w = w →
        Γ.Adj
          (((labeling.data.toAFiberCoordinates.coord 0 p :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a 0)}) : V)) w →
        Γ.Adj
          (((labeling.data.toAFiberCoordinates.coord (0 + (m + m))
              (labeling.midpointReflectionCoordPerm m p) :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a (0 + (m + m)))}) : V)) w →
        w ∈ labeling.data.toAFiberCoordinates.fiber (0 + m)) :
    labeling.midpointExceptionSet m hm ⊆
      labeling.midpointEquationSet m hm := by
  classical
  letI := labeling.data.toAFiberCoordinates.P_fintype
  intro p hp
  rw [mem_midpointEquationSet]
  apply
    AFiberReflectionEquivariance.midpoint_mate_mem_support_imp_matching_eq_reflection_of_fixedCommon_mem_middle
      (ref := labeling.toAFiberMidpointReflectionEquivariance m)
      (m := m) (hm := hm)
      (hsigma0 := by ring)
      (hsigmam := by ring)
      (p := p)
  · intro p w hwfix hxw hyw
    exact hfixedCommon_mem_middle p hwfix hxw
      (by simpa [midpointReflectionCoordPerm] using hyw)
  · simpa [midpointMiddleSupport] using
      ((labeling.mem_midpointExceptionSet m hm p).1 hp)

/-- The exception set is the preimage of the middle support under a matching
equivalence, so it has the same cardinality as that support. -/
theorem midpointExceptionSet_card_eq_midpointMiddleSupport_card
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0) :
    (labeling.midpointExceptionSet m hm).card =
      (labeling.midpointMiddleSupport m).card := by
  classical
  letI := labeling.data.toAFiberCoordinates.P_fintype
  let e : labeling.data.toAFiberCoordinates.P ≃
      labeling.data.toAFiberCoordinates.P :=
    AFiberCoordinates.matchingEquiv h.isMoore
      labeling.data.toAFiberCoordinates 0 (0 + m)
      (index_ne_add_of_ne_zero hm)
  let equiv :
      {p : labeling.data.toAFiberCoordinates.P //
        p ∈ labeling.midpointExceptionSet m hm} ≃
      {q : labeling.data.toAFiberCoordinates.P //
        q ∈ labeling.midpointMiddleSupport m} := {
    toFun := fun p => ⟨e p, by
      simpa [midpointExceptionSet, e] using p.property⟩
    invFun := fun q => ⟨e.symm q, by
      have hq : e (e.symm q) ∈ labeling.midpointMiddleSupport m := by
        simpa only [e.apply_symm_apply] using q.property
      simpa [midpointExceptionSet, e] using hq⟩
    left_inv := by
      intro p
      ext
      exact e.symm_apply_apply p.1
    right_inv := by
      intro q
      ext
      exact e.apply_symm_apply q.1 }
  calc
    (labeling.midpointExceptionSet m hm).card =
        Fintype.card {p : labeling.data.toAFiberCoordinates.P //
          p ∈ labeling.midpointExceptionSet m hm} := by
          rw [Fintype.card_coe]
    _ = Fintype.card {q : labeling.data.toAFiberCoordinates.P //
          q ∈ labeling.midpointMiddleSupport m} :=
          Fintype.card_congr equiv
    _ = (labeling.midpointMiddleSupport m).card := by
          rw [Fintype.card_coe]

/-- Boundary form of the midpoint reflection criterion.  The hard geometric
content is the equivalence between the midpoint matching equation and the
exception set; the surrounding finite-set and transport API is proved in this
file. -/
structure MidpointReflectionCriterionBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) where
  midpoint_equation_iff_exception :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.midpointEquationSet m hm ↔
          p ∈ labeling.midpointExceptionSet m hm

/-- Build the full midpoint-reflection criterion once the remaining geometric
fixed-common-neighbor input has been supplied. -/
noncomputable def midpointReflectionCriterionBoundary_of_fixedCommon_mem_middle
    (labeling : BranchOrbitABCReflectionLabeling h)
    (hfixedCommon_mem_middle :
      ∀ m : ZMod 19, ∀ _hm : m ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P, ∀ {w : V},
          h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) w = w →
          Γ.Adj
            (((labeling.data.toAFiberCoordinates.coord 0 p :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a 0)}) : V)) w →
          Γ.Adj
            (((labeling.data.toAFiberCoordinates.coord (0 + (m + m))
                (labeling.midpointReflectionCoordPerm m p) :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a (0 + (m + m)))}) : V)) w →
          w ∈ labeling.data.toAFiberCoordinates.fiber (0 + m)) :
    MidpointReflectionCriterionBoundary labeling where
  midpoint_equation_iff_exception := by
    intro m hm p
    constructor
    · intro hp
      exact labeling.midpointEquationSet_subset_midpointExceptionSet m hm hp
    · intro hp
      exact
        (labeling.midpointExceptionSet_subset_midpointEquationSet_of_fixedCommon_mem_middle
          m hm (hfixedCommon_mem_middle m hm)) hp

/-- Build the full midpoint-reflection criterion from the smaller
center-neighbor statement that the midpoint reflection fixes only the middle
A-branch among center-neighbors. -/
noncomputable def midpointReflectionCriterionBoundary_of_fixed_center_neighbor_eq_middle
    (labeling : BranchOrbitABCReflectionLabeling h)
    (hfixedBranch :
      ∀ m : ZMod 19, ∀ _hm : m ≠ 0, ∀ {b : V},
        Γ.Adj labeling.data.toAFiberCoordinates.u b →
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) b = b →
        b = labeling.data.toAFiberCoordinates.a (0 + m)) :
    MidpointReflectionCriterionBoundary labeling :=
  labeling.midpointReflectionCriterionBoundary_of_fixedCommon_mem_middle
    (fun m hm p {_w} hwfix hxw hyw =>
      labeling.midpoint_fixedCommon_mem_middle_of_fixed_center_neighbor_eq_middle
        m hm (hfixedBranch m hm) p hwfix hxw hyw)

/-- Build the full midpoint-reflection criterion from the existing fixed-star
leaf boundary for reflections. -/
noncomputable def midpointReflectionCriterionBoundary_of_fixedCenterLeaf
    (labeling : BranchOrbitABCReflectionLabeling h)
    (fixedCenterLeaf : ReflectionFixedCenterLeafBoundary h) :
    MidpointReflectionCriterionBoundary labeling :=
  labeling.midpointReflectionCriterionBoundary_of_fixed_center_neighbor_eq_middle
    (fun m _hm =>
      labeling.midpoint_fixed_center_neighbor_eq_middle_of_fixedCenterLeaf
        fixedCenterLeaf m)

namespace MidpointReflectionCriterionBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

theorem midpointEquationSet_card_eq_midpointMiddleSupport_card
    (boundary : MidpointReflectionCriterionBoundary labeling)
    (m : ZMod 19) (hm : m ≠ 0) :
    (labeling.midpointEquationSet m hm).card =
      (labeling.midpointMiddleSupport m).card := by
  classical
  have hset :
      labeling.midpointEquationSet m hm =
        labeling.midpointExceptionSet m hm := by
    ext p
    exact boundary.midpoint_equation_iff_exception m hm p
  rw [hset]
  exact labeling.midpointExceptionSet_card_eq_midpointMiddleSupport_card m hm

end MidpointReflectionCriterionBoundary

end BranchOrbitABCReflectionLabeling

/-! ## Reference exception-set bridge -/

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
