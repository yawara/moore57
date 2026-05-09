import Moore57.BranchOrbitABCReflectionLabeling
import Moore57.AFiberMatchingExceptionSetBoundary
import Moore57.AFiberMidpointReflectionCriterion

/-!
# Midpoint reflections for reflection-compatible A/B/C labelings

This file packages the reflection used in the natural-language midpoint
argument.  Once a reflection has been shifted to fix the A representative
`a0`, the reflection with parameter `k - 2 * m` sends the A-branch index `i`
to `2 * m - i`; in particular it swaps the reference branch `0` with `2 * m`
and fixes the middle branch `m`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

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

end

end Moore57
