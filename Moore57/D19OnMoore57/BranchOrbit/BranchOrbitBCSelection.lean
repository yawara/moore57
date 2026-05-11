import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCDataFromCenter
import Moore57.D19OnMoore57.AFiber.AFiberOrbitBaseSelectionCover
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitBCSelectionCover

/-!
# B-side selected orbit bases from fixed-center branch data

This file records the first half of the natural-language Section 7 selected
orbit construction.  The selected `Fin 56` bases are chosen from `L_{b0}`;
their rotation-orbit family is exactly the union of the `B`-side branch
fibers.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCFromCenter

variable {h : D19ActsOnMoore57 V Γ}

/-- Membership in the `B`-side fibers generated from center-neighbor data,
expanded to the corresponding `B`-branch rotation orbit. -/
theorem mem_toBFiberCoordinates_allFibers_iff
    (data : BranchOrbitABCFromCenter h) (y : V) :
    y ∈ data.toBFiberCoordinates.allFibers ↔
      ∃ i : ZMod 19,
        y ∈ branchFiber Γ data.u (h.rotation i data.b0) := by
  simpa [BranchOrbitABCFromCenter.toBFiberCoordinates] using
    data.toBFiberCoordinates.mem_allFibers_iff y

/-- The selected orbit-base input generated from `L_{b0}` covers exactly the
`B`-side branch fibers. -/
theorem toOrbitBaseSelectionInputFromBFibers_orbitFamilyUnion_eq_bFibers
    (data : BranchOrbitABCFromCenter h) :
    data.toOrbitBaseSelectionInputFromBFibers.orbitFamilyUnion =
      data.toBFiberCoordinates.allFibers := by
  exact
    data.toBFiberCoordinates
      |>.toOrbitBaseSelectionInputOfMoore_orbitFamilyUnion_eq_allFibers
        data.toBFiberRotationEquivariance

/-- The selected orbit-base input stored in `BranchOrbitABCData` covers
exactly the `B`-side branch fibers. -/
theorem toBranchOrbitABCData_orbitFamilyUnion_eq_bFibers
    (data : BranchOrbitABCFromCenter h) :
    data.toBranchOrbitABCData.toOrbitBaseSelectionInput.orbitFamilyUnion =
      data.toBFiberCoordinates.allFibers := by
  simpa using
    data.toOrbitBaseSelectionInputFromBFibers_orbitFamilyUnion_eq_bFibers

/-- Membership form of the selected `B`-side orbit-family coverage. -/
theorem mem_toBranchOrbitABCData_orbitFamilyUnion_iff_bFibers
    (data : BranchOrbitABCFromCenter h) (y : V) :
    y ∈ data.toBranchOrbitABCData.toOrbitBaseSelectionInput.orbitFamilyUnion ↔
      ∃ i : ZMod 19,
        y ∈ branchFiber Γ data.u (h.rotation i data.b0) := by
  rw [data.toBranchOrbitABCData_orbitFamilyUnion_eq_bFibers]
  exact data.mem_toBFiberCoordinates_allFibers_iff y

/-- The canonical `Fin 56` enumeration of the B-coordinate type, transported
through the coordinate chart at `0`, as an enumeration of `L_{b0}` itself. -/
noncomputable def toBFiberCoordinatesBaseFiberEquiv
    (data : BranchOrbitABCFromCenter h) :
    Fin 56 ≃ {x : V // x ∈ branchFiber Γ data.u data.b0} :=
  (data.toBFiberCoordinates.fin56EquivOfMoore h.isMoore).trans
    ((data.toBFiberCoordinates.coord 0).trans
      (Equiv.subtypeEquivRight (fun x => by
        simp [BranchOrbitABCFromCenter.toBFiberCoordinates])))

/-- The canonical B-fiber orbit-base input is definitionally the direct
`L_{b0}` base enumeration used in the Section 7 cover lemmas. -/
@[simp] theorem toOrbitBaseSelectionInputFromBFibers_base_eq_b0FiberBase
    (data : BranchOrbitABCFromCenter h) :
    data.toOrbitBaseSelectionInputFromBFibers.base =
      data.b0FiberBase
        data.toBFiberCoordinatesBaseFiberEquiv :=
  rfl

/-- If a reflection sends `b0` to `c0`, the canonical selected B-fiber input
and its reflected copy cover exactly the B/C leaves. -/
theorem reflectionCopyUnion_toOrbitBaseSelectionInputFromBFibers_eq_bSideLeaf_union_cSideLeaf
    (data : BranchOrbitABCFromCenter h) {k : ZMod 19}
    (href : h.smul (DihedralGroup.sr k) data.b0 = data.c0) :
    reflectionCopyUnion h data.toOrbitBaseSelectionInputFromBFibers.base k =
      data.bSideLeaf ∪ data.cSideLeaf := by
  simpa using
    data.reflectionCopyUnion_b0FiberBase_eq_bSideLeaf_union_cSideLeaf
      data.toBFiberCoordinatesBaseFiberEquiv href

end BranchOrbitABCFromCenter

end

end Moore57
