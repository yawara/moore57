import Moore57.BranchOrbitABCDataFromCenter
import Moore57.AFiberOrbitBaseSelectionCover

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

end BranchOrbitABCFromCenter

end

end Moore57
