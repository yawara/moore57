import Moore57.BranchOrbitABCFromCenter
import Moore57.BranchOrbitABCData
import Moore57.AFiberOrbitBaseSelection

/-!
# Branch-orbit data from fixed-center neighbor orbits

This file closes the packaging gap between the three rotation orbits on the
neighbors of the rotation-fixed center and the downstream `BranchOrbitABCData`.
The three center-neighbor orbits provide the A/B/C branch representatives.  The
remaining `Fin 56` moved orbit-base input is generated canonically from the
A-branch fiber coordinates already constructed by `BranchOrbitABCFromCenter`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCFromCenter

variable {h : D19ActsOnMoore57 V Γ}

/-- The `Fin 56` moved orbit-base selection generated from the A-branch
coordinates associated to fixed-center A/B/C data. -/
noncomputable def toOrbitBaseSelectionInputFromCoordinates
    (data : BranchOrbitABCFromCenter h) :
    OrbitBaseSelectionInput h :=
  data.toAFiberCoordinates.toOrbitBaseSelectionInputOfMoore
    data.toAFiberRotationEquivariance

/-- Promote fixed-center A/B/C branch data to the downstream
`BranchOrbitABCData`.

The branch representatives come directly from the three center-neighbor
rotation orbits.  The `Fin 56` orbit-base fields are supplied by the canonical
selection obtained from the A-branch coordinate system. -/
noncomputable def toBranchOrbitABCData
    (data : BranchOrbitABCFromCenter h) :
    BranchOrbitABCData h :=
  let input := data.toOrbitBaseSelectionInputFromCoordinates
  { u := data.u
    a0 := data.a0
    b0 := data.b0
    c0 := data.c0
    u_fixed := data.u_fixed
    a0_adj := data.a0_adj
    b0_adj := data.b0_adj
    c0_adj := data.c0_adj
    a0_move_step := 1
    a0_move_step_ne_zero := by decide
    a0_moved := data.a0_moved
    orbitBase := input.base
    orbitBase_moved := input.base_moved
    orbitBase_pairwise_disjoint := input.pairwise_disjoint }

@[simp] theorem toBranchOrbitABCData_u
    (data : BranchOrbitABCFromCenter h) :
    data.toBranchOrbitABCData.u = data.u :=
  rfl

@[simp] theorem toBranchOrbitABCData_a0
    (data : BranchOrbitABCFromCenter h) :
    data.toBranchOrbitABCData.a0 = data.a0 :=
  rfl

@[simp] theorem toBranchOrbitABCData_b0
    (data : BranchOrbitABCFromCenter h) :
    data.toBranchOrbitABCData.b0 = data.b0 :=
  rfl

@[simp] theorem toBranchOrbitABCData_c0
    (data : BranchOrbitABCFromCenter h) :
    data.toBranchOrbitABCData.c0 = data.c0 :=
  rfl

@[simp] theorem toBranchOrbitABCData_a0_move_step
    (data : BranchOrbitABCFromCenter h) :
    data.toBranchOrbitABCData.a0_move_step = 1 :=
  rfl

@[simp] theorem toBranchOrbitABCData_toAFiberCoordinates
    (data : BranchOrbitABCFromCenter h) :
    data.toBranchOrbitABCData.toAFiberCoordinates =
      data.toAFiberCoordinates := by
  rfl

/-- The orbit-base input stored in the promoted `BranchOrbitABCData` is the
one generated from the A-branch coordinates. -/
@[simp] theorem toBranchOrbitABCData_toOrbitBaseSelectionInput
    (data : BranchOrbitABCFromCenter h) :
    data.toBranchOrbitABCData.toOrbitBaseSelectionInput =
      data.toOrbitBaseSelectionInputFromCoordinates := by
  rfl

end BranchOrbitABCFromCenter

namespace BranchOrbitABCData

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructor from already-packaged fixed-center A/B/C data. -/
noncomputable def ofFromCenter
    (data : BranchOrbitABCFromCenter h) :
    BranchOrbitABCData h :=
  data.toBranchOrbitABCData

/-- Constructor from an explicit `Fin 3` family satisfying the fixed-center
neighbor-orbit decomposition conclusions. -/
noncomputable def ofCenterNeighborOrbitBase
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_card :
      ∀ q : Fin 3, (h.rotationOrbitFinset (base q)).card = 19)
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base) :
    BranchOrbitABCData h :=
  (BranchOrbitABCFromCenter.ofNeighborOrbitBase base base_adj base_card
    base_pairwise_disjoint base_cover).toBranchOrbitABCData

/-- Fully automatic constructor: choose the three rotation orbits on the
neighbors of the rotation-fixed center, then generate the downstream `Fin 56`
orbit-base input from the A-branch coordinates. -/
noncomputable def ofRotationFixedCenterNeighborOrbits
    (h : D19ActsOnMoore57 V Γ) :
    BranchOrbitABCData h :=
  (BranchOrbitABCFromCenter.ofExistsThreeRotationOrbitFinsetNeighbors h).toBranchOrbitABCData

/-- Existence form of `ofRotationFixedCenterNeighborOrbits`, recording the
center and move-step normalization supplied by this bridge. -/
theorem exists_of_rotationFixedCenter_neighbor_orbits
    (h : D19ActsOnMoore57 V Γ) :
    ∃ data : BranchOrbitABCData h,
      data.u = h.rotationFixedCenter ∧ data.a0_move_step = 1 := by
  let centerData := BranchOrbitABCFromCenter.ofExistsThreeRotationOrbitFinsetNeighbors h
  exact ⟨centerData.toBranchOrbitABCData, centerData.u_eq_rotationFixedCenter, rfl⟩

end BranchOrbitABCData

end

end Moore57
