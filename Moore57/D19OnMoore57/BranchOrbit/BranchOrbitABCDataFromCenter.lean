import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCFromCenter
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCData
import Moore57.D19OnMoore57.AFiber.AFiberOrbitBaseSelection

/-!
# Branch-orbit data from fixed-center neighbor orbits

This file closes the packaging gap between the three rotation orbits on the
neighbors of the rotation-fixed center and the downstream `BranchOrbitABCData`.
The three center-neighbor orbits provide the A/B/C branch representatives.  The
remaining `Fin 56` moved orbit-base input is generated canonically from the
`B`-branch fiber coordinates, as in the natural-language proof: choose the
56 points of `L_{b0}`, rotate them through the `B` branch orbit, and use the
reflection copy for the `C` side downstream.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCFromCenter

variable {h : D19ActsOnMoore57 V Γ}

/-- The `B`-side fiber coordinates generated from the `b0` branch orbit. -/
noncomputable def toBFiberCoordinates
    (data : BranchOrbitABCFromCenter h) :
    AFiberCoordinates.{u, u} Γ :=
  AFiberCoordinates.ofRotationOrbitOfMoved
    h data.u data.b0 data.u_fixed data.b0_adj
    (d := 1) (by decide) data.b0_moved

/-- The `B`-side fiber coordinates are rotation equivariant. -/
theorem toBFiberRotationEquivariance
    (data : BranchOrbitABCFromCenter h) :
    AFiberRotationEquivariance h data.toBFiberCoordinates :=
  AFiberCoordinates.ofRotationOrbitOfMoved_rotationEquivariance
    h data.u data.b0 data.u_fixed data.b0_adj (by decide) data.b0_moved

/-- The `C`-side fiber coordinates generated from the `c0` branch orbit. -/
noncomputable def toCFiberCoordinates
    (data : BranchOrbitABCFromCenter h) :
    AFiberCoordinates.{u, u} Γ :=
  AFiberCoordinates.ofRotationOrbitOfMoved
    h data.u data.c0 data.u_fixed data.c0_adj
    (d := 1) (by decide) data.c0_moved

/-- The `C`-side fiber coordinates are rotation equivariant. -/
theorem toCFiberRotationEquivariance
    (data : BranchOrbitABCFromCenter h) :
    AFiberRotationEquivariance h data.toCFiberCoordinates :=
  AFiberCoordinates.ofRotationOrbitOfMoved_rotationEquivariance
    h data.u data.c0 data.u_fixed data.c0_adj (by decide) data.c0_moved

/-- The `Fin 56` moved orbit-base selection generated from the `B`-branch
fiber coordinates associated to fixed-center A/B/C data. -/
noncomputable def toOrbitBaseSelectionInputFromBFibers
    (data : BranchOrbitABCFromCenter h) :
    OrbitBaseSelectionInput h :=
  data.toBFiberCoordinates.toOrbitBaseSelectionInputOfMoore
    data.toBFiberRotationEquivariance

/-- Promote fixed-center A/B/C branch data to the downstream
`BranchOrbitABCData`.

The branch representatives come directly from the three center-neighbor
rotation orbits.  The `Fin 56` orbit-base fields are supplied by the
natural-language selected base: the canonical enumeration of `L_{b0}` and its
rotation orbit family. -/
noncomputable def toBranchOrbitABCData
    (data : BranchOrbitABCFromCenter h) :
    BranchOrbitABCData h :=
  let input := data.toOrbitBaseSelectionInputFromBFibers
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
one generated from the `B`-branch fiber coordinates. -/
@[simp] theorem toBranchOrbitABCData_toOrbitBaseSelectionInput
    (data : BranchOrbitABCFromCenter h) :
    data.toBranchOrbitABCData.toOrbitBaseSelectionInput =
      data.toOrbitBaseSelectionInputFromBFibers := by
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
