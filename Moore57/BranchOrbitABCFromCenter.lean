import Moore57.RotationFixedCenterNeighborOrbits
import Moore57.AFiberCoordinateOrbit

/-!
# Branch A/B/C data from the fixed-center neighbor orbits

This file is a thin constructor bridge from the three rotation orbits on the
neighbors of the rotation-fixed center to A/B/C branch boundary data.  It
deliberately does not include the downstream `Fin 56` residual orbit-base
selection.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u}

/-- The three branch representatives as a `Fin 3`-indexed family. -/
def branchABCBase (a0 b0 c0 : V) : Fin 3 → V :=
  fun q => if q = 0 then a0 else if q = 1 then b0 else c0

@[simp] theorem branchABCBase_zero (a0 b0 c0 : V) :
    branchABCBase a0 b0 c0 0 = a0 := by
  simp [branchABCBase]

@[simp] theorem branchABCBase_one (a0 b0 c0 : V) :
    branchABCBase a0 b0 c0 1 = b0 := by
  simp [branchABCBase]

@[simp] theorem branchABCBase_two (a0 b0 c0 : V) :
    branchABCBase a0 b0 c0 2 = c0 := by
  simp [branchABCBase]

variable [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Boundary data for the three center-neighbor rotation orbits.

The record only stores the center, three branch representatives, their
center-adjacency and movedness, and the pairwise/covering facts for the three
neighbor orbits.  The `Fin 56` residual orbit-base data is intentionally absent.
-/
structure BranchOrbitABCFromCenter (h : D19ActsOnMoore57 V Γ) where
  /-- The center fixed by the rotation subgroup. -/
  u : V
  /-- The A-side center-neighbor representative. -/
  a0 : V
  /-- The B-side center-neighbor representative. -/
  b0 : V
  /-- The C-side center-neighbor representative. -/
  c0 : V
  /-- The stored center is the canonical rotation-fixed center. -/
  u_eq_rotationFixedCenter : u = h.rotationFixedCenter
  /-- The center is fixed by every rotation. -/
  u_fixed : ∀ d : ZMod 19, h.rotation d u = u
  /-- The A representative is adjacent to the center. -/
  a0_adj : Γ.Adj u a0
  /-- The B representative is adjacent to the center. -/
  b0_adj : Γ.Adj u b0
  /-- The C representative is adjacent to the center. -/
  c0_adj : Γ.Adj u c0
  /-- Rotation by `1` moves the A representative. -/
  a0_moved : h.rotation 1 a0 ≠ a0
  /-- Rotation by `1` moves the B representative. -/
  b0_moved : h.rotation 1 b0 ≠ b0
  /-- Rotation by `1` moves the C representative. -/
  c0_moved : h.rotation 1 c0 ≠ c0
  /-- Each of the three selected neighbor rotation orbits has size `19`. -/
  orbit_card :
    ∀ q : Fin 3,
      (h.rotationOrbitFinset (branchABCBase a0 b0 c0 q)).card = 19
  /-- The three selected neighbor rotation orbits are pairwise disjoint. -/
  pairwise_disjoint :
    ∀ q r : Fin 3, q ≠ r →
      Disjoint (h.rotationOrbitFinset (branchABCBase a0 b0 c0 q))
        (h.rotationOrbitFinset (branchABCBase a0 b0 c0 r))
  /-- The three selected rotation orbits cover the center-neighbor finset. -/
  cover_neighbors :
    Γ.neighborFinset u = h.orbitFamilyUnion (branchABCBase a0 b0 c0)

namespace BranchOrbitABCFromCenter

variable {h : D19ActsOnMoore57 V Γ}

/-- The branch representatives as a `Fin 3`-indexed family. -/
def base (data : BranchOrbitABCFromCenter h) : Fin 3 → V :=
  branchABCBase data.a0 data.b0 data.c0

@[simp] theorem base_zero (data : BranchOrbitABCFromCenter h) :
    data.base 0 = data.a0 :=
  rfl

@[simp] theorem base_one (data : BranchOrbitABCFromCenter h) :
    data.base 1 = data.b0 :=
  rfl

@[simp] theorem base_two (data : BranchOrbitABCFromCenter h) :
    data.base 2 = data.c0 :=
  rfl

/-- Constructor from an explicit `Fin 3` family satisfying the fixed-center
neighbor-orbit theorem's conclusions. -/
def ofNeighborOrbitBase
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
    BranchOrbitABCFromCenter h := by
  classical
  let abcBase : Fin 3 → V := branchABCBase (base 0) (base 1) (base 2)
  have habcBase_eq : abcBase = base := by
    funext q
    fin_cases q <;> simp [abcBase]
  refine
    { u := h.rotationFixedCenter
      a0 := base 0
      b0 := base 1
      c0 := base 2
      u_eq_rotationFixedCenter := rfl
      u_fixed := h.rotationFixedCenter_fixed_rotation
      a0_adj := base_adj 0
      b0_adj := base_adj 1
      c0_adj := base_adj 2
      a0_moved := h.rotationFixedCenter_neighbor_moved (base_adj 0)
      b0_moved := h.rotationFixedCenter_neighbor_moved (base_adj 1)
      c0_moved := h.rotationFixedCenter_neighbor_moved (base_adj 2)
      orbit_card := ?_
      pairwise_disjoint := ?_
      cover_neighbors := ?_ }
  · intro q
    change (h.rotationOrbitFinset (abcBase q)).card = 19
    rw [habcBase_eq]
    exact base_card q
  · intro q r hqr
    change Disjoint (h.rotationOrbitFinset (abcBase q))
      (h.rotationOrbitFinset (abcBase r))
    rw [habcBase_eq]
    exact base_pairwise_disjoint q r hqr
  · change Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion abcBase
    rw [habcBase_eq]
    exact base_cover

/-- Noncomputable constructor choosing the three center-neighbor rotation
orbits supplied by
`exists_three_rotationOrbitFinset_neighbors_rotationFixedCenter`. -/
def ofExistsThreeRotationOrbitFinsetNeighbors
    (h : D19ActsOnMoore57 V Γ) :
    BranchOrbitABCFromCenter h := by
  classical
  let base :=
    Classical.choose h.exists_three_rotationOrbitFinset_neighbors_rotationFixedCenter
  have hbase :=
    Classical.choose_spec h.exists_three_rotationOrbitFinset_neighbors_rotationFixedCenter
  exact ofNeighborOrbitBase base hbase.1 hbase.2.1 hbase.2.2.1 hbase.2.2.2

/-- Existence form of `ofExistsThreeRotationOrbitFinsetNeighbors`. -/
theorem exists_from_rotationFixedCenter_neighbor_orbits
    (h : D19ActsOnMoore57 V Γ) :
    ∃ data : BranchOrbitABCFromCenter h,
      data.u = h.rotationFixedCenter ∧
        Γ.neighborFinset data.u = h.orbitFamilyUnion data.base := by
  let data := ofExistsThreeRotationOrbitFinsetNeighbors h
  refine ⟨data, data.u_eq_rotationFixedCenter, ?_⟩
  exact data.cover_neighbors

/-- Convert the A branch orbit to the existing A-fiber coordinate constructor.
-/
def toAFiberCoordinates
    (data : BranchOrbitABCFromCenter h) :
    AFiberCoordinates.{u, u} Γ :=
  AFiberCoordinates.ofRotationOrbitOfMoved
    h data.u data.a0 data.u_fixed data.a0_adj
    (d := 1) (by decide) data.a0_moved

@[simp] theorem toAFiberCoordinates_u
    (data : BranchOrbitABCFromCenter h) :
    data.toAFiberCoordinates.u = data.u :=
  rfl

@[simp] theorem toAFiberCoordinates_a
    (data : BranchOrbitABCFromCenter h) :
    data.toAFiberCoordinates.a = fun i : ZMod 19 => h.rotation i data.a0 :=
  rfl

/-- The A-fiber coordinates generated from the A branch are rotation
equivariant. -/
theorem toAFiberRotationEquivariance
    (data : BranchOrbitABCFromCenter h) :
    AFiberRotationEquivariance h data.toAFiberCoordinates :=
  AFiberCoordinates.ofRotationOrbitOfMoved_rotationEquivariance
    h data.u data.a0 data.u_fixed data.a0_adj (by decide) data.a0_moved

end BranchOrbitABCFromCenter

end

end Moore57
