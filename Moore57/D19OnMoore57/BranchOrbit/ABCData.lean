import Moore57.D19OnMoore57.AFiber.CoordinateOrbit
import Moore57.D19OnMoore57.Orbit.BaseSelectionInputs

/-!
# Branch-orbit A/B/C boundary data

This file records a minimal boundary record for the branch-orbit data around
the rotation-fixed center.  It only exposes the fields needed to connect to the
existing A-fiber coordinate constructor and orbit-base input API.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Minimal branch-orbit data around the rotation-fixed center.

The A-side fields construct rotation-orbit A-fiber coordinates.  The selected
orbit-base fields are exactly the downstream `OrbitBaseSelectionInput` data for
the 56 moved rotation orbits.
-/
structure BranchOrbitABCData (h : D19ActsOnMoore57 V Γ) where
  /-- The center fixed by the rotation subgroup. -/
  u : V
  /-- The initial A-side branch. -/
  a0 : V
  /-- The initial B-side branch, kept as boundary data for later constructions. -/
  b0 : V
  /-- The initial C-side branch, kept as boundary data for later constructions. -/
  c0 : V
  /-- The center is fixed by every rotation. -/
  u_fixed : ∀ d : ZMod 19, h.rotation d u = u
  /-- The initial A-side branch is adjacent to the center. -/
  a0_adj : Γ.Adj u a0
  /-- The initial B-side branch is adjacent to the center. -/
  b0_adj : Γ.Adj u b0
  /-- The initial C-side branch is adjacent to the center. -/
  c0_adj : Γ.Adj u c0
  /-- A nonzero rotation step moving the initial A-side branch. -/
  a0_move_step : ZMod 19
  /-- The chosen A-side moving step is nonzero. -/
  a0_move_step_ne_zero : a0_move_step ≠ 0
  /-- The chosen nonzero rotation step moves the initial A-side branch. -/
  a0_moved : h.rotation a0_move_step a0 ≠ a0
  /-- One representative for each selected moved rotation orbit. -/
  orbitBase : Fin 56 → V
  /-- Every selected orbit representative is moved by rotation `1`. -/
  orbitBase_moved : ∀ q : Fin 56, h.rotation 1 (orbitBase q) ≠ orbitBase q
  /-- The selected rotation orbits are pairwise disjoint. -/
  orbitBase_pairwise_disjoint :
    ∀ q r : Fin 56, q ≠ r →
      Disjoint (h.rotationOrbitFinset (orbitBase q))
        (h.rotationOrbitFinset (orbitBase r))

namespace BranchOrbitABCData

variable {h : D19ActsOnMoore57 V Γ}

/-- The A-side branch indexed by the rotation orbit of `a0`. -/
def aBranch (data : BranchOrbitABCData h) : ZMod 19 → V :=
  fun i => h.rotation i data.a0

/-- The B-side branch indexed by the rotation orbit of `b0`. -/
def bBranch (data : BranchOrbitABCData h) : ZMod 19 → V :=
  fun i => h.rotation i data.b0

/-- The C-side branch indexed by the rotation orbit of `c0`. -/
def cBranch (data : BranchOrbitABCData h) : ZMod 19 → V :=
  fun i => h.rotation i data.c0

/-- Construct the downstream A-fiber coordinate system from the A-side branch
orbit. -/
noncomputable def toAFiberCoordinates
    (data : BranchOrbitABCData h) :
    AFiberCoordinates.{u, u} Γ :=
  AFiberCoordinates.ofRotationOrbitOfMoved
    h data.u data.a0 data.u_fixed data.a0_adj
    (d := data.a0_move_step)
    data.a0_move_step_ne_zero data.a0_moved

/-- Package the selected moved rotation orbits as the existing downstream
`OrbitBaseSelectionInput`. -/
def toOrbitBaseSelectionInput
    (data : BranchOrbitABCData h) :
    OrbitBaseSelectionInput h where
  base := data.orbitBase
  base_moved := data.orbitBase_moved
  pairwise_disjoint := data.orbitBase_pairwise_disjoint

@[simp] theorem toOrbitBaseSelectionInput_base
    (data : BranchOrbitABCData h) :
    data.toOrbitBaseSelectionInput.base = data.orbitBase :=
  rfl

@[simp] theorem toAFiberCoordinates_u
    (data : BranchOrbitABCData h) :
    data.toAFiberCoordinates.u = data.u :=
  rfl

@[simp] theorem toAFiberCoordinates_a
    (data : BranchOrbitABCData h) :
    data.toAFiberCoordinates.a = data.aBranch :=
  rfl

end BranchOrbitABCData

end

end Moore57
