import Moore57.D19OnMoore57.BranchOrbit.ABCFromCenter
import Moore57.D19OnMoore57.AFiber.OrbitBaseSelectionMoved
import Moore57.D19OnMoore57.AFiber.OrbitBaseSelectionCover
import Moore57.D19OnMoore57.BranchOrbit.ABCReflectionLabeling

/-!
# B-side orbit base selection (variant of `toAFiberCoordinates` using `b0`)

The default `BranchOrbitABCFromCenter.toAFiberCoordinates` uses `data.a0` as
the base A-branch.  In a reflection-compatible labeling, the reflection
`sr k` swaps `data.b0` with `data.c0`, hence:

* the `A`-orbit (containing `a0`) is **fixed** as a set by every reflection;
* the `B`-orbit and `C`-orbit are **swapped** as sets.

The avoidance condition required by the compact adjacent-moved witness
(`sr k · base r ∉ orbitFamilyUnion`) **fails** for the A-side orbit base,
because reflection sends `branchFiber u (a 0)` back into `allFibers` (just to
a different `a i`).

The avoidance **holds** if we instead use `data.b0` (or `c0`) as the base:
`sr k · branchFiber u (b 0) = branchFiber u (c 0)`, which is a C-fiber,
disjoint from the B-fiber union.

This file packages the B-base variant.
-/

namespace Moore57

namespace BranchOrbitABCFromCenter

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {h : D19ActsOnMoore57 V Γ}

/-- A-fiber coordinates built from the B-side representative `b0`. -/
noncomputable def toAFiberCoordinatesB
    (data : BranchOrbitABCFromCenter h) :
    AFiberCoordinates.{u_1, u_1} Γ :=
  AFiberCoordinates.ofRotationOrbitOfMoved
    h data.u data.b0 data.u_fixed data.b0_adj
    (d := 1) (by decide) data.b0_moved

@[simp] theorem toAFiberCoordinatesB_u
    (data : BranchOrbitABCFromCenter h) :
    data.toAFiberCoordinatesB.u = data.u :=
  rfl

@[simp] theorem toAFiberCoordinatesB_a
    (data : BranchOrbitABCFromCenter h) :
    data.toAFiberCoordinatesB.a = fun i : ZMod 19 => h.rotation i data.b0 :=
  rfl

/-- The B-base A-fiber coordinates are rotation equivariant. -/
theorem toAFiberRotationEquivarianceB
    (data : BranchOrbitABCFromCenter h) :
    AFiberRotationEquivariance h data.toAFiberCoordinatesB :=
  AFiberCoordinates.ofRotationOrbitOfMoved_rotationEquivariance
    h data.u data.b0 data.u_fixed data.b0_adj (by decide) data.b0_moved

/-- The B-base orbit selection input. -/
noncomputable def toOrbitBaseSelectionInputB
    (data : BranchOrbitABCFromCenter h) :
    OrbitBaseSelectionInput h :=
  AFiberCoordinates.ofRotationOrbitOfMoved_toOrbitBaseSelectionInput
    h data.u data.b0 data.u_fixed data.b0_adj
    (d := 1) (by decide) data.b0_moved

/-- The B-base orbit family union equals the B-fiber union under the B-base
A-fiber coordinates. -/
theorem toOrbitBaseSelectionInputB_orbitFamilyUnion_eq_allFibers
    (data : BranchOrbitABCFromCenter h) :
    data.toOrbitBaseSelectionInputB.orbitFamilyUnion =
      data.toAFiberCoordinatesB.allFibers := by
  unfold toOrbitBaseSelectionInputB toAFiberCoordinatesB
  exact data.toAFiberCoordinatesB.toOrbitBaseSelectionInputOfMoore_orbitFamilyUnion_eq_allFibers
    data.toAFiberRotationEquivarianceB

/-- `c0` is not in the rotation orbit of `b0`: B-orbit and C-orbit are
disjoint by the labeling. -/
theorem c0_not_mem_rotationOrbit_b0
    (data : BranchOrbitABCFromCenter h) :
    ∀ i : ZMod 19, h.rotation i data.b0 ≠ data.c0 := by
  intro i heq
  have hdisj :
      Disjoint
        (h.rotationOrbitFinset (data.base 1))
        (h.rotationOrbitFinset (data.base 2)) :=
    data.pairwise_disjoint 1 2 (by decide)
  have hb0 : data.base 1 = data.b0 := data.base_one
  have hc0 : data.base 2 = data.c0 := data.base_two
  rw [hb0, hc0] at hdisj
  have hcB : data.c0 ∈ h.rotationOrbitFinset data.b0 :=
    (h.mem_rotationOrbitFinset data.b0 data.c0).mpr ⟨i, heq⟩
  have hcC : data.c0 ∈ h.rotationOrbitFinset data.c0 :=
    (h.mem_rotationOrbitFinset data.c0 data.c0).mpr ⟨0, by simp⟩
  exact Finset.disjoint_left.mp hdisj hcB hcC

end BranchOrbitABCFromCenter

end Moore57
