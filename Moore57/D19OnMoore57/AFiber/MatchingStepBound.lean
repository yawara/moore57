import Moore57.D19OnMoore57.AFiber.MatchingSupportEquations
import Moore57.D19OnMoore57.AFiber.OrbitMoved
import Moore57.D19OnMoore57.Rotation.OrbitInternalDiff

/-!
# Transposed A-fiber matching step bound

This file turns the coordinate-wise matching equation around: after fixing a
fiber index `i` and a coordinate `p`, the nonzero rotation steps `d` satisfying
the matching equation form a subset of the internal difference set of the
rotation orbit through the vertex represented by `(i, p)`.  The Moore
four-cycle bound then gives cardinality at most two.
-/

namespace Moore57

open Finset

noncomputable section

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instAFiberMatchingStepBoundDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace AFiberCoordinates

/-- The vertex represented by coordinate `p` in the `i`-th A-fiber chart. -/
def coordVertex (coords : AFiberCoordinates.{u, uP} Γ)
    (i : ZMod 19) (p : coords.P) : V :=
  ((coords.coord i p :
    {x : V // x ∈ branchFiber Γ coords.u (coords.a i)}) : V)

@[simp] theorem coordVertex_mem
    (coords : AFiberCoordinates.{u, uP} Γ)
    (i : ZMod 19) (p : coords.P) :
    coords.coordVertex i p ∈ coords.fiber i :=
  coords.coord_mem i p

end AFiberCoordinates

namespace AFiberRotationEquivariance

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}

/-- The rotation-coordinate permutation reads as literal rotation after
forgetting coordinates. -/
@[simp] theorem coordVertex_coordPerm_apply
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (p : coords.P) :
    coords.coordVertex (i + d) (rot.coordPerm d i p) =
      h.rotation d (coords.coordVertex i p) := by
  simp [AFiberCoordinates.coordVertex]

/-- For fixed `i` and `p`, the nonzero steps satisfying the explicit
matching equation. -/
def matchingStepSet
    (rot : AFiberRotationEquivariance h coords)
    (i : ZMod 19) (p : coords.P) : Finset (ZMod 19) := by
  classical
  exact ((Finset.univ : Finset (ZMod 19)).erase 0).filter fun d =>
    ∃ hd : d ≠ 0,
      AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
          (index_ne_add_of_ne_zero hd) p =
        rot.coordPerm d i p

theorem mem_matchingStepSet_iff
    (rot : AFiberRotationEquivariance h coords)
    (i : ZMod 19) (p : coords.P) (d : ZMod 19) :
    d ∈ rot.matchingStepSet i p ↔
      d ≠ 0 ∧
        ∃ hd : d ≠ 0,
          AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
              (index_ne_add_of_ne_zero hd) p =
            rot.coordPerm d i p := by
  classical
  simp [matchingStepSet]

/-- Bridge form: any step satisfying the fixed-coordinate matching equation is
an internal difference of the rotation orbit through that coordinate vertex. -/
theorem matchingStepSet_subset_internalDiffSet
    (rot : AFiberRotationEquivariance h coords)
    (i : ZMod 19) (p : coords.P) :
    rot.matchingStepSet i p ⊆
      internalDiffSet Γ
        (fun n : ZMod 19 => h.rotation n (coords.coordVertex i p)) := by
  classical
  intro d hdmem
  rcases (mem_matchingStepSet_iff rot i p d).mp hdmem with
    ⟨hd0, hdmatch⟩
  rcases hdmatch with ⟨hd, hmatch⟩
  have hAdjTarget :
      Γ.Adj (coords.coordVertex i p)
        (coords.coordVertex (i + d) (rot.coordPerm d i p)) := by
    exact
      (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore coords
        (index_ne_add_of_ne_zero hd) p (rot.coordPerm d i p)).2 hmatch
  have hAdj :
      Γ.Adj (coords.coordVertex i p)
        (h.rotation d (coords.coordVertex i p)) := by
    simpa [AFiberCoordinates.coordVertex, coordPerm] using hAdjTarget
  exact
    (h.mem_internalDiffSet_rotationOrbit_iff
      (coords.coordVertex i p) d).mpr ⟨hd0, hAdj⟩

/-- Transposed matching bound: for fixed coordinate `p` in fiber `i`, at most
two nonzero steps satisfy the matching equation. -/
theorem matchingStepSet_card_le_two
    (rot : AFiberRotationEquivariance h coords)
    (i : ZMod 19) (p : coords.P) :
    (rot.matchingStepSet i p).card ≤ 2 := by
  classical
  let y : V := coords.coordVertex i p
  have hsub :
      rot.matchingStepSet i p ⊆
        internalDiffSet Γ (fun n : ZMod 19 => h.rotation n y) := by
    simpa [y] using matchingStepSet_subset_internalDiffSet rot i p
  have hy : y ∈ coords.fiber i := by
    simpa [y] using AFiberCoordinates.coordVertex_mem coords i p
  have hmove : h.rotation (1 : ZMod 19) y ≠ y :=
    rot.moved_by_nonzero_rotation_of_mem_fiber
      (d := 1) (i := i) (by decide) hy
  have hinj : Function.Injective (fun n : ZMod 19 => h.rotation n y) :=
    h.rotation_orbit_injective_of_nonzero_moved
      (d := 1) (x := y) (by decide) hmove
  have hInternal :
      (internalDiffSet Γ (fun n : ZMod 19 => h.rotation n y)).card ≤ 2 :=
    Dq_card_le_two_of_moore h.isMoore
      (fun n : ZMod 19 => h.rotation n y) hinj
      (internalDiffSet Γ (fun n : ZMod 19 => h.rotation n y))
      (internalDiffSet_zero (Γ := Γ)
        (fun n : ZMod 19 => h.rotation n y))
      (fun d hd => internalDiffSet_adj
        (Γ := Γ) (fun n : ZMod 19 => h.rotation n y) hd)
      (fun d hd => internalDiffSet_symm
        (Γ := Γ) (fun n : ZMod 19 => h.rotation n y) hd)
  exact (Finset.card_le_card hsub).trans hInternal

/-- Raw-filter spelling of `matchingStepSet_card_le_two`. -/
theorem matchingEquation_step_filter_card_le_two
    (rot : AFiberRotationEquivariance h coords)
    (i : ZMod 19) (p : coords.P) :
    (((Finset.univ : Finset (ZMod 19)).erase 0).filter fun d =>
      ∃ hd : d ≠ 0,
        AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
            (index_ne_add_of_ne_zero hd) p =
          rot.coordPerm d i p).card ≤ 2 := by
  change (rot.matchingStepSet i p).card ≤ 2
  exact matchingStepSet_card_le_two rot i p

end AFiberRotationEquivariance

end

end Moore57
