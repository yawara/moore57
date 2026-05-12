import Moore57.D19OnMoore57.Rotation.RotationOrbitFinset
import Moore57.D19OnMoore57.Rotation.RotationOrbitInternalDiff

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Rotations commute when applied at a vertex. -/
theorem rotation_apply_comm
    (h : D19ActsOnMoore57 V Γ) (d i : ZMod 19) (x : V) :
    h.rotation i (h.rotation d x) = h.rotation d (h.rotation i x) := by
  calc
    h.rotation i (h.rotation d x)
        = (h.rotation i * h.rotation d) x := by
            simp [Equiv.Perm.mul_apply]
    _ = h.rotation (i + d) x := by
            rw [← h.rotation_add]
    _ = h.rotation (d + i) x := by
            rw [add_comm]
    _ = (h.rotation d * h.rotation i) x := by
            rw [h.rotation_add]
    _ = h.rotation d (h.rotation i x) := by
            simp [Equiv.Perm.mul_apply]

/-- If `x` is sent to an adjacent vertex by rotation through `d`, then every
translate of `x` on its rotation orbit has the same property. -/
theorem adjacent_rotation_moved_on_orbit
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x : V}
    (hadj : Γ.Adj x (h.rotation d x)) (i : ZMod 19) :
    Γ.Adj (h.rotation i x) (h.rotation d (h.rotation i x)) := by
  have hAdj_i : Γ.Adj (h.rotation i x) (h.rotation i (h.rotation d x)) := by
    exact (h.smul_adj (DihedralGroup.r i) x (h.rotation d x)).mp hadj
  simpa [h.rotation_apply_comm d i x] using hAdj_i

/-- The same orbit-adjacency propagation with the target written as the
`i + d` orbit coordinate. -/
theorem adjacent_rotation_moved_on_orbit_add
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x : V}
    (hadj : Γ.Adj x (h.rotation d x)) (i : ZMod 19) :
    Γ.Adj (h.rotation i x) (h.rotation (i + d) x) := by
  have hAdj := h.adjacent_rotation_moved_on_orbit (d := d) (x := x) hadj i
  have htarget : h.rotation d (h.rotation i x) = h.rotation (i + d) x := by
    calc
      h.rotation d (h.rotation i x)
          = (h.rotation d * h.rotation i) x := by
              simp [Equiv.Perm.mul_apply]
      _ = h.rotation (d + i) x := by
              rw [← h.rotation_add]
      _ = h.rotation (i + d) x := by
              rw [add_comm]
  simpa [htarget] using hAdj

/-- Membership in the internal difference set for the rotation orbit gives
adjacency from every orbit coordinate to its `d`-translate. -/
theorem adjacent_rotation_moved_of_internalDiffSet
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x : V}
    (hd : d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x)) :
    ∀ i : ZMod 19, Γ.Adj (h.rotation i x) (h.rotation d (h.rotation i x)) := by
  intro i
  have hAdj :
      Γ.Adj (h.rotation i x) (h.rotation (i + d) x) :=
    internalDiffSet_adj (fun i : ZMod 19 => h.rotation i x) hd i
  have htarget : h.rotation (i + d) x = h.rotation d (h.rotation i x) := by
    calc
      h.rotation (i + d) x
          = (h.rotation i * h.rotation d) x := by
              rw [h.rotation_add]
      _ = h.rotation i (h.rotation d x) := by
              simp [Equiv.Perm.mul_apply]
      _ = h.rotation d (h.rotation i x) := h.rotation_apply_comm d i x
  simpa [htarget] using hAdj

/-- Internal difference-set membership implies every vertex in the finite
rotation orbit is sent to an adjacent vertex by the `d` rotation. -/
theorem adjacent_rotation_moved_of_mem_rotationOrbitFinset
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x y : V}
    (hd : d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x))
    (hy : y ∈ h.rotationOrbitFinset x) :
    Γ.Adj y (h.rotation d y) := by
  rcases (h.mem_rotationOrbitFinset x y).mp hy with ⟨i, rfl⟩
  exact h.adjacent_rotation_moved_of_internalDiffSet (d := d) (x := x) hd i

/-- Conversely, if every vertex in the finite rotation orbit is sent to an
adjacent vertex by `rotation d` and `d` is nonzero, then `d` is an internal
difference of the orbit-coordinate function. -/
theorem internalDiffSet_of_adjacent_rotation_moved_on_rotationOrbitFinset
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x : V}
    (hd0 : d ≠ 0)
    (hadj : ∀ y ∈ h.rotationOrbitFinset x, Γ.Adj y (h.rotation d y)) :
    d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x) := by
  classical
  rw [internalDiffSet]
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · simp [hd0]
  · intro i
    have hi : h.rotation i x ∈ h.rotationOrbitFinset x :=
      (h.mem_rotationOrbitFinset x (h.rotation i x)).mpr ⟨i, rfl⟩
    have hAdj : Γ.Adj (h.rotation i x) (h.rotation d (h.rotation i x)) :=
      hadj (h.rotation i x) hi
    have htarget : h.rotation d (h.rotation i x) = h.rotation (i + d) x := by
      calc
        h.rotation d (h.rotation i x)
            = (h.rotation d * h.rotation i) x := by
                simp [Equiv.Perm.mul_apply]
        _ = h.rotation (d + i) x := by
                rw [← h.rotation_add]
        _ = h.rotation (i + d) x := by
                rw [add_comm]
    simpa [htarget] using hAdj

end D19ActsOnMoore57

end Moore57
