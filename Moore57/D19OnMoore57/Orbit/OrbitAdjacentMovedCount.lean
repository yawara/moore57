import Moore57.D19OnMoore57.AdjacentMoved.AdjacentMovedOnOrbit
import Moore57.D19OnMoore57.Fixed.FixedVertexOrbitComplement

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- If `d` is an internal difference of the rotation orbit through `x`, then
every vertex in that finite orbit is counted by the adjacent-moved filter. -/
theorem rotationOrbitFinset_filter_adjacent_rotation_moved_card_eq_card
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x : V}
    (hd : d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x)) :
    ((h.rotationOrbitFinset x).filter
        fun y => Γ.Adj y (h.rotation d y)).card =
      (h.rotationOrbitFinset x).card := by
  classical
  have hFilter :
      (h.rotationOrbitFinset x).filter
          (fun y => Γ.Adj y (h.rotation d y)) =
        h.rotationOrbitFinset x := by
    ext y
    constructor
    · intro hy
      exact (Finset.mem_filter.mp hy).1
    · intro hy
      exact Finset.mem_filter.mpr
        ⟨hy, h.adjacent_rotation_moved_of_mem_rotationOrbitFinset hd hy⟩
  rw [hFilter]

/-- If nonzero `d` is not an internal difference of the rotation orbit through
`x`, then no vertex in that orbit is sent to an adjacent vertex by
`rotation d`. -/
theorem rotationOrbitFinset_filter_adjacent_rotation_moved_card_eq_zero_of_nonzero_not_mem
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x : V}
    (hd0 : d ≠ 0)
    (hdNot : d ∉ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x)) :
    ((h.rotationOrbitFinset x).filter
        fun y => Γ.Adj y (h.rotation d y)).card = 0 := by
  classical
  rw [Finset.card_eq_zero]
  ext y
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hyOrbit, hyAdj⟩
    exfalso
    apply hdNot
    rcases (h.mem_rotationOrbitFinset x y).mp hyOrbit with ⟨i, rfl⟩
    apply h.internalDiffSet_of_adjacent_rotation_moved_on_rotationOrbitFinset hd0
    intro z hzOrbit
    rcases (h.mem_rotationOrbitFinset x z).mp hzOrbit with ⟨j, rfl⟩
    have hAdj :=
      h.adjacent_rotation_moved_on_orbit
        (d := d) (x := h.rotation i x) hyAdj (j - i)
    have hbase :
        h.rotation (j - i) (h.rotation i x) = h.rotation j x := by
      calc
        h.rotation (j - i) (h.rotation i x)
            = (h.rotation (j - i) * h.rotation i) x := by
                simp [Equiv.Perm.mul_apply]
        _ = h.rotation ((j - i) + i) x := by
                rw [← h.rotation_add]
        _ = h.rotation j x := by
                rw [sub_add_cancel]
    simpa [hbase] using hAdj
  · intro hy
    simp at hy

/-- If `d` is an internal difference of the rotation orbit through `x`, and
some nonzero rotation moves `x`, then exactly nineteen vertices of that orbit
are sent to adjacent vertices by `rotation d`. -/
theorem rotationOrbitFinset_filter_adjacent_rotation_moved_card_eq_nineteen
    (h : D19ActsOnMoore57 V Γ) {d e : ZMod 19} {x : V}
    (hd : d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x))
    (he0 : e ≠ 0) (hemove : h.rotation e x ≠ x) :
    ((h.rotationOrbitFinset x).filter
        fun y => Γ.Adj y (h.rotation d y)).card = 19 := by
  rw [h.rotationOrbitFinset_filter_adjacent_rotation_moved_card_eq_card hd]
  exact h.rotationOrbitFinset_card_eq_nineteen_of_nonzero_moved' he0 hemove

end D19ActsOnMoore57

end Moore57
