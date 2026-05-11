import Moore57.D19OnMoore57.Orbit.OrbitAdjacentMovedCount

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- On a rotation orbit, internal-difference membership is invariant under
negating the offset. -/
theorem internalDiffSet_rotationOrbit_neg_mem_iff
    (h : D19ActsOnMoore57 V Γ) (x : V) (d : ZMod 19) :
    -d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x) ↔
      d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x) := by
  constructor
  · intro hd
    have hdd :
        -(-d) ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x) :=
      internalDiffSet_symm (Γ := Γ)
        (fun i : ZMod 19 => h.rotation i x) hd
    simpa using hdd
  · intro hd
    exact internalDiffSet_symm (Γ := Γ)
      (fun i : ZMod 19 => h.rotation i x) hd

/-- On a fixed rotation orbit, the adjacent-moved filter has the same cardinality
for offsets `d` and `-d`. -/
theorem rotationOrbitFinset_filter_adjacent_rotation_moved_card_neg_eq
    (h : D19ActsOnMoore57 V Γ) (x : V) (d : ZMod 19) :
    ((h.rotationOrbitFinset x).filter fun y =>
        Γ.Adj y (h.rotation (-d) y)).card =
      ((h.rotationOrbitFinset x).filter fun y =>
        Γ.Adj y (h.rotation d y)).card := by
  classical
  by_cases hd0 : d = 0
  · subst d
    simp
  · by_cases hdMem :
        d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x)
    · have hnegMem :
          -d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x) :=
        (h.internalDiffSet_rotationOrbit_neg_mem_iff x d).2 hdMem
      rw [h.rotationOrbitFinset_filter_adjacent_rotation_moved_card_eq_card
          (d := -d) (x := x) hnegMem,
        h.rotationOrbitFinset_filter_adjacent_rotation_moved_card_eq_card
          (d := d) (x := x) hdMem]
    · have hneg0 : -d ≠ 0 := by
        intro hneg
        apply hd0
        simpa using congrArg Neg.neg hneg
      have hnegNot :
          -d ∉ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x) := by
        intro hnegMem
        exact hdMem ((h.internalDiffSet_rotationOrbit_neg_mem_iff x d).1 hnegMem)
      rw [h.rotationOrbitFinset_filter_adjacent_rotation_moved_card_eq_zero_of_nonzero_not_mem
          (d := -d) (x := x) hneg0 hnegNot,
        h.rotationOrbitFinset_filter_adjacent_rotation_moved_card_eq_zero_of_nonzero_not_mem
          (d := d) (x := x) hd0 hdMem]

end D19ActsOnMoore57

end Moore57
