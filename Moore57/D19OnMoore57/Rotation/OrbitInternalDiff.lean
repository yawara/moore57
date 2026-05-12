import Moore57.D19OnMoore57.Rotation.FixedCardinality
import Moore57.Moore57Graph.InternalDiffSet.Translate

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- For a rotation orbit, an internal difference is exactly a nonzero rotation
whose endpoint from the base vertex is adjacent to the base vertex. -/
theorem mem_internalDiffSet_rotationOrbit_iff
    (h : D19ActsOnMoore57 V Γ) (x : V) (d : ZMod 19) :
    d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x) ↔
      d ≠ 0 ∧ Γ.Adj x (h.rotation d x) := by
  classical
  rw [internalDiffSet]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hdMem, hAdj⟩
    have hd0 : d ≠ 0 := by
      simpa using hdMem
    refine ⟨hd0, ?_⟩
    simpa using hAdj 0
  · rintro ⟨hd0, hAdj⟩
    refine ⟨?_, ?_⟩
    · simp [hd0]
    intro i
    have hi :
        Γ.Adj (h.rotation i x) (h.rotation i (h.rotation d x)) := by
      simpa [rotation] using
        (h.smul_adj (DihedralGroup.r i) x (h.rotation d x)).mp hAdj
    have hcomp : h.rotation i (h.rotation d x) = h.rotation (i + d) x := by
      calc
        h.rotation i (h.rotation d x)
            = (h.rotation i * h.rotation d) x := by
                simp [Equiv.Perm.mul_apply]
        _ = h.rotation (i + d) x := by
                rw [← h.rotation_add]
    simpa [hcomp] using hi

/-- Forward direction of `mem_internalDiffSet_rotationOrbit_iff`. -/
theorem internalDiffSet_rotationOrbit_adj
    (h : D19ActsOnMoore57 V Γ) {x : V} {d : ZMod 19}
    (hd : d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x)) :
    Γ.Adj x (h.rotation d x) :=
  ((h.mem_internalDiffSet_rotationOrbit_iff x d).mp hd).2

/-- Reverse direction of `mem_internalDiffSet_rotationOrbit_iff`. -/
theorem mem_internalDiffSet_rotationOrbit_of_adj
    (h : D19ActsOnMoore57 V Γ) {x : V} {d : ZMod 19}
    (hd0 : d ≠ 0) (hAdj : Γ.Adj x (h.rotation d x)) :
    d ∈ internalDiffSet Γ (fun i : ZMod 19 => h.rotation i x) :=
  (h.mem_internalDiffSet_rotationOrbit_iff x d).mpr ⟨hd0, hAdj⟩

end D19ActsOnMoore57

end Moore57
