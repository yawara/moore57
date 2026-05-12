import Moore57.D19OnMoore57.Rotation.FixedSets
import Moore57.Foundations.GroupAction.FixedPointBasics

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- All nontrivial rotations have the same number of fixed vertices. -/
theorem fixedVertexCount_rotation_eq_of_nonzero
    (h : D19ActsOnMoore57 V Γ) {d e : ZMod 19} (hd : d ≠ 0) (he : e ≠ 0) :
    fixedVertexCount (h.rotation d) = fixedVertexCount (h.rotation e) := by
  calc
    fixedVertexCount (h.rotation d)
        = Fintype.card (fixedVertexSet (h.rotation d)) := by
          rw [fixedVertexCount_eq_card_fixedVertexSet]
    _ = Fintype.card (fixedVertexSet (h.rotation e)) := by
          exact Fintype.card_congr
            (Equiv.setCongr (h.fixedVertexSet_rotation_eq_of_nonzero hd he))
    _ = fixedVertexCount (h.rotation e) := by
          rw [fixedVertexCount_eq_card_fixedVertexSet]

/-- Every nontrivial rotation has the same fixed-vertex count as rotation by `1`. -/
theorem fixedVertexCount_rotation_eq_one
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} (hd : d ≠ 0) :
    fixedVertexCount (h.rotation d) = fixedVertexCount (h.rotation 1) := by
  exact h.fixedVertexCount_rotation_eq_of_nonzero hd (by decide)

end D19ActsOnMoore57

end Moore57
