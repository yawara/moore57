import Moore57.Moore57Graph.Moore57Definition
import Moore57.D19OnMoore57.Counting.AbstractCounting
import Moore57.D19OnMoore57.Action.D19Action

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The concrete `a1` attached to a `D19ActsOnMoore57` action is exactly the
adjacent-moved count of the corresponding rotation. -/
theorem rotation_a1_def (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) :
    adjacentMovedCount Γ (h.rotation d) = h.a1 d := by
  rfl

/-- Nontrivial-rotation form of `rotation_a1_def`, matching the field shape in
`TraceCharacterData`. -/
theorem rotation_a1_def_of_ne_zero (h : D19ActsOnMoore57 V Γ)
    (d : ZMod 19) (_hd : d ≠ 0) :
    adjacentMovedCount Γ (h.rotation d) = h.a1 d :=
  h.rotation_a1_def d

end D19ActsOnMoore57

end Moore57
