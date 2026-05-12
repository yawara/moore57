import Moore57.D19OnMoore57.Trace.DataSplit
import Moore57.D19OnMoore57.Rotation.FixedCardinality

/-!
# Bridges to rotation fixed-point data

This file packages weaker fixed-count bounds for nontrivial rotations into
`RotationFixedData`.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A nontrivial rotation with fewer than twenty fixed vertices has exactly one
fixed vertex. -/
theorem fixedVertexCount_rotation_eq_one_of_lt_twenty
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} (_hd : d ≠ 0)
    (hlt : fixedVertexCount (h.rotation d) < 20) :
    fixedVertexCount (h.rotation d) = 1 := by
  have hpos : 0 < fixedVertexCount (h.rotation d) :=
    h.fixedVertexCount_rotation_pos d
  by_contra hne
  have hone_lt : 1 < fixedVertexCount (h.rotation d) := by omega
  have htwenty : 20 ≤ fixedVertexCount (h.rotation d) :=
    h.fixedVertexCount_rotation_ge_twenty_of_one_lt d hone_lt
  omega

/-- Bounds by `< 20` for all nontrivial rotations give the fixed-point data
needed by the trace split. -/
def toRotationFixedData_of_lt_twenty
    (h : D19ActsOnMoore57 V Γ)
    (hlt : ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) < 20) :
    RotationFixedData h.rotation where
  rotation_fixed := by
    intro d hd
    exact h.fixedVertexCount_rotation_eq_one_of_lt_twenty hd (hlt d hd)

/-- Bounds by `≤ 19` for all nontrivial rotations give the fixed-point data
needed by the trace split. -/
def toRotationFixedData_of_le_nineteen
    (h : D19ActsOnMoore57 V Γ)
    (hle : ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) ≤ 19) :
    RotationFixedData h.rotation :=
  h.toRotationFixedData_of_lt_twenty (by
    intro d hd
    have hbound : fixedVertexCount (h.rotation d) ≤ 19 := hle d hd
    omega)

end D19ActsOnMoore57

end Moore57
