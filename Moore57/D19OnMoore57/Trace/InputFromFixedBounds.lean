import Moore57.D19OnMoore57.Trace.MultiplicityPackaging
import Moore57.D19OnMoore57.Rotation.FixedDataBridge

/-!
# D19 trace input from fixed-count bounds

This file packages fixed-count bounds for nontrivial rotations directly into
`D19TraceInput`.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Multiplicity data, nontrivial-rotation character values, and `< 20`
fixed-count bounds package into `D19TraceInput`. -/
def toD19TraceInput_of_fixed_lt_twenty
    (h : D19ActsOnMoore57 V Γ)
    (hmult : TraceMultiplicityData)
    (hchar :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (hmult.alpha : ℚ) + (hmult.beta : ℚ) - (hmult.gamma : ℚ))
    (hlt : ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) < 20) :
    D19TraceInput h where
  multiplicity := hmult
  rotation_character := hchar
  fixed := h.toRotationFixedData_of_lt_twenty hlt

/-- Multiplicity data, nontrivial-rotation character values, and `≤ 19`
fixed-count bounds package into `D19TraceInput`. -/
def toD19TraceInput_of_fixed_le_nineteen
    (h : D19ActsOnMoore57 V Γ)
    (hmult : TraceMultiplicityData)
    (hchar :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (hmult.alpha : ℚ) + (hmult.beta : ℚ) - (hmult.gamma : ℚ))
    (hle : ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) ≤ 19) :
    D19TraceInput h where
  multiplicity := hmult
  rotation_character := hchar
  fixed := h.toRotationFixedData_of_le_nineteen hle

/-- Directly produce the arithmetic trace representation data from `≤ 19`
fixed-count bounds. -/
noncomputable def toTraceRepresentationData_of_fixed_le_nineteen
    (h : D19ActsOnMoore57 V Γ)
    (hmult : TraceMultiplicityData)
    (hchar :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (hmult.alpha : ℚ) + (hmult.beta : ℚ) - (hmult.gamma : ℚ))
    (hle : ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) ≤ 19) :
    TraceRepresentationData h.a1 :=
  (h.toD19TraceInput_of_fixed_le_nineteen hmult hchar hle).toTraceRepresentationData

end D19ActsOnMoore57

end Moore57
