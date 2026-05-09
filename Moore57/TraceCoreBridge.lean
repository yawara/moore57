import Moore57.TraceDataSplit
import Moore57.D19ActionTraceBridge

/-!
# Bridges from `D19ActsOnMoore57` to split trace core data

This file specializes the split trace records to the `D19ActsOnMoore57`
rotation and `a1` definitions.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Package multiplicity data and the nontrivial-rotation character identity
into the split trace core data for the rotation action attached to
`D19ActsOnMoore57`. -/
noncomputable def toTraceCharacterCoreData
    (h : D19ActsOnMoore57 V Γ)
    (hmult : TraceMultiplicityData)
    (hchar :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (hmult.alpha : ℚ) + (hmult.beta : ℚ) - (hmult.gamma : ℚ)) :
    TraceCharacterCoreData Γ h.rotation h.a1 where
  toTraceMultiplicityData := hmult
  rotation_a1 := h.rotation_a1_def_of_ne_zero
  rotation_character := hchar

/-- Combine the specialized trace core data with fixed-point data to obtain
the arithmetic trace representation data for the `D19ActsOnMoore57` `a1`. -/
noncomputable def toTraceRepresentationData
    (h : D19ActsOnMoore57 V Γ)
    (hmult : TraceMultiplicityData)
    (hchar :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (hmult.alpha : ℚ) + (hmult.beta : ℚ) - (hmult.gamma : ℚ))
    (hfixed : RotationFixedData h.rotation) :
    TraceRepresentationData h.a1 :=
  (h.toTraceCharacterCoreData hmult hchar).toTraceRepresentationData hfixed h.isMoore

end D19ActsOnMoore57

end Moore57
