import Moore57.TraceInputFromFixedBounds
import Moore57.TraceDataSplit

/-!
# Coarse reduction of trace-character inputs

This file records the small amount of trace-character input still needed by the
current `D19TraceInput` interface.  The rotation and `a1` data come from the
ambient `D19ActsOnMoore57` witness; the remaining assumptions are:

* representation-theoretic multiplicity data,
* the nontrivial-rotation character identity,
* the coarse fixed-count upper bound `≤ 19`.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The trace-character assumptions still needed after specializing to a
`D19ActsOnMoore57` witness.

This deliberately has no independent `rotation` or `a1` fields: both are read
from `h`.  The fixed-point input is kept only as the coarse upper bound that the
current reduction needs in order to recover `RotationFixedData`. -/
structure D19CharacterInput (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and their arithmetic constraints. -/
  multiplicity : TraceMultiplicityData
  /-- The character value for every nontrivial rotation. -/
  rotation_character :
    ∀ d : ZMod 19, d ≠ 0 →
      Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
        (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) - (multiplicity.gamma : ℚ)
  /-- Coarse fixed-count input; exact fixed-point data is derived from this. -/
  fixed_le_nineteen :
    ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) ≤ 19

namespace D19CharacterInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the coarse character input into the current reduced trace input. -/
def toD19TraceInput (hin : D19CharacterInput h) : D19TraceInput h :=
  h.toD19TraceInput_of_fixed_le_nineteen
    hin.multiplicity hin.rotation_character hin.fixed_le_nineteen

/-- Convert the coarse character input directly to arithmetic trace data. -/
noncomputable def toTraceRepresentationData (hin : D19CharacterInput h) :
    TraceRepresentationData h.a1 :=
  hin.toD19TraceInput.toTraceRepresentationData

end D19CharacterInput

/-- Old bundled `TraceCharacterData` gives the coarse input when specialized to
the rotation and `a1` of the `D19ActsOnMoore57` witness.  The fixed-count bound
is obtained from the old exact fixed-point equality. -/
noncomputable def D19CharacterInput.ofTraceCharacterData
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1) :
    D19CharacterInput h where
  multiplicity := hold.toTraceMultiplicityData
  rotation_character := hold.rotation_character
  fixed_le_nineteen := by
    intro d hd
    rw [hold.rotation_fixed d hd]
    norm_num

end D19ActsOnMoore57

end Moore57
