import Moore57.RotationFixedDataBridge
import Moore57.FixedInducedDegree
import Moore57.FixedVertexOrbitComplement
import Moore57.RotationFixedCardEquality
import Moore57.TraceCharacterInputReduction

/-!
# Upper-bound inputs for rotation fixed counts

This file packages the remaining fixed-count input `≤ 19` for nontrivial
rotations, together with common stronger criteria that produce it.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Coarse upper-bound input for fixed vertices of nontrivial rotations. -/
structure RotationFixedUpperBoundInput (h : D19ActsOnMoore57 V Γ) where
  /-- Every nontrivial rotation has at most nineteen fixed vertices. -/
  fixed_le_nineteen :
    ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) ≤ 19

/-- It is enough to prove the upper bound for rotation by `1`, since all
nontrivial rotations have the same fixed-vertex count. -/
theorem fixed_le_nineteen_of_rotation_one
    (h : D19ActsOnMoore57 V Γ)
    (h_one : fixedVertexCount (h.rotation 1) ≤ 19) :
    ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) ≤ 19 := by
  intro d hd
  rw [h.fixedVertexCount_rotation_eq_one hd]
  exact h_one

/-- The global `≤ 19` upper bound is equivalent to checking rotation by `1`. -/
theorem fixed_le_nineteen_iff_rotation_one
    (h : D19ActsOnMoore57 V Γ) :
    (∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) ≤ 19) ↔
      fixedVertexCount (h.rotation 1) ≤ 19 := by
  constructor
  · intro hle
    exact hle 1 (by decide)
  · exact h.fixed_le_nineteen_of_rotation_one

namespace RotationFixedUpperBoundInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the coarse upper-bound input to exact `RotationFixedData`. -/
def toRotationFixedData (hin : RotationFixedUpperBoundInput h) :
    RotationFixedData h.rotation :=
  h.toRotationFixedData_of_le_nineteen hin.fixed_le_nineteen

/-- The coarse upper-bound input implies that rotation by `1` has exactly one
fixed vertex. -/
theorem rotation_one_fixed_count_eq_one
    (hin : RotationFixedUpperBoundInput h) :
    fixedVertexCount (h.rotation 1) = 1 :=
  hin.toRotationFixedData.rotation_fixed 1 (by decide)

/-- Bounds by `< 20` package into the coarse upper-bound input. -/
def of_lt_twenty
    (hlt : ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) < 20) :
    RotationFixedUpperBoundInput h where
  fixed_le_nineteen := by
    intro d hd
    have hbound : fixedVertexCount (h.rotation d) < 20 := hlt d hd
    omega

/-- A bound for rotation by `1` packages into the coarse upper-bound input. -/
def of_rotation_one_le_nineteen
    (h_one : fixedVertexCount (h.rotation 1) ≤ 19) :
    RotationFixedUpperBoundInput h where
  fixed_le_nineteen := h.fixed_le_nineteen_of_rotation_one h_one

/-- A strict `< 20` bound for rotation by `1` packages into the coarse
upper-bound input. -/
def of_rotation_one_lt_twenty
    (h_one : fixedVertexCount (h.rotation 1) < 20) :
    RotationFixedUpperBoundInput h :=
  of_rotation_one_le_nineteen (by omega)

/-- Add multiplicity and character inputs to produce the reduced trace input. -/
def toD19TraceInput
    (hin : RotationFixedUpperBoundInput h)
    (hmult : TraceMultiplicityData)
    (hchar :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (hmult.alpha : ℚ) + (hmult.beta : ℚ) - (hmult.gamma : ℚ)) :
    D19TraceInput h where
  multiplicity := hmult
  rotation_character := hchar
  fixed := hin.toRotationFixedData

/-- Add multiplicity and character inputs to produce the coarser character
input record. -/
def toD19CharacterInput
    (hin : RotationFixedUpperBoundInput h)
    (hmult : TraceMultiplicityData)
    (hchar :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (hmult.alpha : ℚ) + (hmult.beta : ℚ) - (hmult.gamma : ℚ)) :
    D19CharacterInput h where
  multiplicity := hmult
  rotation_character := hchar
  fixed_le_nineteen := hin.fixed_le_nineteen

end RotationFixedUpperBoundInput

end D19ActsOnMoore57

end Moore57
