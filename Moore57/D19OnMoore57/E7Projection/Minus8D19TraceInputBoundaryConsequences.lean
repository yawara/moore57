import Moore57.D19OnMoore57.E7Projection.Minus8TraceRepresentationTraceBoundaryConsequences

/-!
# E7/minus-8 package consequences from `D19TraceInput`

This file moves one step upstream from `TraceRepresentationData h.a1`.
`D19TraceInput h` already carries the nontrivial rotation fixed-count data, so
the package constructors here only ask for the remaining minus-8 boundary and
reflection representative counts.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the packaged E7/minus-8 boundary from `D19TraceInput h`, a minus-8
value boundary, and the standard reflection representative counts. -/
def ofD19TraceInputAndMinus8Values
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationData h traceInput.toTraceRepresentationData
    A B C minus8Values traceInput.fixed.rotation_fixed
    reflection_fixed_count reflection_adjacent_moved

/-- Fixed-star variant of `ofD19TraceInputAndMinus8Values`. -/
def ofD19TraceInputAndMinus8ValuesAndReflectionStar
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationDataAndReflectionStar h
    traceInput.toTraceRepresentationData A B C minus8Values
    traceInput.fixed.rotation_fixed hStar

/-- Build the packaged E7/minus-8 boundary from `D19TraceInput h` and explicit
complementary minus-8 projection trace values. -/
def ofD19TraceInputAndMinus8ProjectionTraceBoundary
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8_one_trace :
      Matrix.trace (permMatrix (h.smulEquiv (1 : DihedralGroup 19))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (1 : DihedralGroup 19))) =
        (A : ℚ) + (B : ℚ) + 18 * (C : ℚ))
    (minus8_rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.r d))) - 1 -
            Matrix.trace (E7Matrix Γ *
              permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (A : ℚ) + (B : ℚ) - (C : ℚ))
    (minus8_reflection_zero_trace :
      Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.sr 0))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (A : ℚ) - (B : ℚ))
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationDataAndMinus8ProjectionTraceBoundary h
    traceInput.toTraceRepresentationData A B C
    minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
    traceInput.fixed.rotation_fixed
    reflection_fixed_count reflection_adjacent_moved

/-- Fixed-star variant of `ofD19TraceInputAndMinus8ProjectionTraceBoundary`. -/
def ofD19TraceInputAndMinus8ProjectionTraceBoundaryAndReflectionStar
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8_one_trace :
      Matrix.trace (permMatrix (h.smulEquiv (1 : DihedralGroup 19))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (1 : DihedralGroup 19))) =
        (A : ℚ) + (B : ℚ) + 18 * (C : ℚ))
    (minus8_rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.r d))) - 1 -
            Matrix.trace (E7Matrix Γ *
              permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (A : ℚ) + (B : ℚ) - (C : ℚ))
    (minus8_reflection_zero_trace :
      Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.sr 0))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (A : ℚ) - (B : ℚ))
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar h
    traceInput.toTraceRepresentationData A B C
    minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
    traceInput.fixed.rotation_fixed hStar

end E7Minus8CharacterReflectionCountBoundary

/-- `D19TraceInput` plus a minus-8 value boundary and reflection counts gives a
nonempty linear-character input. -/
theorem nonempty_d19LinearCharacterInput_of_d19TraceInputAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8Values h
    traceInput A B C minus8Values
    reflection_fixed_count reflection_adjacent_moved).nonempty_d19LinearCharacterInput

/-- `D19TraceInput` plus explicit minus-8 projection trace values and reflection
counts gives a nonempty linear-character input. -/
theorem nonempty_d19LinearCharacterInput_of_d19TraceInputAndMinus8ProjectionTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8_one_trace :
      Matrix.trace (permMatrix (h.smulEquiv (1 : DihedralGroup 19))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (1 : DihedralGroup 19))) =
        (A : ℚ) + (B : ℚ) + 18 * (C : ℚ))
    (minus8_rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.r d))) - 1 -
            Matrix.trace (E7Matrix Γ *
              permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (A : ℚ) + (B : ℚ) - (C : ℚ))
    (minus8_reflection_zero_trace :
      Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.sr 0))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (A : ℚ) - (B : ℚ))
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8ProjectionTraceBoundary
      h traceInput A B C
      minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
      reflection_fixed_count reflection_adjacent_moved).nonempty_d19LinearCharacterInput

end D19ActsOnMoore57

end

end Moore57
