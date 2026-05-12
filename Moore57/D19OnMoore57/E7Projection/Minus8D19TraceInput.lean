import Moore57.D19OnMoore57.E7Projection.Minus8TraceRepresentation
import Moore57.D19OnMoore57.Fixed.InducedStrongStarBridge

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

/-!
# D19 trace input plus complementary minus-8 boundary

This file lifts the concrete complementary `(-8)` bridge from
`TraceRepresentationData h.a1` to `D19TraceInput h`.  The trace input supplies
both the trace-representation data and the nontrivial rotation fixed-count
input; the remaining assumptions are the standard reflection representative
counts, or equivalently the fixed-star boundary at `sr 0`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the packaged E7/minus-8 boundary from `D19TraceInput h`, using the
complementary minus-8 projection formula and the standard reflection
representative counts. -/
def ofD19TraceInputComplement
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationDataComplement h
    traceInput.toTraceRepresentationData
    traceInput.fixed.rotation_fixed
    reflection_fixed_count reflection_adjacent_moved

/-- Fixed-star variant of `ofD19TraceInputComplement`. -/
def ofD19TraceInputComplementAndReflectionStar
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19TraceInputComplement h traceInput
    hStar.fixedVertexCount_eq_56
    (hStar.adjacentMovedCount_eq_112 h.isMoore)

end E7Minus8CharacterReflectionCountBoundary

/-- `D19TraceInput` plus the standard reflection counts gives a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_d19TraceInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement h
    traceInput reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_d19LinearCharacterInput

/-- The complementary `D19TraceInput` route gives the paper-shaped fixed-star
boundary for any reflection. -/
theorem involutionFixedSetStar56_of_d19TraceInputComplement_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement h
    traceInput reflection_fixed_count reflection_adjacent_moved)
      |>.involutionFixedSetStar56_raw_reflection k

/-- The complementary `D19TraceInput` route gives a nonempty `K_{1,55}` witness
for any reflection. -/
theorem nonempty_involutionK155_of_d19TraceInputComplement_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement h
    traceInput reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_involutionK155_raw_reflection k

/-- The complementary `D19TraceInput` route gives the fixed-center leaf
boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_d19TraceInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement h
    traceInput reflection_fixed_count reflection_adjacent_moved)
      |>.reflectionFixedCenterLeafBoundary

/-- The complementary `D19TraceInput` route gives the representation character
component boundary. -/
theorem representationCharacterComponentsBoundary_of_d19TraceInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement h
    traceInput reflection_fixed_count reflection_adjacent_moved)
      |>.representationCharacterComponentsBoundary

/-- The complementary `D19TraceInput` route rules out the current final-gap
boundary. -/
theorem no_currentFinalGapBoundary_of_d19TraceInputComplement
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement h
    traceInput reflection_fixed_count reflection_adjacent_moved)
      |>.no_currentFinalGapBoundary

/-- Fixed-star input variant of
`nonempty_d19LinearCharacterInput_of_d19TraceInputComplement`. -/
theorem nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionStar
    h traceInput hStar)
      |>.nonempty_d19LinearCharacterInput

/-- Fixed-star input variant of
`involutionFixedSetStar56_of_d19TraceInputComplement_raw_reflection`. -/
theorem involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionStar
    h traceInput hStar)
      |>.involutionFixedSetStar56_raw_reflection k

/-- Fixed-star input variant of
`nonempty_involutionK155_of_d19TraceInputComplement_raw_reflection`. -/
theorem nonempty_involutionK155_of_d19TraceInputComplementAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionStar
    h traceInput hStar)
      |>.nonempty_involutionK155_raw_reflection k

/-- Fixed-star input variant of
`reflectionFixedCenterLeafBoundary_of_d19TraceInputComplement`. -/
theorem reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionStar
    h traceInput hStar)
      |>.reflectionFixedCenterLeafBoundary

/-- Fixed-star input variant of
`representationCharacterComponentsBoundary_of_d19TraceInputComplement`. -/
theorem representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionStar
    h traceInput hStar)
      |>.representationCharacterComponentsBoundary

/-- Fixed-star input variant of
`no_currentFinalGapBoundary_of_d19TraceInputComplement`. -/
theorem no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionStar
    h traceInput hStar)
      |>.no_currentFinalGapBoundary

end D19ActsOnMoore57

end

end Moore57

/-!
# Direct no-go consumers from `D19TraceInput`

This file exposes downstream fixed-star, K155, fixed-center, component, and
current-gap consumers directly from `D19TraceInput` plus the minus-8 boundary
surfaces.  It deliberately routes through
`E7Minus8CharacterReflectionCountBoundary.ofD19TraceInput...` constructors,
not through the inverse-pair trace bridge.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- `D19TraceInput` plus a minus-8 value boundary and reflection counts gives
the paper-shaped fixed-star boundary for any reflection. -/
theorem involutionFixedSetStar56_of_d19TraceInputAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8Values h
    traceInput A B C minus8Values
    reflection_fixed_count reflection_adjacent_moved).involutionFixedSetStar56_raw_reflection k

/-- `D19TraceInput` plus a minus-8 value boundary and reflection counts gives
a `K_{1,55}` witness for any reflection. -/
theorem nonempty_involutionK155_of_d19TraceInputAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8Values h
    traceInput A B C minus8Values
    reflection_fixed_count reflection_adjacent_moved).nonempty_involutionK155_raw_reflection k

/-- `D19TraceInput` plus a minus-8 value boundary and reflection counts gives
the fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_d19TraceInputAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8Values h
    traceInput A B C minus8Values
    reflection_fixed_count reflection_adjacent_moved).reflectionFixedCenterLeafBoundary

/-- `D19TraceInput` plus a minus-8 value boundary and reflection counts gives
the representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_d19TraceInputAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8Values h
    traceInput A B C minus8Values
    reflection_fixed_count reflection_adjacent_moved).representationCharacterComponentsBoundary

/-- `D19TraceInput` plus a minus-8 value boundary and reflection counts rules
out the current branch-orbit final gap. -/
theorem no_currentFinalGapBoundary_of_d19TraceInputAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8Values h
    traceInput A B C minus8Values
    reflection_fixed_count reflection_adjacent_moved).no_currentFinalGapBoundary

/-- `D19TraceInput` plus explicit minus-8 projection traces and reflection
counts gives the paper-shaped fixed-star boundary for any reflection. -/
theorem involutionFixedSetStar56_of_d19TraceInputAndMinus8ProjectionTraceBoundary
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
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8ProjectionTraceBoundary
      h traceInput A B C
      minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
      reflection_fixed_count reflection_adjacent_moved).involutionFixedSetStar56_raw_reflection k

/-- `D19TraceInput` plus explicit minus-8 projection traces and reflection
counts gives a `K_{1,55}` witness for any reflection. -/
theorem nonempty_involutionK155_of_d19TraceInputAndMinus8ProjectionTraceBoundary
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
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8ProjectionTraceBoundary
      h traceInput A B C
      minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
      reflection_fixed_count reflection_adjacent_moved).nonempty_involutionK155_raw_reflection k

/-- `D19TraceInput` plus explicit minus-8 projection traces and reflection
counts gives the fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_d19TraceInputAndMinus8ProjectionTraceBoundary
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
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8ProjectionTraceBoundary
      h traceInput A B C
      minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
      reflection_fixed_count reflection_adjacent_moved).reflectionFixedCenterLeafBoundary

/-- `D19TraceInput` plus explicit minus-8 projection traces and reflection
counts gives the representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_d19TraceInputAndMinus8ProjectionTraceBoundary
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
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8ProjectionTraceBoundary
      h traceInput A B C
      minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
      reflection_fixed_count reflection_adjacent_moved).representationCharacterComponentsBoundary

/-- `D19TraceInput` plus explicit minus-8 projection traces and reflection
counts rules out the current branch-orbit final gap. -/
theorem no_currentFinalGapBoundary_of_d19TraceInputAndMinus8ProjectionTraceBoundary
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
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8ProjectionTraceBoundary
      h traceInput A B C
      minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
      reflection_fixed_count reflection_adjacent_moved).no_currentFinalGapBoundary

end D19ActsOnMoore57

end

end Moore57

/-!
# D19 trace input plus inverse-pair minus-8 trace consequences

This file is the `D19TraceInput` surface for the inverse-pair `(-8)` trace
boundary.  It reuses the trace-representation bridge after extracting
`TraceRepresentationData h.a1` and the nontrivial rotation fixed-count input
from `D19TraceInput h`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the packaged E7/minus-8 boundary from `D19TraceInput h`,
inverse-pair complementary minus-8 projection trace data, and the standard
reflection representative counts. -/
def ofD19TraceInputAndMinus8InversePairTraceBoundary
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationDataAndMinus8InversePairTraceBoundary h
    traceInput.toTraceRepresentationData A B C minus8Trace
    traceInput.fixed.rotation_fixed
    reflection_fixed_count reflection_adjacent_moved

/-- Fixed-star variant of
`ofD19TraceInputAndMinus8InversePairTraceBoundary`. -/
def ofD19TraceInputAndMinus8InversePairTraceBoundaryAndReflectionStar
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationDataAndMinus8InversePairTraceBoundaryAndReflectionStar h
    traceInput.toTraceRepresentationData A B C minus8Trace
    traceInput.fixed.rotation_fixed hStar

end E7Minus8CharacterReflectionCountBoundary

/-- `D19TraceInput` plus inverse-pair minus-8 trace data and the standard
count inputs give a nonempty linear-character input. -/
theorem nonempty_d19LinearCharacterInput_of_d19TraceInputAndMinus8InversePairTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8InversePairTraceBoundary
    h traceInput A B C minus8Trace
    reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_d19LinearCharacterInput

/-- `D19TraceInput` plus inverse-pair minus-8 trace data and the standard
count inputs give the paper-shaped fixed-star boundary for any reflection. -/
theorem involutionFixedSetStar56_of_d19TraceInputAndMinus8InversePairTraceBoundary_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8InversePairTraceBoundary
    h traceInput A B C minus8Trace
    reflection_fixed_count reflection_adjacent_moved)
      |>.involutionFixedSetStar56_raw_reflection k

/-- `D19TraceInput` plus inverse-pair minus-8 trace data and the standard
count inputs give a nonempty `K_{1,55}` witness for any reflection. -/
theorem nonempty_involutionK155_of_d19TraceInputAndMinus8InversePairTraceBoundary_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8InversePairTraceBoundary
    h traceInput A B C minus8Trace
    reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_involutionK155_raw_reflection k

/-- The `D19TraceInput` inverse-pair trace route rules out the current final
gap boundary. -/
theorem no_currentFinalGapBoundary_of_d19TraceInputAndMinus8InversePairTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8InversePairTraceBoundary
    h traceInput A B C minus8Trace
    reflection_fixed_count reflection_adjacent_moved)
      |>.no_currentFinalGapBoundary

/-- Fixed-star input variant of
`nonempty_d19LinearCharacterInput_of_d19TraceInputAndMinus8InversePairTraceBoundary`.
-/
theorem nonempty_d19LinearCharacterInput_of_d19TraceInputAndMinus8InversePairTraceBoundaryAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8InversePairTraceBoundaryAndReflectionStar
    h traceInput A B C minus8Trace hStar)
      |>.nonempty_d19LinearCharacterInput

/-- Fixed-star input variant of
`involutionFixedSetStar56_of_d19TraceInputAndMinus8InversePairTraceBoundary_raw_reflection`.
-/
theorem involutionFixedSetStar56_of_d19TraceInputAndMinus8InversePairTraceBoundaryAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8InversePairTraceBoundaryAndReflectionStar
    h traceInput A B C minus8Trace hStar)
      |>.involutionFixedSetStar56_raw_reflection k

/-- Fixed-star input variant of
`nonempty_involutionK155_of_d19TraceInputAndMinus8InversePairTraceBoundary_raw_reflection`.
-/
theorem nonempty_involutionK155_of_d19TraceInputAndMinus8InversePairTraceBoundaryAndReflectionStar_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8InversePairTraceBoundaryAndReflectionStar
    h traceInput A B C minus8Trace hStar)
      |>.nonempty_involutionK155_raw_reflection k

/-- Fixed-star input variant of
`no_currentFinalGapBoundary_of_d19TraceInputAndMinus8InversePairTraceBoundary`.
-/
theorem no_currentFinalGapBoundary_of_d19TraceInputAndMinus8InversePairTraceBoundaryAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8InversePairTraceBoundaryAndReflectionStar
    h traceInput A B C minus8Trace hStar)
      |>.no_currentFinalGapBoundary

end D19ActsOnMoore57

end

end Moore57

/-!
# Complementary minus-8 route from reflection fixed count only

The complementary `D19TraceInput` route previously accepted both the reflection
fixed count `56` and the adjacent-moved count `112`.  The fixed count already
implies the paper-shaped fixed-star statement for a raw reflection, and that
paper statement supplies the adjacent-moved count.  This file records the
smaller input surface.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the packaged E7/minus-8 boundary from `D19TraceInput h` and only
the fixed count `56` for the standard reflection representative.  The
adjacent-moved count is derived via the paper-shaped fixed-star bridge. -/
def ofD19TraceInputComplementAndReflectionFixedCount
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofD19TraceInputComplementAndReflectionStar h traceInput
    (h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56
      0 reflection_fixed_count)

end E7Minus8CharacterReflectionCountBoundary

/-- `D19TraceInput` plus the standard reflection fixed count gives a nonempty
linear-character input through the complementary minus-8 route. -/
theorem nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionFixedCount
    h traceInput
      reflection_fixed_count)
      |>.nonempty_d19LinearCharacterInput

/-- The fixed-count-only complementary route gives the paper-shaped fixed-star
boundary for any reflection. -/
theorem involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionFixedCount
    h traceInput
      reflection_fixed_count)
      |>.involutionFixedSetStar56_raw_reflection k

/-- The fixed-count-only complementary route gives a nonempty `K_{1,55}`
witness for any reflection. -/
theorem nonempty_involutionK155_of_d19TraceInputComplementAndReflectionFixedCount_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionFixedCount
    h traceInput
      reflection_fixed_count)
      |>.nonempty_involutionK155_raw_reflection k

/-- The fixed-count-only complementary route gives the fixed-center leaf
boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionFixedCount
    h traceInput
      reflection_fixed_count)
      |>.reflectionFixedCenterLeafBoundary

/-- The fixed-count-only complementary route gives the representation
character component boundary. -/
theorem representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionFixedCount
    h traceInput
      reflection_fixed_count)
      |>.representationCharacterComponentsBoundary

/-- The fixed-count-only complementary route rules out the current final-gap
boundary. -/
theorem no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (traceInput : D19TraceInput h)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionFixedCount
    h traceInput
      reflection_fixed_count)
      |>.no_currentFinalGapBoundary

end D19ActsOnMoore57

end

end Moore57

