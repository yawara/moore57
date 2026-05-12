import Moore57.D19OnMoore57.E7Projection.Minus8D19TraceInputBoundaryConsequences

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
