import Moore57.D19OnMoore57.E7Projection.Minus8TraceBoundaryBridge
import Moore57.D19OnMoore57.D19Core.RepresentationCharacterDataBridge

/-!
# E7 class-boundary from the `a1` trace arithmetic

The newer mathlib-facing representation pipeline consumes
`D19CharacterClassBoundary h.e7ProjectionRepresentation`.  Older arithmetic
surfaces often expose the nontrivial-rotation information as
`TraceRepresentationData h.a1`, whose rotation field is the integer equation
`a1 d - 57 = 15 * (alpha + beta - gamma)`.

This file bridges those two surfaces using the Higman trace formula already
available for `D19ActsOnMoore57`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- If nontrivial rotations have one fixed vertex and the `a1` arithmetic
matches `alpha + beta - gamma`, then the E7 trace has the corresponding
rotation character value. -/
theorem e7_rotation_trace_eq_of_fixed_one_and_a1_trace
    (alpha beta gamma : ℕ)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (rotation_a1_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        ((h.a1 d : ℚ) - 57) =
          15 * ((alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)))
    (d : ZMod 19) (hd : d ≠ 0) :
    Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
      (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ) := by
  rw [h.rotation_trace_eq_fixed_a1 d, rotation_fixed d hd]
  have htrace := rotation_a1_trace d hd
  calc
    (8 * (1 : ℚ) + (h.a1 d : ℚ) - 65) / 15
        = ((h.a1 d : ℚ) - 57) / 15 := by ring
    _ = (15 * ((alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))) / 15 := by
      rw [htrace]
    _ = (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ) := by ring

/-- Integer `TraceRepresentationData` rotation arithmetic gives the E7
rotation character value once nontrivial rotations have one fixed vertex. -/
theorem e7_rotation_trace_eq_of_traceRepresentationData
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (d : ZMod 19) (hd : d ≠ 0) :
    Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
      (data.alpha : ℚ) + (data.beta : ℚ) - (data.gamma : ℚ) := by
  apply h.e7_rotation_trace_eq_of_fixed_one_and_a1_trace
  · exact rotation_fixed
  · intro e he
    have hint := data.rotation_trace e he
    exact_mod_cast hint
  · exact hd

namespace E7ProjectionCharacterClassBoundary

/-- Build the E7 projection class-boundary from the `a1` trace arithmetic
surface plus the reflection representative trace. -/
def ofTraceRepresentationData
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_zero_trace :
      Matrix.trace (E7Matrix Γ *
          permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (data.alpha : ℚ) - (data.beta : ℚ)) :
    D19CharacterClassBoundary h.e7ProjectionRepresentation
      data.alpha data.beta data.gamma :=
  D19CharacterClassBoundary.ofE7ProjectionTraceBoundary h
    data.alpha data.beta data.gamma
    data.dimension
    (by
      intro d hd
      simpa [D19ActsOnMoore57.rotation] using
        h.e7_rotation_trace_eq_of_traceRepresentationData
          data rotation_fixed d hd)
    reflection_zero_trace

/-- Reflection fixed count `56` and adjacent-moved count `112` give the E7
reflection representative trace required by the class-boundary API. -/
theorem reflection_zero_trace_eq_of_traceRepresentationData_and_counts
    (data : TraceRepresentationData h.a1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Matrix.trace (E7Matrix Γ *
        permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
      (data.alpha : ℚ) - (data.beta : ℚ) := by
  have hreflectionℚ :
      (data.alpha : ℚ) - (data.beta : ℚ) = 33 := by
    exact_mod_cast data.reflection
  rw [h.isMoore.higman_trace_formula,
    reflection_fixed_count, reflection_adjacent_moved]
  rw [hreflectionℚ]
  norm_num

/-- Build the E7 projection class-boundary from the `a1` trace arithmetic,
nontrivial rotation fixed count `1`, and the standard reflection count inputs
at `sr 0`. -/
def ofTraceRepresentationDataAndReflectionCounts
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    D19CharacterClassBoundary h.e7ProjectionRepresentation
      data.alpha data.beta data.gamma :=
  ofTraceRepresentationData h data rotation_fixed
    (reflection_zero_trace_eq_of_traceRepresentationData_and_counts h
      data reflection_fixed_count reflection_adjacent_moved)

end E7ProjectionCharacterClassBoundary

end D19ActsOnMoore57

end

end Moore57
