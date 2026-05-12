import Moore57.D19OnMoore57.E7Projection.Minus8TraceRepresentationPackageBridge
import Moore57.D19OnMoore57.LinearCharacter.Dimension

/-!
# Complementary minus-8 boundary from trace-representation data

This file closes the concrete complement bridge: once `TraceRepresentationData`
has built the E7 boundary, the `(-8)` projection character values are the
vertex permutation trace minus the trivial and E7 traces.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace TraceRepresentationData

variable {a1 : ZMod 19 → ℕ}

/-- The `γ` multiplicity is bounded strongly enough to form the complementary
`(-8)` multiplicity `171 - γ`. -/
theorem gamma_le_171 (data : TraceRepresentationData a1) :
    data.gamma ≤ 171 := by
  have hmul :
      18 * data.gamma ≤ data.alpha + data.beta + 18 * data.gamma := by
    omega
  rw [data.dimension] at hmul
  omega

end TraceRepresentationData

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- The concrete `(-8)` projection representation has the complementary D19
character values determined by `TraceRepresentationData h.a1`.

The E7 values are supplied by
`E7ProjectionCharacterClassBoundary.ofTraceRepresentationDataAndReflectionCounts`;
the complement is computed from the permutation trace, the trivial line, and
the E7 projection trace. -/
theorem minus8ProjectionRepresentation_characterValueBoundary_of_traceRepresentationDataComplement
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    D19CharacterValueBoundary h.minus8ProjectionRepresentation
      (113 - data.alpha) (58 - data.beta) (171 - data.gamma) := by
  let e7Class :=
    E7ProjectionCharacterClassBoundary.ofTraceRepresentationDataAndReflectionCounts
      h data rotation_fixed reflection_fixed_count reflection_adjacent_moved
  have hAℚ :
      (((113 - data.alpha : ℕ) : ℚ) =
        (113 : ℚ) - (data.alpha : ℚ)) := by
    exact Nat.cast_sub data.minus8_trivial_nonneg
  have hBℚ :
      (((58 - data.beta : ℕ) : ℚ) =
        (58 : ℚ) - (data.beta : ℚ)) := by
    exact Nat.cast_sub data.minus8_sign_nonneg
  have hCℚ :
      (((171 - data.gamma : ℕ) : ℚ) =
        (171 : ℚ) - (data.gamma : ℚ)) := by
    exact Nat.cast_sub data.gamma_le_171
  refine
    { one_value := ?_
      rotation_value := ?_
      reflection_zero := ?_ }
  · have he7_one := e7Class.one_value h.finrank_E7Range_eq_1729
    rw [h.e7ProjectionRepresentation_character_eq_matrix_trace] at he7_one
    rw [h.smulEquiv_one] at he7_one
    rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
    rw [h.smulEquiv_one]
    rw [trace_permMatrix_eq_fixedVertexCount, fixedVertexCount_one, h.isMoore.card]
    rw [he7_one]
    rw [hAℚ, hBℚ, hCℚ]
    ring_nf
  · intro d hd
    have he7_rotation := e7Class.rotation_value d hd
    rw [h.e7ProjectionRepresentation_character_eq_matrix_trace] at he7_rotation
    have hfix :
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1 := by
      simpa [D19ActsOnMoore57.rotation] using rotation_fixed d hd
    rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
    rw [trace_permMatrix_eq_fixedVertexCount, hfix]
    rw [he7_rotation]
    rw [hAℚ, hBℚ, hCℚ]
    ring_nf
  · have he7_reflection := e7Class.reflection_zero
    rw [h.e7ProjectionRepresentation_character_eq_matrix_trace] at he7_reflection
    rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
    rw [trace_permMatrix_eq_fixedVertexCount, reflection_fixed_count]
    rw [he7_reflection]
    rw [hAℚ, hBℚ]
    ring_nf

namespace E7Minus8CharacterReflectionCountBoundary

/-- Package the E7 trace-representation boundary with the complementary
minus-8 character-value boundary. -/
def ofTraceRepresentationDataComplement
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationData h data
    (113 - data.alpha) (58 - data.beta) (171 - data.gamma)
    (h.minus8ProjectionRepresentation_characterValueBoundary_of_traceRepresentationDataComplement
      data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
    rotation_fixed reflection_fixed_count reflection_adjacent_moved

end E7Minus8CharacterReflectionCountBoundary

/-- Trace-representation E7 data and the standard count inputs give a nonempty
linear-character input, with the minus-8 values supplied by the complementary
projection formula. -/
theorem nonempty_d19LinearCharacterInput_of_traceRepresentationDataComplement
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_d19LinearCharacterInput

end D19ActsOnMoore57

end

end Moore57
