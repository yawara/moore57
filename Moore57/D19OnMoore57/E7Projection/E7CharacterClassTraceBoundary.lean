import Moore57.D19OnMoore57.E7Projection.E7LinearCharacterInputBridge
import Moore57.D19OnMoore57.E7Projection.E7TraceThirtyThreeComplementBoundary

/-!
# E7 character-class boundary to trace-thirty-three routes

This file packages the current representation-theoretic frontier in the shape
suggested by the natural-language proof: once the concrete E7 projection
representation has the D19 character-class values with `alpha - beta = 33`, the
existing trace-core and reflection-trace routes supply the fixed-star and final
no-go consequences.
-/

namespace Moore57

noncomputable section

universe u

namespace D19ActsOnMoore57

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Repackage D19 character-class data for the concrete E7 projection
representation as the trace-core boundary used by the arithmetic pipeline. -/
def traceCoreCharacterBoundary_of_E7ProjectionCharacterClassBoundary
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (characterClass :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    TraceCoreCharacterBoundary h :=
  TraceCoreCharacterBoundary.ofComponents (h := h)
    alpha beta gamma reflection characterClass.dimension
    minus8_trivial_nonneg minus8_sign_nonneg
    (by
      intro d hd
      calc
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d))
            = (h.e7ProjectionRepresentation).character
                (DihedralGroup.r d) := by
              simpa [D19ActsOnMoore57.rotation] using
                (h.e7ProjectionRepresentation_character_eq_matrix_trace
                  (DihedralGroup.r d)).symm
        _ = (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ) :=
              characterClass.rotation_value d hd)

/-- D19 character-class data with `alpha - beta = 33` gives E7 trace `33` for
every reflection. -/
theorem e7_reflection_trace_eq_33_of_E7ProjectionCharacterClassBoundary
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (characterClass :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (k : ZMod 19) :
    Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
      (33 : ℚ) := by
  have hreflectionℚ : (alpha : ℚ) - (beta : ℚ) = (33 : ℚ) := by
    exact_mod_cast reflection
  calc
    Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k)))
        = (h.e7ProjectionRepresentation).character (DihedralGroup.sr k) := by
          exact
            (h.e7ProjectionRepresentation_character_eq_matrix_trace
              (DihedralGroup.sr k)).symm
    _ = (alpha : ℚ) - (beta : ℚ) :=
          characterClass.reflection_value k
    _ = (33 : ℚ) := hreflectionℚ

/-- The same character-class data lowers to the older trace-representation
record without asking separately for reflection fixed counts. -/
def traceRepresentationData_of_E7ProjectionCharacterClassBoundary
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (characterClass :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    TraceRepresentationData h.a1 :=
  (traceCoreCharacterBoundary_of_E7ProjectionCharacterClassBoundary h
      alpha beta gamma characterClass reflection
      minus8_trivial_nonneg minus8_sign_nonneg).toTraceRepresentationData

/-- Character-class reflection value `33` forces reflection fixed count `56`
through the trace-thirty-three route. -/
theorem fixedVertexCount_reflection_eq_56_of_E7ProjectionCharacterClassBoundary
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (characterClass :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
  h.fixedVertexCount_reflection_eq_56_of_E7_trace_eq_33 k
    (e7_reflection_trace_eq_33_of_E7ProjectionCharacterClassBoundary h
      alpha beta gamma characterClass reflection k)

/-- Character-class data gives the fixed-star boundary for every reflection. -/
theorem involutionFixedSetStar56_of_E7ProjectionCharacterClassBoundary
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (characterClass :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_traceCoreComplementAndE7ReflectionTraceThirtyThree
    h
    (traceCoreCharacterBoundary_of_E7ProjectionCharacterClassBoundary h
      alpha beta gamma characterClass reflection
      minus8_trivial_nonneg minus8_sign_nonneg)
    (fun k =>
      e7_reflection_trace_eq_33_of_E7ProjectionCharacterClassBoundary h
        alpha beta gamma characterClass reflection k)
    k

/-- Character-class data rules out the current final-gap boundary through the
trace-core complement route. -/
theorem no_currentFinalGapBoundary_of_E7ProjectionCharacterClassBoundary
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (characterClass :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_currentFinalGapBoundary_of_traceCoreComplementAndE7ReflectionTraceThirtyThree
    h
    (traceCoreCharacterBoundary_of_E7ProjectionCharacterClassBoundary h
      alpha beta gamma characterClass reflection
      minus8_trivial_nonneg minus8_sign_nonneg)
    (fun k =>
      e7_reflection_trace_eq_33_of_E7ProjectionCharacterClassBoundary h
        alpha beta gamma characterClass reflection k)

end D19ActsOnMoore57

end

end Moore57
