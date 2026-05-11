import Moore57.E7Minus8RotationSplitAdjacentSwapNoGo
import Moore57.E7CharacterClassTraceBoundary
import Moore57.D19RotationSplitRawActionNoGoConnectors
import Moore57.D19RepresentationCharacterDataBridge

/-!
# Trace data from the rotation split and raw action

The concrete rotation split and the raw reflection fixed-count theorem now
construct the E7 character-class boundary with the side arithmetic
`alpha - beta = 33`, `alpha ≤ 113`, and `beta ≤ 58`.  This file reifies the
positive trace packages and reflection trace value obtained from that route,
rather than only exposing no-go endpoints.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Raw action plus the concrete rotation split supplies the trace-core
character boundary. -/
noncomputable def traceCoreCharacterBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    TraceCoreCharacterBoundary h :=
  h.representationCharacterComponentsBoundary_of_rotation_split_and_raw_action
    |>.toTraceCoreCharacterBoundary

/-- Raw action plus the concrete rotation split supplies the older
trace-representation data package. -/
noncomputable def traceRepresentationData_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    TraceRepresentationData h.a1 :=
  (h.traceCoreCharacterBoundary_of_rotation_split_raw_action)
    |>.toTraceRepresentationData

/-- Raw action plus the concrete rotation split gives E7 reflection trace
`33` for every reflection. -/
theorem e7_reflection_trace_eq_33_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ)
    (k : ZMod 19) :
    Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
      (33 : ℚ) := by
  classical
  rcases h.exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_raw_action
      0 with
    ⟨alpha, beta, gamma, characterClass, reflection, _, _⟩
  exact
    e7_reflection_trace_eq_33_of_E7ProjectionCharacterClassBoundary h
      alpha beta gamma characterClass reflection k

/-- Raw action plus the concrete rotation split also gives the E7
character-class trace-star route for every reflection. -/
theorem involutionFixedSetStar56_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  classical
  rcases h.exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_raw_action
      0 with
    ⟨alpha, beta, gamma, characterClass, reflection,
      minus8_trivial_nonneg, minus8_sign_nonneg⟩
  exact
    involutionFixedSetStar56_of_E7ProjectionCharacterClassBoundary h
      alpha beta gamma characterClass reflection minus8_trivial_nonneg
      minus8_sign_nonneg k

end D19ActsOnMoore57

end

end Moore57
