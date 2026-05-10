import Moore57.E7Minus8TraceRepresentationPackageBridge
import Moore57.E7Minus8InversePairTraceBoundaryBridge

/-!
# Trace-representation plus inverse-pair minus-8 trace boundary consequences

This file combines the older `TraceRepresentationData h.a1` E7 surface with
the inverse-pair `(-8)` projection trace boundary.  The inverse-pair trace
data is first expanded to the existing `D19CharacterValueBoundary` API, then
fed into the packaged E7/minus-8 reflection-count boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the packaged E7/minus-8 boundary from the older E7
`TraceRepresentationData h.a1` surface, inverse-pair complementary minus-8
projection trace data, and the standard count inputs at `sr 0`. -/
def ofTraceRepresentationDataAndMinus8InversePairTraceBoundary
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationData h data A B C
    minus8Trace.toCharacterValueBoundary
    rotation_fixed reflection_fixed_count reflection_adjacent_moved

/-- Fixed-star variant of
`ofTraceRepresentationDataAndMinus8InversePairTraceBoundary`: the `sr 0`
fixed-star witness supplies both standard reflection count inputs. -/
def ofTraceRepresentationDataAndMinus8InversePairTraceBoundaryAndReflectionStar
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationDataAndMinus8InversePairTraceBoundary h data A B C
    minus8Trace rotation_fixed
    hStar.fixedVertexCount_eq_56
    (hStar.adjacentMovedCount_eq_112 h.isMoore)

end E7Minus8CharacterReflectionCountBoundary

/-- Trace-representation E7 data plus inverse-pair minus-8 trace data and the
standard count inputs give a nonempty linear-character input. -/
theorem nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8InversePairTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8InversePairTraceBoundary
    h
    data A B C minus8Trace rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_d19LinearCharacterInput

/-- Trace-representation E7 data plus inverse-pair minus-8 trace data and the
standard count inputs give the paper-shaped fixed-star boundary for any
reflection. -/
theorem involutionFixedSetStar56_of_traceRepresentationDataAndMinus8InversePairTraceBoundary_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8InversePairTraceBoundary
    h
    data A B C minus8Trace rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.involutionFixedSetStar56_raw_reflection k

end D19ActsOnMoore57

end

end Moore57
