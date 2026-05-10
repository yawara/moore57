import Moore57.E7Minus8D19TraceInputBoundaryConsequences
import Moore57.E7Minus8TraceRepresentationInversePairTraceBoundaryConsequences

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
