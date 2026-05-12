import Moore57.D19OnMoore57.E7Projection.Minus8BoundaryPackage
import Moore57.D19OnMoore57.E7Projection.Minus8CharacterBoundaryPackages
import Moore57.D19OnMoore57.E7Projection.Minus8InversePairTrace
import Moore57.D19OnMoore57.E7Projection.ProjectionA1CharacterBoundary
import Moore57.D19OnMoore57.Fixed.InducedStrongStarBridge
import Moore57.D19OnMoore57.LinearCharacter.Dimension

/-!
# Package bridge from trace-representation data

This file connects the older `TraceRepresentationData h.a1` arithmetic surface
to the newer Type-valued E7/minus-8 character boundary package.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the direct E7/minus-8 character package from the older
`TraceRepresentationData h.a1` arithmetic data, a minus-8 value-boundary, and
the standard count inputs at the reflection representative `sr 0`. -/
def ofTraceRepresentationData
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    E7Minus8CharacterReflectionCountBoundary h where
  alpha := data.alpha
  beta := data.beta
  gamma := data.gamma
  A := A
  B := B
  C := C
  e7Class :=
    E7ProjectionCharacterClassBoundary.ofTraceRepresentationDataAndReflectionCounts
      h data rotation_fixed reflection_fixed_count reflection_adjacent_moved
  minus8Values := minus8Values
  dt := 0
  reflection_fixed_count := reflection_fixed_count
  reflection_adjacent_moved := reflection_adjacent_moved
  rotation_fixed_count := rotation_fixed

/-- Fixed-star form of `ofTraceRepresentationData`: the `sr 0` fixed-star
boundary supplies both standard reflection count inputs. -/
def ofTraceRepresentationDataAndReflectionStar
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationData h data A B C minus8Values rotation_fixed
    hStar.fixedVertexCount_eq_56
    (hStar.adjacentMovedCount_eq_112 h.isMoore)

end E7Minus8CharacterReflectionCountBoundary

end D19ActsOnMoore57

end

end Moore57

/-!
# Direct consequences of trace-representation E7/minus-8 data

This file keeps the `TraceRepresentationData h.a1` surface thin: build the
packaged E7/minus-8 character boundary, then expose the standard downstream
linear-character, fixed-star, `K_{1,55}`, component, and current-gap
consequences.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Trace-representation E7 data plus minus-8 value data and the standard
count inputs give a nonempty linear-character input. -/
theorem nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationData h
    data A B C minus8Values rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_d19LinearCharacterInput

/-- Trace-representation E7 data plus minus-8 value data and the standard
count inputs give the paper-shaped fixed-star boundary for any reflection. -/
theorem involutionFixedSetStar56_of_traceRepresentationDataAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationData h
    data A B C minus8Values rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.involutionFixedSetStar56_raw_reflection k

/-- Trace-representation E7 data plus minus-8 value data and the standard
count inputs give a nonempty `K_{1,55}` witness for any reflection. -/
theorem nonempty_involutionK155_of_traceRepresentationDataAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationData h
    data A B C minus8Values rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_involutionK155_raw_reflection k

/-- Trace-representation E7 data plus minus-8 value data and the standard
count inputs give the fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_traceRepresentationDataAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationData h
    data A B C minus8Values rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.reflectionFixedCenterLeafBoundary

/-- Trace-representation E7 data plus minus-8 value data and the standard
count inputs give the representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_traceRepresentationDataAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationData h
    data A B C minus8Values rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.representationCharacterComponentsBoundary

/-- Trace-representation E7 data plus minus-8 value data and the standard
count inputs rule out the current final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_traceRepresentationDataAndMinus8Values
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationData h
    data A B C minus8Values rotation_fixed
    reflection_fixed_count reflection_adjacent_moved)
      |>.no_currentFinalGapBoundary

/-- Fixed-star input variant of
`nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8Values`.
-/
theorem nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndReflectionStar
    h data A B C minus8Values rotation_fixed hStar)
      |>.nonempty_d19LinearCharacterInput

/-- Fixed-star input variant of
`involutionFixedSetStar56_of_traceRepresentationDataAndMinus8Values`. -/
theorem involutionFixedSetStar56_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndReflectionStar
    h data A B C minus8Values rotation_fixed hStar)
      |>.involutionFixedSetStar56_raw_reflection k

/-- Fixed-star input variant of
`nonempty_involutionK155_of_traceRepresentationDataAndMinus8Values`. -/
theorem nonempty_involutionK155_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndReflectionStar
    h data A B C minus8Values rotation_fixed hStar)
      |>.nonempty_involutionK155_raw_reflection k

/-- Fixed-star input variant of
`reflectionFixedCenterLeafBoundary_of_traceRepresentationDataAndMinus8Values`.
-/
theorem reflectionFixedCenterLeafBoundary_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndReflectionStar
    h data A B C minus8Values rotation_fixed hStar)
      |>.reflectionFixedCenterLeafBoundary

/-- Fixed-star input variant of
`representationCharacterComponentsBoundary_of_traceRepresentationDataAndMinus8Values`.
-/
theorem representationCharacterComponentsBoundary_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndReflectionStar
    h data A B C minus8Values rotation_fixed hStar)
      |>.representationCharacterComponentsBoundary

/-- Fixed-star input variant of
`no_currentFinalGapBoundary_of_traceRepresentationDataAndMinus8Values`. -/
theorem no_currentFinalGapBoundary_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndReflectionStar
    h data A B C minus8Values rotation_fixed hStar)
      |>.no_currentFinalGapBoundary

end D19ActsOnMoore57

end

end Moore57

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

/-!
# Trace-representation plus minus-8 trace boundary consequences

This file keeps the `(-8)` side on the concrete projection representation API:
explicit complementary projection trace values are first lowered to
`D19CharacterValueBoundary h.minus8ProjectionRepresentation`, then combined
with the existing `TraceRepresentationData h.a1` bridge into the packaged
E7/minus-8 reflection-count boundary.
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
`TraceRepresentationData h.a1` surface, explicit complementary minus-8
projection trace values, and the standard count inputs at `sr 0`. -/
def ofTraceRepresentationDataAndMinus8ProjectionTraceBoundary
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationData h data A B C
    (D19CharacterValueBoundary.ofMinus8ProjectionTraceBoundary h A B C
      minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace)
    rotation_fixed reflection_fixed_count reflection_adjacent_moved

/-- Fixed-star variant of
`ofTraceRepresentationDataAndMinus8ProjectionTraceBoundary`: the `sr 0`
fixed-star witness supplies the two reflection count inputs. -/
def ofTraceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationDataAndMinus8ProjectionTraceBoundary h data A B C
    minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
    rotation_fixed hStar.fixedVertexCount_eq_56
    (hStar.adjacentMovedCount_eq_112 h.isMoore)

end E7Minus8CharacterReflectionCountBoundary

end D19ActsOnMoore57

end

end Moore57

/-!
# No-go connectors from trace-representation data and explicit minus-8 traces

This file exposes the direct consumer surface for the concrete
`TraceRepresentationData h.a1` plus explicit complementary `(-8)` projection
trace boundary route.  The proofs only build the packaged
`E7Minus8CharacterReflectionCountBoundary` and reuse its standard downstream
consequences.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Explicit trace-representation E7 data plus complementary minus-8
projection trace values and the standard count inputs give a nonempty
linear-character input. -/
theorem nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundary
      h data A B C
      minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
      rotation_fixed reflection_fixed_count reflection_adjacent_moved)
        |>.nonempty_d19LinearCharacterInput

/-- The explicit trace-boundary route gives the paper-shaped fixed-star
boundary for any reflection. -/
theorem involutionFixedSetStar56_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundary
      h data A B C
      minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
      rotation_fixed reflection_fixed_count reflection_adjacent_moved)
        |>.involutionFixedSetStar56_raw_reflection k

/-- The explicit trace-boundary route gives a nonempty `K_{1,55}` witness for
any reflection. -/
theorem nonempty_involutionK155_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundary
      h data A B C
      minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
      rotation_fixed reflection_fixed_count reflection_adjacent_moved)
        |>.nonempty_involutionK155_raw_reflection k

/-- The explicit trace-boundary route gives the fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundary
      h data A B C
      minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
      rotation_fixed reflection_fixed_count reflection_adjacent_moved)
        |>.reflectionFixedCenterLeafBoundary

/-- The explicit trace-boundary route gives the representation character
component boundary. -/
theorem representationCharacterComponentsBoundary_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundary
      h data A B C
      minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
      rotation_fixed reflection_fixed_count reflection_adjacent_moved)
        |>.representationCharacterComponentsBoundary

/-- The explicit trace-boundary route rules out the current final-gap
boundary. -/
theorem no_currentFinalGapBoundary_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundary
      h data A B C
      minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace
      rotation_fixed reflection_fixed_count reflection_adjacent_moved)
        |>.no_currentFinalGapBoundary

/-- Fixed-star input variant of
`nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary`.
-/
theorem nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
      h data A B C minus8_one_trace minus8_rotation_trace
      minus8_reflection_zero_trace rotation_fixed hStar)
        |>.nonempty_d19LinearCharacterInput

/-- Fixed-star input variant of
`involutionFixedSetStar56_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary`.
-/
theorem involutionFixedSetStar56_of_traceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
      h data A B C minus8_one_trace minus8_rotation_trace
      minus8_reflection_zero_trace rotation_fixed hStar)
        |>.involutionFixedSetStar56_raw_reflection k

/-- Fixed-star input variant of
`nonempty_involutionK155_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary`.
-/
theorem nonempty_involutionK155_of_traceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
      h data A B C minus8_one_trace minus8_rotation_trace
      minus8_reflection_zero_trace rotation_fixed hStar)
        |>.nonempty_involutionK155_raw_reflection k

/-- Fixed-star input variant of
`reflectionFixedCenterLeafBoundary_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary`.
-/
theorem reflectionFixedCenterLeafBoundary_of_traceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
      h data A B C minus8_one_trace minus8_rotation_trace
      minus8_reflection_zero_trace rotation_fixed hStar)
        |>.reflectionFixedCenterLeafBoundary

/-- Fixed-star input variant of
`representationCharacterComponentsBoundary_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary`.
-/
theorem representationCharacterComponentsBoundary_of_traceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
      h data A B C minus8_one_trace minus8_rotation_trace
      minus8_reflection_zero_trace rotation_fixed hStar)
        |>.representationCharacterComponentsBoundary

/-- Fixed-star input variant of
`no_currentFinalGapBoundary_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary`.
-/
theorem no_currentFinalGapBoundary_of_traceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
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
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
      h data A B C minus8_one_trace minus8_rotation_trace
      minus8_reflection_zero_trace rotation_fixed hStar)
        |>.no_currentFinalGapBoundary

end D19ActsOnMoore57

end

end Moore57

/-!
# No-go connectors from trace-representation data and complementary minus-8 values

This file exposes the direct consumer surface for `TraceRepresentationData h.a1`
when the `(-8)` character values are supplied by the complementary projection
formula.  The proofs only build
`E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement`
and reuse the standard downstream package methods.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Complementary trace-representation data and the standard count inputs give
the paper-shaped fixed-star boundary for any reflection. -/
theorem involutionFixedSetStar56_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.involutionFixedSetStar56_raw_reflection k

/-- Complementary trace-representation data and the standard count inputs give
a `K_{1,55}` witness for any reflection. -/
theorem nonempty_involutionK155_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.nonempty_involutionK155_raw_reflection k

/-- Complementary trace-representation data and the standard count inputs give
the fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.reflectionFixedCenterLeafBoundary

/-- Complementary trace-representation data and the standard count inputs give
the representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.representationCharacterComponentsBoundary

/-- Complementary trace-representation data and the standard count inputs rule
out the current branch-orbit final gap. -/
theorem no_currentFinalGapBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_currentFinalGapBoundary

/-- Complementary trace-representation data rules out the action-level final
boundary. -/
theorem no_actionLevelFinalBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelFinalBoundary

/-- Complementary trace-representation data rules out the action-level local
obstruction boundary. -/
theorem no_actionLevelLocalObstructionBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelLocalObstructionBoundary

/-- Complementary trace-representation data rules out the action-level
reduced-coordinate witness boundary. -/
theorem no_actionLevelReducedCoordinateWitnessBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelReducedCoordinateWitnessBoundary

/-- Complementary trace-representation data rules out the action-level
set-invariant witness boundary. -/
theorem no_actionLevelSetInvariantWitnessBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelSetInvariantWitnessBoundary

/-- Complementary trace-representation data rules out the common-neighbor
reduced action-level boundary. -/
theorem no_actionLevelCommonNeighborReducedBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelCommonNeighborReducedBoundary

/-- Complementary trace-representation data rules out the minimal-remaining
action-level boundary. -/
theorem no_actionLevelMinimalRemainingBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingBoundary

/-- Complementary trace-representation data rules out the refined
minimal-remaining action-level boundary. -/
theorem no_actionLevelMinimalRemainingRefinedBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingRefinedBoundary

/-- Complementary trace-representation data rules out the matching-equation
refined minimal-remaining action-level boundary. -/
theorem no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_traceRepresentationDataComplement
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
    h data rotation_fixed reflection_fixed_count reflection_adjacent_moved)
      |>.no_actionLevelMinimalRemainingRefinedMatchingBoundary

end D19ActsOnMoore57

end

end Moore57

/-!
# Complementary trace-representation route from reflection fixed count only

The complementary `TraceRepresentationData` route previously accepted both the
standard reflection fixed count `56` and the adjacent-moved count `112`.  The
fixed count gives the paper-shaped fixed-star statement for `sr 0`, and that
statement supplies the adjacent-moved count consumed by the existing package.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the packaged E7/minus-8 boundary from complementary
`TraceRepresentationData h.a1` and only the fixed count `56` for the standard
reflection representative. -/
def ofTraceRepresentationDataComplementAndReflectionFixedCount
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    E7Minus8CharacterReflectionCountBoundary h :=
  let hStar :=
    h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56
      0 reflection_fixed_count
  ofTraceRepresentationDataComplement h data rotation_fixed reflection_fixed_count
    (hStar.adjacentMovedCount_eq_112 h.isMoore)

end E7Minus8CharacterReflectionCountBoundary

/-- Complementary trace-representation data plus the standard reflection fixed
count gives a nonempty linear-character input. -/
theorem nonempty_d19LinearCharacterInput_of_traceRepresentationDataComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    Nonempty (D19LinearCharacterInput h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplementAndReflectionFixedCount
    h data rotation_fixed reflection_fixed_count)
      |>.nonempty_d19LinearCharacterInput

/-- The fixed-count-only complementary trace-representation route gives the
paper-shaped fixed-star boundary for any reflection. -/
theorem involutionFixedSetStar56_of_traceRepresentationDataComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplementAndReflectionFixedCount
    h data rotation_fixed reflection_fixed_count)
      |>.involutionFixedSetStar56_raw_reflection k

/-- The fixed-count-only complementary trace-representation route gives a
`K_{1,55}` witness for any reflection. -/
theorem nonempty_involutionK155_of_traceRepresentationDataComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplementAndReflectionFixedCount
    h data rotation_fixed reflection_fixed_count)
      |>.nonempty_involutionK155_raw_reflection k

/-- The fixed-count-only complementary trace-representation route gives the
fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary_of_traceRepresentationDataComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ReflectionFixedCenterLeafBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplementAndReflectionFixedCount
    h data rotation_fixed reflection_fixed_count)
      |>.reflectionFixedCenterLeafBoundary

/-- The fixed-count-only complementary trace-representation route gives the
representation character component boundary. -/
theorem representationCharacterComponentsBoundary_of_traceRepresentationDataComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    RepresentationCharacterComponentsBoundary h :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplementAndReflectionFixedCount
    h data rotation_fixed reflection_fixed_count)
      |>.representationCharacterComponentsBoundary

/-- The fixed-count-only complementary trace-representation route rules out the
current final-gap boundary. -/
theorem no_currentFinalGapBoundary_of_traceRepresentationDataComplementAndReflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    (data : TraceRepresentationData h.a1)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  (E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplementAndReflectionFixedCount
    h data rotation_fixed reflection_fixed_count)
      |>.no_currentFinalGapBoundary

end D19ActsOnMoore57

end

end Moore57

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

