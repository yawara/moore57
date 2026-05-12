import Moore57.D19OnMoore57.E7Projection.Minus8TraceBoundaryBridge
import Moore57.D19OnMoore57.E7Projection.Minus8PaperFixedStarNoGoConnectors
import Moore57.D19OnMoore57.E7Projection.Minus8K155NoGoConnectors

/-!
# Trace-boundary E7/minus-8 no-go connectors

This file is a thin wrapper layer from concrete projection trace data to the
existing E7/minus-8 fixed-star no-go surfaces.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Fixed-star reference-matching no-go from concrete projection trace
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8TraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7_dimension : alpha + beta + 18 * gamma = 1729)
    (e7_rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (e7_reflection_zero_trace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (alpha : ℚ) - (beta : ℚ))
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
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    (D19CharacterClassBoundary.ofE7ProjectionTraceBoundary h
      alpha beta gamma e7_dimension e7_rotation_trace e7_reflection_zero_trace)
    (D19CharacterValueBoundary.ofMinus8ProjectionTraceBoundary h
      A B C minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace)
    hStar

/-- Fixed-star local-obstruction no-go from concrete projection trace
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8TraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7_dimension : alpha + beta + 18 * gamma = 1729)
    (e7_rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (e7_reflection_zero_trace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (alpha : ℚ) - (beta : ℚ))
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
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    (D19CharacterClassBoundary.ofE7ProjectionTraceBoundary h
      alpha beta gamma e7_dimension e7_rotation_trace e7_reflection_zero_trace)
    (D19CharacterValueBoundary.ofMinus8ProjectionTraceBoundary h
      A B C minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace)
    hStar

/-- Fixed-star witness no-go from concrete projection trace boundaries and an
explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarWitnessBoundary_of_E7AndMinus8TraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7_dimension : alpha + beta + 18 * gamma = 1729)
    (e7_rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (e7_reflection_zero_trace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (alpha : ℚ) - (beta : ℚ))
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
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    (D19CharacterClassBoundary.ofE7ProjectionTraceBoundary h
      alpha beta gamma e7_dimension e7_rotation_trace e7_reflection_zero_trace)
    (D19CharacterValueBoundary.ofMinus8ProjectionTraceBoundary h
      A B C minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace)
    hStar

/-- Fixed-star coordinate-witness no-go from concrete projection trace
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8TraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7_dimension : alpha + beta + 18 * gamma = 1729)
    (e7_rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (e7_reflection_zero_trace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (alpha : ℚ) - (beta : ℚ))
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
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    (D19CharacterClassBoundary.ofE7ProjectionTraceBoundary h
      alpha beta gamma e7_dimension e7_rotation_trace e7_reflection_zero_trace)
    (D19CharacterValueBoundary.ofMinus8ProjectionTraceBoundary h
      A B C minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace)
    hStar

/-- Lean-aware fixed-star final no-go from concrete projection trace
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8TraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7_dimension : alpha + beta + 18 * gamma = 1729)
    (e7_rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (e7_reflection_zero_trace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (alpha : ℚ) - (beta : ℚ))
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
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
            star labeling :=
  no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    (D19CharacterClassBoundary.ofE7ProjectionTraceBoundary h
      alpha beta gamma e7_dimension e7_rotation_trace e7_reflection_zero_trace)
    (D19CharacterValueBoundary.ofMinus8ProjectionTraceBoundary h
      A B C minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace)
    hStar

/-- Fixed-star reference-matching no-go from concrete projection trace
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8TraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7_dimension : alpha + beta + 18 * gamma = 1729)
    (e7_rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (e7_reflection_zero_trace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (alpha : ℚ) - (beta : ℚ))
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
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    (D19CharacterClassBoundary.ofE7ProjectionTraceBoundary h
      alpha beta gamma e7_dimension e7_rotation_trace e7_reflection_zero_trace)
    (D19CharacterValueBoundary.ofMinus8ProjectionTraceBoundary h
      A B C minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace)
    hK

/-- Fixed-star local-obstruction no-go from concrete projection trace
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8TraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7_dimension : alpha + beta + 18 * gamma = 1729)
    (e7_rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (e7_reflection_zero_trace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (alpha : ℚ) - (beta : ℚ))
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
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    (D19CharacterClassBoundary.ofE7ProjectionTraceBoundary h
      alpha beta gamma e7_dimension e7_rotation_trace e7_reflection_zero_trace)
    (D19CharacterValueBoundary.ofMinus8ProjectionTraceBoundary h
      A B C minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace)
    hK

/-- Fixed-star witness no-go from concrete projection trace boundaries and an
explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarWitnessBoundary_of_E7AndMinus8TraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7_dimension : alpha + beta + 18 * gamma = 1729)
    (e7_rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (e7_reflection_zero_trace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (alpha : ℚ) - (beta : ℚ))
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
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    (D19CharacterClassBoundary.ofE7ProjectionTraceBoundary h
      alpha beta gamma e7_dimension e7_rotation_trace e7_reflection_zero_trace)
    (D19CharacterValueBoundary.ofMinus8ProjectionTraceBoundary h
      A B C minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace)
    hK

/-- Fixed-star coordinate-witness no-go from concrete projection trace
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8TraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7_dimension : alpha + beta + 18 * gamma = 1729)
    (e7_rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (e7_reflection_zero_trace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (alpha : ℚ) - (beta : ℚ))
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
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    (D19CharacterClassBoundary.ofE7ProjectionTraceBoundary h
      alpha beta gamma e7_dimension e7_rotation_trace e7_reflection_zero_trace)
    (D19CharacterValueBoundary.ofMinus8ProjectionTraceBoundary h
      A B C minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace)
    hK

/-- Lean-aware fixed-star final no-go from concrete projection trace
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8TraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7_dimension : alpha + beta + 18 * gamma = 1729)
    (e7_rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (e7_reflection_zero_trace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (alpha : ℚ) - (beta : ℚ))
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
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
            star labeling :=
  no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    (D19CharacterClassBoundary.ofE7ProjectionTraceBoundary h
      alpha beta gamma e7_dimension e7_rotation_trace e7_reflection_zero_trace)
    (D19CharacterValueBoundary.ofMinus8ProjectionTraceBoundary h
      A B C minus8_one_trace minus8_rotation_trace minus8_reflection_zero_trace)
    hK

end

end Moore57
