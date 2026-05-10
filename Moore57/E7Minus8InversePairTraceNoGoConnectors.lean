import Moore57.E7Minus8InversePairTraceBoundaryBridge
import Moore57.E7Minus8PaperFixedStarNoGoConnectors
import Moore57.E7Minus8K155NoGoConnectors

/-!
# Inverse-pair trace no-go connectors for E7 and minus-8

This file is a thin wrapper layer from inverse-pair projection trace data to
the existing fixed-star no-go surfaces.  The trace data is first expanded to
the concrete character-boundary API; no linear algebra or representation theory
is reproved here.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Fixed-star reference-matching no-go from inverse-pair projection trace
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar

/-- Fixed-star local-obstruction no-go from inverse-pair projection trace
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar

/-- Fixed-star witness no-go from inverse-pair projection trace boundaries and
an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarWitnessBoundary_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar

/-- Fixed-star coordinate-witness no-go from inverse-pair projection trace
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar

/-- Lean-aware fixed-star final no-go from inverse-pair projection trace
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
            star labeling :=
  no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar

/-- Fixed-star reference-matching no-go from inverse-pair projection trace
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK

/-- Fixed-star local-obstruction no-go from inverse-pair projection trace
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK

/-- Fixed-star witness no-go from inverse-pair projection trace boundaries and
an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarWitnessBoundary_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK

/-- Fixed-star coordinate-witness no-go from inverse-pair projection trace
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK

/-- Lean-aware fixed-star final no-go from inverse-pair projection trace
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
            star labeling :=
  no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK

end

end Moore57
