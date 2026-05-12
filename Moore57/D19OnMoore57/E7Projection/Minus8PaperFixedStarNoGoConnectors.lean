import Moore57.D19OnMoore57.E7Projection.Minus8PaperFixedStarConnectors
import Moore57.D19OnMoore57.NoGo.FixedStarBoundaryNoGoConnectors
import Moore57.D19OnMoore57.BranchOrbit.ABCLeanAwareFinalBoundary

/-!
# Concrete E7/minus-8 paper fixed-star no-go connectors

This file exposes the concrete `E7` and `(-8)` projection character boundaries
in the fixed-star no-go surfaces, with the reflection-side counts supplied by
an explicit paper-shaped `56`-vertex fixed-star witness.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Fixed-star reference-matching no-go from concrete projection character
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
      h alpha beta gamma A B C e7Class minus8Values hStar)

/-- Fixed-star local-obstruction no-go from concrete projection character
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
      h alpha beta gamma A B C e7Class minus8Values hStar)

/-- Fixed-star witness no-go from concrete projection character boundaries and
an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
      h alpha beta gamma A B C e7Class minus8Values hStar)

/-- Fixed-star coordinate-witness no-go from concrete projection character
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
      h alpha beta gamma A B C e7Class minus8Values hStar)

/-- Lean-aware fixed-star final no-go from concrete projection character
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
            star labeling := by
  intro hlean
  rcases hlean with ⟨star, labeling, boundary⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
        h alpha beta gamma A B C e7Class minus8Values hStar,
      star, labeling, boundary⟩

end

end Moore57
