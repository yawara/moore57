import Moore57.BranchOrbitABCFixedStarCoordinateWitnessBoundary
import Moore57.BranchOrbitABCFixedStarFinalBridge
import Moore57.D19FinalInputs
import Moore57.D19RepresentationCharacterDataBridge

/-!
# Fixed-star boundary no-go connectors

This file only exposes delegation wrappers from existing character-component
inputs to the fixed-star boundary no-go theorems.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

private theorem representationComponents_of_finalCharacterInputs
    {h : D19ActsOnMoore57 V Γ}
    (character : D19FinalCharacterInputs h) :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h :=
  character.representation.representationCharacterComponentsBoundary

/-- Component-boundary form of the fixed-star reference-matching cardinality
pipeline no-go. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling := by
  intro boundary
  exact no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary h
    ⟨representationComponents, boundary⟩

/-- Final-character-input form of the fixed-star reference-matching
cardinality pipeline no-go. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_components h
    (representationComponents_of_finalCharacterInputs character)

/-- Component-boundary form of the fixed-star local-obstruction no-go. -/
theorem no_D19_fixedStarLocalObstructionBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling := by
  intro boundary
  exact no_D19_fixedStarLocalObstructionBoundary h
    ⟨representationComponents, boundary⟩

/-- Final-character-input form of the fixed-star local-obstruction no-go. -/
theorem no_D19_fixedStarLocalObstructionBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_components h
    (representationComponents_of_finalCharacterInputs character)

/-- Component-boundary form of the fixed-star witness no-go. -/
theorem no_D19_fixedStarWitnessBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling := by
  intro boundary
  exact no_D19_fixedStarWitnessBoundary h
    ⟨representationComponents, boundary⟩

/-- Final-character-input form of the fixed-star witness no-go. -/
theorem no_D19_fixedStarWitnessBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_components h
    (representationComponents_of_finalCharacterInputs character)

/-- Component-boundary form of the fixed-star coordinate-witness no-go. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary_of_components
    (h : D19ActsOnMoore57 V Γ)
    (representationComponents :
      D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling := by
  intro boundary
  exact no_D19_fixedStarCoordinateWitnessBoundary h
    ⟨representationComponents, boundary⟩

/-- Final-character-input form of the fixed-star coordinate-witness no-go. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary_of_finalCharacterInputs
    (h : D19ActsOnMoore57 V Γ)
    (character : D19FinalCharacterInputs h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_components h
    (representationComponents_of_finalCharacterInputs character)

end

end Moore57
