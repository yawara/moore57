import Moore57.D19OnMoore57.Reflection.ReflectionLinearCharacterNonemptyBridge
import Moore57.D19OnMoore57.NoGo.D19FixedStarBoundaryNoGoConnectors
import Moore57.D19OnMoore57.NoGo.D19CurrentGapBoundaryNoGoConnectors

/-!
# No-go connectors from nonempty linear-character input

This file routes `Nonempty (D19LinearCharacterInput h)` into the component
boundary consumed by the existing branch-orbit no-go frontiers.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- A nonempty linear-character input supplies the representation component
boundary consumed by the no-go frontiers. -/
theorem representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
    (hin : Nonempty (D19LinearCharacterInput h)) :
    RepresentationCharacterComponentsBoundary h := by
  rcases hin with ⟨hin⟩
  exact hin.toD19RepresentationCharacterInput.representationCharacterComponentsBoundary

end D19ActsOnMoore57

/-- Fixed-star reference-matching no-go from a nonempty linear-character
input. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Fixed-star local-obstruction no-go from a nonempty linear-character input. -/
theorem no_D19_fixedStarLocalObstructionBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Fixed-star witness no-go from a nonempty linear-character input. -/
theorem no_D19_fixedStarWitnessBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Fixed-star coordinate-witness no-go from a nonempty linear-character
input. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Current final gap no-go from a nonempty linear-character input. -/
theorem no_D19_currentFinalGapBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_D19_currentFinalGapBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

end

end Moore57
