import Moore57.D19OnMoore57.Reflection.LinearCharacterNonemptyBridge
import Moore57.D19OnMoore57.NoGo.FixedStarBoundaryNoGoConnectors
import Moore57.D19OnMoore57.NoGo.CurrentGapBoundaryNoGoConnectors
import Moore57.D19OnMoore57.NoGo.ActionLevelBoundaryNoGoConnectors

/-!
# No-go connectors from nonempty linear-character input

A `Nonempty (D19LinearCharacterInput h)` produces the representation
component boundary that the existing branch-orbit no-go frontiers consume.
This file packages, in three groups:

1. The base bridge: nonempty input → `RepresentationCharacterComponentsBoundary`.
2. Fixed-star variant no-gos (reference-matching, local-obstruction,
   witness, coordinate-witness) and the current-final-gap no-go.
3. Current-gap-style no-gos (common-neighbor-reduced, minimal-remaining and
   its refinements).
4. Action-level no-gos (case, witness, coordinate-witness, final,
   local-obstruction, doubling-equation/support, set-invariant-witness,
   reduced-coordinate-witness).
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

/-! ### Fixed-star variant no-gos -/

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

/-! ### Current-gap-style no-gos -/

/-- Common-neighbor reduced no-go from a nonempty linear-character input. -/
theorem no_D19_actionLevelCommonNeighborReducedBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :=
  no_D19_actionLevelCommonNeighborReducedBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Minimal remaining no-go from a nonempty linear-character input. -/
theorem no_D19_actionLevelMinimalRemainingBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingBoundary h) :=
  no_D19_actionLevelMinimalRemainingBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Refined minimal remaining no-go from a nonempty linear-character input. -/
theorem no_D19_actionLevelMinimalRemainingRefinedBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty
        (BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Matching-equation refined minimal remaining no-go from a nonempty
linear-character input. -/
theorem no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty
        (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-! ### Action-level no-gos -/

/-- Action-level case no-go from a nonempty linear-character input. -/
theorem no_D19_actionLevelCaseBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelCaseBoundary h) :=
  no_D19_actionLevelCaseBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level witness no-go from a nonempty linear-character input. -/
theorem no_D19_actionLevelWitnessBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelWitnessBoundary h) :=
  no_D19_actionLevelWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level coordinate-witness no-go from a nonempty linear-character
input. -/
theorem no_D19_actionLevelCoordinateWitnessBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelCoordinateWitnessBoundary h) :=
  no_D19_actionLevelCoordinateWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level final no-go from a nonempty linear-character input. -/
theorem no_D19_actionLevelFinalBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  no_D19_actionLevelFinalBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level local-obstruction no-go from a nonempty linear-character
input. -/
theorem no_D19_actionLevelLocalObstructionBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) :=
  no_D19_actionLevelLocalObstructionBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level doubling-equation/support no-go from a nonempty
linear-character input. -/
theorem no_D19_actionLevelDoublingEquationSupportBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :=
  no_D19_actionLevelDoublingEquationSupportBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level set-invariant witness no-go from a nonempty linear-character
input. -/
theorem no_D19_actionLevelSetInvariantWitnessBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :=
  no_D19_actionLevelSetInvariantWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

/-- Action-level reduced-coordinate witness no-go from a nonempty
linear-character input. -/
theorem no_D19_actionLevelReducedCoordinateWitnessBoundary_of_nonempty_linearCharacterInput
    (h : D19ActsOnMoore57 V Γ)
    (hin : Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h)) :
    ¬ Nonempty (BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :=
  no_D19_actionLevelReducedCoordinateWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
      hin)

end

end Moore57
