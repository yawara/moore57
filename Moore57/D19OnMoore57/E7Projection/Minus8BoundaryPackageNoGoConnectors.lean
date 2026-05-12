import Moore57.D19OnMoore57.E7Projection.Minus8CharacterBoundaryPackages
import Moore57.D19OnMoore57.E7Projection.Minus8InversePairTraceBoundaryPackages

/-!
# No-go connectors for packaged E7/minus-8 boundaries

This file exposes fixed-star no-go frontiers directly from the Type-valued
projection-character boundary packages.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace E7Minus8CharacterReflectionCountBoundary

/-- Reference-matching no-go from the packaged direct character boundary. -/
theorem no_fixedStarReferenceMatchingCardinalityPipeline
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

/-- Local-obstruction no-go from the packaged direct character boundary. -/
theorem no_fixedStarLocalObstruction
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

/-- Witness-boundary no-go from the packaged direct character boundary. -/
theorem no_fixedStarWitness
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

/-- Coordinate-witness no-go from the packaged direct character boundary. -/
theorem no_fixedStarCoordinateWitness
    (boundary : E7Minus8CharacterReflectionCountBoundary h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

end E7Minus8CharacterReflectionCountBoundary

namespace E7Minus8InversePairTraceReflectionCountBoundary

/-- Reference-matching no-go from the packaged inverse-pair trace boundary. -/
theorem no_fixedStarReferenceMatchingCardinalityPipeline
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

/-- Local-obstruction no-go from the packaged inverse-pair trace boundary. -/
theorem no_fixedStarLocalObstruction
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

/-- Witness-boundary no-go from the packaged inverse-pair trace boundary. -/
theorem no_fixedStarWitness
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

/-- Coordinate-witness no-go from the packaged inverse-pair trace boundary. -/
theorem no_fixedStarCoordinateWitness
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_nonempty_linearCharacterInput
    h boundary.nonempty_d19LinearCharacterInput

end E7Minus8InversePairTraceReflectionCountBoundary

end D19ActsOnMoore57

end

end Moore57
