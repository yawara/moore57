import Moore57.D19OnMoore57.Reflection.ReflectionTraceCandidateLowerBoundBridge
import Moore57.D19OnMoore57.NoGo.D19PaperFixedStarNoGoConnectors
import Moore57.D19OnMoore57.E7Projection.E7Minus8PaperFixedStarNoGoConnectors

/-!
# Lower-bound reflection no-go connectors

This file exposes thin no-go wrappers from the trace-refined lower-bound
package `ReflectionFixedCountLower47`, and from an exact reflection fixed count
`56`, to the existing paper-shaped fixed-star no-go connectors.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Exact reflection fixed count `56` supplies the paper-shaped fixed-star
witness consumed by the final no-go connectors. -/
theorem involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56_connector
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19)
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56 k hcount

/-- Exact reflection fixed count `56` supplies a Prop-level `K_{1,55}`
witness. -/
theorem nonempty_involutionK155_of_reflection_fixedVertexCount_eq_56_connector
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19)
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56_connector
    h k hcount).nonempty_involutionK155

namespace D19ActsOnMoore57.ReflectionFixedCountLower47

variable {h : D19ActsOnMoore57 V Γ}

/-- The lower-bound package supplies a Prop-level `K_{1,55}` witness for each
reflection. -/
theorem nonempty_involutionK155
    (bounds : ReflectionFixedCountLower47 h) (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (bounds.involutionFixedSetStar56 k).nonempty_involutionK155

end D19ActsOnMoore57.ReflectionFixedCountLower47

/-- Eigenspace-character no-go with exact reflection fixed count `56` and
automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndReflectionFixedCount56_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56) :
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndPaperFixedStar56_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56_connector
      h dt hcount)

/-- Eigenspace-character no-go with the uniform reflection lower bound `47`
and automatic rotation counts. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndReflectionFixedCountLower47_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    (bounds : D19ActsOnMoore57.ReflectionFixedCountLower47 h)
    (dt : ZMod 19) :
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_eigenspaceCharactersAndPaperFixedStar56_autoRotation
    h alpha beta gamma A B C h7 hMinus8 (bounds.involutionFixedSetStar56 dt)

/-- Eigenspace-character no-go for the explicit per-reflection `K_{1,55}`
wrapper, with exact reflection fixed count `56`. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndReflectionFixedCount56_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndPaperFixedStar56_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56_connector
      h dt hcount)

/-- Eigenspace-character no-go for the explicit per-reflection `K_{1,55}`
wrapper, with the uniform reflection lower bound `47`. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndReflectionFixedCountLower47_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    (bounds : D19ActsOnMoore57.ReflectionFixedCountLower47 h)
    (dt : ZMod 19) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) :=
  no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_eigenspaceCharactersAndPaperFixedStar56_autoRotation
    h alpha beta gamma A B C h7 hMinus8 (bounds.involutionFixedSetStar56 dt)

/-- Current final-gap no-go with exact reflection fixed count `56`. -/
theorem no_D19_currentFinalGapBoundary_of_eigenspaceCharactersAndReflectionFixedCount56_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_D19_currentFinalGapBoundary_of_eigenspaceCharactersAndPaperFixedStar56_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56_connector
      h dt hcount)

/-- Current final-gap no-go with the uniform reflection lower bound `47`. -/
theorem no_D19_currentFinalGapBoundary_of_eigenspaceCharactersAndReflectionFixedCountLower47_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    (bounds : D19ActsOnMoore57.ReflectionFixedCountLower47 h)
    (dt : ZMod 19) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_D19_currentFinalGapBoundary_of_eigenspaceCharactersAndPaperFixedStar56_autoRotation
    h alpha beta gamma A B C h7 hMinus8 (bounds.involutionFixedSetStar56 dt)

/-- Endpoint-obstruction final-boundary no-go with exact reflection fixed
count `56`. -/
theorem no_D19_endpointObstructionFinalBoundary_of_eigenspaceCharactersAndReflectionFixedCount56_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    {dt : ZMod 19}
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56) :
    ¬ Nonempty (BranchOrbitABCEndpointObstructionFinalBoundary h) :=
  no_D19_endpointObstructionFinalBoundary_of_eigenspaceCharactersAndPaperFixedStar56_autoRotation
    h alpha beta gamma A B C h7 hMinus8
    (involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56_connector
      h dt hcount)

/-- Endpoint-obstruction final-boundary no-go with the uniform reflection lower
bound `47`. -/
theorem no_D19_endpointObstructionFinalBoundary_of_eigenspaceCharactersAndReflectionFixedCountLower47_autoRotation
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    (hMinus8 : ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ))
    (bounds : D19ActsOnMoore57.ReflectionFixedCountLower47 h)
    (dt : ZMod 19) :
    ¬ Nonempty (BranchOrbitABCEndpointObstructionFinalBoundary h) :=
  no_D19_endpointObstructionFinalBoundary_of_eigenspaceCharactersAndPaperFixedStar56_autoRotation
    h alpha beta gamma A B C h7 hMinus8 (bounds.involutionFixedSetStar56 dt)

/-- Fixed-star reference-matching no-go from concrete projection character
boundaries and exact reflection fixed count `56`. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndReflectionFixedCount56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C e7Class minus8Values
    (involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56_connector
      h dt hcount)

/-- Fixed-star reference-matching no-go from concrete projection character
boundaries and the uniform reflection lower bound `47`. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndReflectionFixedCountLower47
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (bounds : D19ActsOnMoore57.ReflectionFixedCountLower47 h)
    (dt : ZMod 19) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C e7Class minus8Values
    (bounds.involutionFixedSetStar56 dt)

/-- Fixed-star local-obstruction no-go from concrete projection character
boundaries and exact reflection fixed count `56`. -/
theorem no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8CharacterBoundariesAndReflectionFixedCount56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C e7Class minus8Values
    (involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56_connector
      h dt hcount)

/-- Fixed-star local-obstruction no-go from concrete projection character
boundaries and the uniform reflection lower bound `47`. -/
theorem no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8CharacterBoundariesAndReflectionFixedCountLower47
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (bounds : D19ActsOnMoore57.ReflectionFixedCountLower47 h)
    (dt : ZMod 19) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C e7Class minus8Values
    (bounds.involutionFixedSetStar56 dt)

/-- Fixed-star witness no-go from concrete projection character boundaries and
exact reflection fixed count `56`. -/
theorem no_D19_fixedStarWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndReflectionFixedCount56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C e7Class minus8Values
    (involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56_connector
      h dt hcount)

/-- Fixed-star witness no-go from concrete projection character boundaries and
the uniform reflection lower bound `47`. -/
theorem no_D19_fixedStarWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndReflectionFixedCountLower47
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (bounds : D19ActsOnMoore57.ReflectionFixedCountLower47 h)
    (dt : ZMod 19) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C e7Class minus8Values
    (bounds.involutionFixedSetStar56 dt)

/-- Fixed-star coordinate-witness no-go from concrete projection character
boundaries and exact reflection fixed count `56`. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndReflectionFixedCount56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C e7Class minus8Values
    (involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56_connector
      h dt hcount)

/-- Fixed-star coordinate-witness no-go from concrete projection character
boundaries and the uniform reflection lower bound `47`. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndReflectionFixedCountLower47
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (bounds : D19ActsOnMoore57.ReflectionFixedCountLower47 h)
    (dt : ZMod 19) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C e7Class minus8Values
    (bounds.involutionFixedSetStar56 dt)

/-- Lean-aware fixed-star final no-go from concrete projection character
boundaries and exact reflection fixed count `56`. -/
theorem no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndReflectionFixedCount56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
            star labeling :=
  no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C e7Class minus8Values
    (involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56_connector
      h dt hcount)

/-- Lean-aware fixed-star final no-go from concrete projection character
boundaries and the uniform reflection lower bound `47`. -/
theorem no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndReflectionFixedCountLower47
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (bounds : D19ActsOnMoore57.ReflectionFixedCountLower47 h)
    (dt : ZMod 19) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
            star labeling :=
  no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C e7Class minus8Values
    (bounds.involutionFixedSetStar56 dt)

end

end Moore57
