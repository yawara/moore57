import Moore57.E7Minus8CharacterInputBridge
import Moore57.D19FixedStarBoundaryNoGoConnectors
import Moore57.BranchOrbitABCLeanAwareFinalBoundary

/-!
# Concrete E7/minus-8 K155 no-go connectors

This file exposes the current mathlib-facing representation boundary in the
fixed-star no-go surfaces.  The linear algebra is not reproved here: the
concrete `E7` and `(-8)` projection representations are lowered through their
existing `Representation.character` trace bridges, then the existing
`K_{1,55}` eigenspace connector supplies the component boundary consumed by
the branch-orbit contradictions.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace D19LinearCharacterInput

/-- Build the full linear-character input from the concrete `E7` and `(-8)`
projection character boundaries plus an explicit `K_{1,55}` reflection fixed
star. -/
noncomputable def ofE7AndMinus8CharacterBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    D19LinearCharacterInput h :=
  ofEigenspaceCharactersAndInvolutionK155 (h := h)
    alpha beta gamma A B C
    (h.e7_trace_eq_d19Linear_of_characterClassBoundary
      alpha beta gamma e7Class)
    (h.minus8_trace_eq_d19Linear_of_characterValueBoundary
      A B C minus8Values)
    hK

end D19LinearCharacterInput

/-- Component-boundary form of
`D19LinearCharacterInput.ofE7AndMinus8CharacterBoundariesAndInvolutionK155`. -/
theorem representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofE7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C e7Class minus8Values hK)
      |>.representationCharacterComponentsBoundary

end D19ActsOnMoore57

/-- Fixed-star reference-matching no-go from concrete projection character
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
        h alpha beta gamma A B C e7Class minus8Values hK)

/-- Fixed-star local-obstruction no-go from concrete projection character
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
        h alpha beta gamma A B C e7Class minus8Values hK)

/-- Fixed-star witness no-go from concrete projection character boundaries and
an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
        h alpha beta gamma A B C e7Class minus8Values hK)

/-- Fixed-star coordinate-witness no-go from concrete projection character
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_components h
    (D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
        h alpha beta gamma A B C e7Class minus8Values hK)

/-- Lean-aware fixed-star final no-go from concrete projection character
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
            star labeling := by
  intro hlean
  rcases hlean with ⟨star, labeling, boundary⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
        h alpha beta gamma A B C e7Class minus8Values hK,
      star, labeling, boundary⟩

end

end Moore57
