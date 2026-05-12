import Moore57.D19OnMoore57.NoGo.D19NonRepresentationFrontierAfterDefaultBase
import Moore57.D19OnMoore57.LinearCharacter.D19LinearCharacterDimensionConnectors

/-!
# Linear-character no-go for the default-base non-representation frontier

This file exposes the post-default-base frontier no-go directly from the
existing linear-character/count connectors.  It does not add representation
theory; it only delegates to
`representationCharacterComponentsBoundary_of_*AndCounts` and the component
level frontier contradiction.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Linear-character/count form of the post-default-base frontier no-go. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) := by
  intro frontier
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨D19ActsOnMoore57.representationCharacterComponentsBoundary_of_linearCharacterAndCounts
        h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
        hlin ha0 ha1,
      frontier⟩

/-- Mathlib-representation/count form of the post-default-base frontier no-go.

The representation side is consumed through the existing connector file, so
this theorem avoids the older explicit finrank and reflection-arithmetic
arguments at this frontier layer. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_representationCharacterAndCounts
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) := by
  intro frontier
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h
    ⟨D19ActsOnMoore57.representationCharacterComponentsBoundary_of_representationCharacterAndCounts
        h ρ alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
        trace_eq_character character_eq_d19Linear ha0 ha1,
      frontier⟩

/-- Linear-character/count form for the raw-action diagnostic proposition. -/
theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_linearCharacterAndCounts
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    ¬ RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_linearCharacterAndCounts
    h alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg hlin ha0 ha1

/-- Mathlib-representation/count form for the raw-action diagnostic
proposition. -/
theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_representationCharacterAndCounts
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    ¬ RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_remainingNonRepresentationFrontierAfterDefaultBase_of_representationCharacterAndCounts
    h ρ alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
    trace_eq_character character_eq_d19Linear ha0 ha1

end

end Moore57
