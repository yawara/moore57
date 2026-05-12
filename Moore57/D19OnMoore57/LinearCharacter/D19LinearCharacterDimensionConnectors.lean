import Moore57.D19OnMoore57.LinearCharacter.D19LinearCharacterDimension
import Moore57.D19OnMoore57.D19Core.D19ConstructiveFinalInputs
import Moore57.D19OnMoore57.D19Core.D19RepresentationCharacterMathlibBridge

/-!
# Connectors for linear-character dimension data

This file keeps the representation-side boundary close to mathlib character
data.  A full `Representation.character` decomposition, together with the
standard reflection counts, is enough to build the existing linear-character
input; the dimension and reflection arithmetic fields are filled by
`D19LinearCharacterDimension`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace D19LinearCharacterInput

/-- Build the full linear-character input from a mathlib representation
character identity and the standard reflection counts.

Compared with `ofRepresentationCharacter`, this does not ask for a
pre-packaged `TraceMultiplicityData`: the dimension equation and the
reflection equation are derived from the full linear-character equality by
`ofLinearCharacterAndCounts`. -/
noncomputable def ofRepresentationCharacterAndCounts
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
    D19LinearCharacterInput h :=
  ofLinearCharacterAndCounts (h := h) alpha beta gamma
    minus8_trivial_nonneg minus8_sign_nonneg
    (by
      intro g
      exact (trace_eq_character g).trans (character_eq_d19Linear g))
    ha0 ha1

end D19LinearCharacterInput

namespace D19RepresentationCharacterInput

/-- Forget a raw full linear-character equality with standard reflection counts
to the representation-character input consumed by the D19 pipeline. -/
noncomputable def ofLinearCharacterAndCounts
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    D19RepresentationCharacterInput h :=
  (D19LinearCharacterInput.ofLinearCharacterAndCounts (h := h)
    alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
    hlin ha0 ha1).toD19RepresentationCharacterInput

/-- Mathlib representation-character version of
`ofLinearCharacterAndCounts`. -/
noncomputable def ofRepresentationCharacterAndCounts
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
    D19RepresentationCharacterInput h :=
  (D19LinearCharacterInput.ofRepresentationCharacterAndCounts (h := h)
    ρ alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
    trace_eq_character character_eq_d19Linear ha0 ha1).toD19RepresentationCharacterInput

end D19RepresentationCharacterInput

/-- Exposed component-boundary form of `ofLinearCharacterAndCounts`. -/
theorem representationCharacterComponentsBoundary_of_linearCharacterAndCounts
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
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofLinearCharacterAndCounts (h := h)
    alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
    hlin ha0 ha1).representationCharacterComponentsBoundary

/-- Exposed component-boundary form for mathlib representation-character data.

This removes the explicit `finrank = 1729`, dimension arithmetic, and
reflection arithmetic assumptions from the representation side when a full
D19 linear-character identity and the standard reflection counts are
available. -/
theorem representationCharacterComponentsBoundary_of_representationCharacterAndCounts
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
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofRepresentationCharacterAndCounts (h := h)
    ρ alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
    trace_eq_character character_eq_d19Linear ha0 ha1)
      |>.representationCharacterComponentsBoundary

end D19ActsOnMoore57

namespace D19FinalCharacterInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Build final character inputs from a full linear-character equality,
standard reflection counts, and a separately supplied fixed-count upper
bound. -/
noncomputable def ofLinearCharacterAndCounts
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112)
    (fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h) :
    D19FinalCharacterInputs h :=
  ofD19LinearCharacterInput
    (D19ActsOnMoore57.D19LinearCharacterInput.ofLinearCharacterAndCounts
      (h := h) alpha beta gamma minus8_trivial_nonneg
      minus8_sign_nonneg hlin ha0 ha1)
    fixedUpperBound

/-- Mathlib representation-character version of
`ofLinearCharacterAndCounts`. -/
noncomputable def ofRepresentationCharacterAndCounts
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
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112)
    (fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h) :
    D19FinalCharacterInputs h :=
  ofD19LinearCharacterInput
    (D19ActsOnMoore57.D19LinearCharacterInput.ofRepresentationCharacterAndCounts
      (h := h) ρ alpha beta gamma minus8_trivial_nonneg
      minus8_sign_nonneg trace_eq_character character_eq_d19Linear ha0 ha1)
    fixedUpperBound

end D19FinalCharacterInputs

namespace D19ConstructiveFinalInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructive final inputs from a full linear-character equality and the
standard reflection counts. -/
noncomputable def ofLinearCharacterAndCounts
    (alpha beta gamma : ℕ)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112)
    (fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h)
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h where
  character :=
    D19FinalCharacterInputs.ofLinearCharacterAndCounts (h := h)
      alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
      hlin ha0 ha1 fixedUpperBound
  orbitBase := orbitBase
  adjacentMoved := adjacentMoved

/-- Constructive final inputs from mathlib representation-character data and
the standard reflection counts. -/
noncomputable def ofRepresentationCharacterAndCounts
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
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112)
    (fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h)
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalInputs h where
  character :=
    D19FinalCharacterInputs.ofRepresentationCharacterAndCounts (h := h)
      ρ alpha beta gamma minus8_trivial_nonneg minus8_sign_nonneg
      trace_eq_character character_eq_d19Linear ha0 ha1 fixedUpperBound
  orbitBase := orbitBase
  adjacentMoved := adjacentMoved

end D19ConstructiveFinalInputs

end Moore57
