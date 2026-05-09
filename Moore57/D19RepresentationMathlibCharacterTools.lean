import Moore57.D19RepresentationCharacterMathlibBridge

/-!
# Mathlib character tools for the D19 representation input

This file keeps the next representation-theoretic step on the mathlib side:
`Representation.char_one` turns a full character decomposition into the
dimension equation at the identity.  The remaining hypotheses below are the
D19-specific finite character decomposition, reflection value, and `-8`
isotypic nonnegativity checks.
-/

namespace Moore57

/-- Mathlib's character-at-identity theorem, specialized to the D19 group and
the rational coefficient field used in this project. -/
theorem representationCharacter_one_eq_finrank
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    ρ.character (1 : DihedralGroup 19) = (Module.finrank ℚ W : ℚ) :=
  Representation.char_one ρ

/-- If a mathlib representation has D19 linear character
`α·1 + β·ε + γ·ρ`, then its dimension is the value of that character at the
identity.  The only D19-specific computation here is
`d19LinearCharacter_one`. -/
theorem finrank_eq_d19LinearCharacter_one_of_character_eq
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ)) :
    (Module.finrank ℚ W : ℚ) =
      (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ) := by
  calc
    (Module.finrank ℚ W : ℚ)
        = ρ.character (1 : DihedralGroup 19) :=
      (representationCharacter_one_eq_finrank ρ).symm
    _ = (d19LinearCharacter alpha beta gamma (1 : DihedralGroup 19) : ℚ) :=
      character_eq_d19Linear 1
    _ = (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ) := by
      rw [d19LinearCharacter_one]
      norm_num

/-- Character decomposition plus `finrank = 1729` supplies the dimension
equation expected by `TraceMultiplicityData`. -/
theorem dimension_eq_of_finrank_eq_of_character_eq
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ)) :
    alpha + beta + 18 * gamma = 1729 := by
  have hdimℚ :
      ((alpha + beta + 18 * gamma : ℕ) : ℚ) = (1729 : ℚ) := by
    calc
      ((alpha + beta + 18 * gamma : ℕ) : ℚ)
          = (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ) := by
        norm_num
      _ = (Module.finrank ℚ W : ℚ) :=
        (finrank_eq_d19LinearCharacter_one_of_character_eq
          ρ alpha beta gamma character_eq_d19Linear).symm
      _ = (1729 : ℚ) := by
        rw [finrank_eq]
        norm_num
  exact_mod_cast hdimℚ

namespace TraceMultiplicityData

/-- Build the project multiplicity record when the dimension field is supplied
by a mathlib character computation at the identity.

The reflection equation and the two `-8` bounds remain explicit finite D19
checks. -/
def ofMathlibCharacter
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    TraceMultiplicityData where
  alpha := alpha
  beta := beta
  gamma := gamma
  reflection := reflection
  dimension :=
    dimension_eq_of_finrank_eq_of_character_eq
      ρ alpha beta gamma finrank_eq character_eq_d19Linear
  minus8_trivial_nonneg := minus8_trivial_nonneg
  minus8_sign_nonneg := minus8_sign_nonneg

@[simp] theorem ofMathlibCharacter_alpha
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    (ofMathlibCharacter ρ alpha beta gamma finrank_eq character_eq_d19Linear
      reflection minus8_trivial_nonneg minus8_sign_nonneg).alpha = alpha :=
  rfl

@[simp] theorem ofMathlibCharacter_beta
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    (ofMathlibCharacter ρ alpha beta gamma finrank_eq character_eq_d19Linear
      reflection minus8_trivial_nonneg minus8_sign_nonneg).beta = beta :=
  rfl

@[simp] theorem ofMathlibCharacter_gamma
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    (ofMathlibCharacter ρ alpha beta gamma finrank_eq character_eq_d19Linear
      reflection minus8_trivial_nonneg minus8_sign_nonneg).gamma = gamma :=
  rfl

end TraceMultiplicityData

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19LinearCharacterInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Build the full linear-character input from a mathlib representation, using
`Representation.char_one` to fill the dimension equation. -/
noncomputable def ofRepresentationCharacterComponents
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    D19LinearCharacterInput h :=
  ofRepresentationCharacter (h := h) ρ
    (TraceMultiplicityData.ofMathlibCharacter ρ alpha beta gamma
      finrank_eq character_eq_d19Linear reflection
      minus8_trivial_nonneg minus8_sign_nonneg)
    trace_eq_character
    (by
      intro g
      simpa [TraceMultiplicityData.ofMathlibCharacter] using
        character_eq_d19Linear g)

@[simp] theorem ofRepresentationCharacterComponents_multiplicity
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    (ofRepresentationCharacterComponents (h := h) ρ alpha beta gamma
      finrank_eq trace_eq_character character_eq_d19Linear reflection
      minus8_trivial_nonneg minus8_sign_nonneg).multiplicity =
        TraceMultiplicityData.ofMathlibCharacter ρ alpha beta gamma
          finrank_eq character_eq_d19Linear reflection
          minus8_trivial_nonneg minus8_sign_nonneg :=
  rfl

end D19LinearCharacterInput

/-- Direct component-boundary constructor from a mathlib representation, with
the dimension equation supplied by `Representation.char_one`. -/
theorem representationCharacterComponentsBoundary_of_representationCharacterComponents
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g =
          (d19LinearCharacter alpha beta gamma g : ℚ))
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofRepresentationCharacterComponents (h := h)
      ρ alpha beta gamma finrank_eq trace_eq_character
      character_eq_d19Linear reflection minus8_trivial_nonneg
      minus8_sign_nonneg)
    |>.representationCharacterComponentsBoundary

end D19ActsOnMoore57

end Moore57
