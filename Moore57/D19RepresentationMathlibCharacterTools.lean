import Moore57.D19RepresentationCharacterMathlibBridge
import Moore57.ZMod19Lemmas

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

/-- A function on `D19` agrees with `d19LinearCharacter` once its values are
known on the identity, nontrivial rotations, and reflections. -/
theorem character_eq_d19Linear_of_values
    (χ : DihedralGroup 19 → ℚ)
    (alpha beta gamma : ℕ)
    (one_value :
      χ (1 : DihedralGroup 19) =
        (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ))
    (rotation_value :
      ∀ d : ZMod 19, d ≠ 0 →
        χ (DihedralGroup.r d) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (reflection_value :
      ∀ k : ZMod 19,
        χ (DihedralGroup.sr k) = (alpha : ℚ) - (beta : ℚ)) :
    ∀ g : DihedralGroup 19,
      χ g = (d19LinearCharacter alpha beta gamma g : ℚ) := by
  intro g
  cases g with
  | r d =>
      by_cases hd : d = 0
      · subst d
        simpa [DihedralGroup.r_zero, d19LinearCharacter_one] using one_value
      · simpa [d19LinearCharacter_rotation_ne alpha beta gamma hd] using
          rotation_value d hd
  | sr k =>
      simpa [d19LinearCharacter_reflection] using reflection_value k

/-- Every reflection in `D19` is conjugate to `sr 0`. -/
theorem dihedral19_reflection_conj_zero (k : ZMod 19) :
    ∃ a : ZMod 19,
      DihedralGroup.r a * DihedralGroup.sr 0 * (DihedralGroup.r a)⁻¹ =
        DihedralGroup.sr k := by
  let a : ZMod 19 := -((2 : ZMod 19)⁻¹ * k)
  refine ⟨a, ?_⟩
  have htwo : (2 : ZMod 19) * ((2 : ZMod 19)⁻¹ * k) = k := by
    rw [← mul_assoc, mul_inv_cancel₀ two_ne_zero_zmod19, one_mul]
  simp [a]
  rw [← two_mul, htwo]

/-- Mathlib character values are constant on the reflection class of `D19`. -/
theorem representationCharacter_reflection_eq_reflection_zero
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) (k : ZMod 19) :
    ρ.character (DihedralGroup.sr k) =
      ρ.character (DihedralGroup.sr 0) := by
  rcases dihedral19_reflection_conj_zero k with ⟨a, ha⟩
  rw [← ha]
  exact Representation.char_conj ρ (DihedralGroup.sr 0) (DihedralGroup.r a)

/-- The D19 character-value boundary used by the final proof: identity,
nontrivial rotations, and one representative of the reflection class. -/
structure D19CharacterValueBoundary
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ) where
  one_value :
    ρ.character (1 : DihedralGroup 19) =
      (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ)
  rotation_value :
    ∀ d : ZMod 19, d ≠ 0 →
      ρ.character (DihedralGroup.r d) =
        (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)
  reflection_zero :
    ρ.character (DihedralGroup.sr 0) = (alpha : ℚ) - (beta : ℚ)

namespace D19CharacterValueBoundary

variable {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
variable {ρ : Representation ℚ (DihedralGroup 19) W}
variable {alpha beta gamma : ℕ}

/-- Extend the reflection value from `sr 0` to every reflection. -/
theorem reflection_value
    (boundary : D19CharacterValueBoundary ρ alpha beta gamma)
    (k : ZMod 19) :
    ρ.character (DihedralGroup.sr k) = (alpha : ℚ) - (beta : ℚ) := by
  rw [representationCharacter_reflection_eq_reflection_zero ρ k]
  exact boundary.reflection_zero

/-- Convert the value-boundary structure to pointwise `d19LinearCharacter`
equality. -/
theorem character_eq_d19Linear
    (boundary : D19CharacterValueBoundary ρ alpha beta gamma) :
    ∀ g : DihedralGroup 19,
      ρ.character g = (d19LinearCharacter alpha beta gamma g : ℚ) :=
  character_eq_d19Linear_of_values ρ.character alpha beta gamma
    boundary.one_value boundary.rotation_value boundary.reflection_value

end D19CharacterValueBoundary

/-- Character class data in the form closest to the natural-language
representation argument: the dimension equation, values on nontrivial
rotations, and one reflection representative.  The identity character value is
derived from mathlib's `Representation.char_one`. -/
structure D19CharacterClassBoundary
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ) where
  dimension : alpha + beta + 18 * gamma = 1729
  rotation_value :
    ∀ d : ZMod 19, d ≠ 0 →
      ρ.character (DihedralGroup.r d) =
        (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)
  reflection_zero :
    ρ.character (DihedralGroup.sr 0) = (alpha : ℚ) - (beta : ℚ)

namespace D19CharacterClassBoundary

variable {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
variable {ρ : Representation ℚ (DihedralGroup 19) W}
variable {alpha beta gamma : ℕ}

/-- The identity value follows from `Representation.char_one`, the ambient
finrank, and the stored dimension equation. -/
theorem one_value
    (boundary : D19CharacterClassBoundary ρ alpha beta gamma)
    (finrank_eq : Module.finrank ℚ W = 1729) :
    ρ.character (1 : DihedralGroup 19) =
      (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ) := by
  have hdimℚ :
      ((alpha + beta + 18 * gamma : ℕ) : ℚ) = (1729 : ℚ) := by
    exact_mod_cast boundary.dimension
  calc
    ρ.character (1 : DihedralGroup 19)
        = (Module.finrank ℚ W : ℚ) :=
      representationCharacter_one_eq_finrank ρ
    _ = (1729 : ℚ) := by
      rw [finrank_eq]
      norm_num
    _ = ((alpha + beta + 18 * gamma : ℕ) : ℚ) :=
      hdimℚ.symm
    _ = (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ) := by
      norm_num

/-- Extend the stored reflection representative value to every reflection. -/
theorem reflection_value
    (boundary : D19CharacterClassBoundary ρ alpha beta gamma)
    (k : ZMod 19) :
    ρ.character (DihedralGroup.sr k) = (alpha : ℚ) - (beta : ℚ) := by
  rw [representationCharacter_reflection_eq_reflection_zero ρ k]
  exact boundary.reflection_zero

/-- Convert class-boundary data to the value-boundary structure used by the
existing constructors. -/
def toValueBoundary
    (boundary : D19CharacterClassBoundary ρ alpha beta gamma)
    (finrank_eq : Module.finrank ℚ W = 1729) :
    D19CharacterValueBoundary ρ alpha beta gamma where
  one_value := boundary.one_value finrank_eq
  rotation_value := boundary.rotation_value
  reflection_zero := boundary.reflection_zero

/-- Convert class-boundary data to pointwise `d19LinearCharacter` equality. -/
theorem character_eq_d19Linear
    (boundary : D19CharacterClassBoundary ρ alpha beta gamma)
    (finrank_eq : Module.finrank ℚ W = 1729) :
    ∀ g : DihedralGroup 19,
      ρ.character g = (d19LinearCharacter alpha beta gamma g : ℚ) :=
  (boundary.toValueBoundary finrank_eq).character_eq_d19Linear

end D19CharacterClassBoundary

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

/-- Build the project multiplicity record from class-value data on identity,
nontrivial rotations, and reflections. -/
def ofMathlibCharacterValues
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (one_value :
      ρ.character (1 : DihedralGroup 19) =
        (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ))
    (rotation_value :
      ∀ d : ZMod 19, d ≠ 0 →
        ρ.character (DihedralGroup.r d) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (reflection_value :
      ∀ k : ZMod 19,
        ρ.character (DihedralGroup.sr k) = (alpha : ℚ) - (beta : ℚ))
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    TraceMultiplicityData :=
  ofMathlibCharacter ρ alpha beta gamma finrank_eq
    (character_eq_d19Linear_of_values ρ.character alpha beta gamma
      one_value rotation_value reflection_value)
    reflection minus8_trivial_nonneg minus8_sign_nonneg

/-- Build the project multiplicity record from the structured D19
character-value boundary. -/
def ofMathlibCharacterValueBoundary
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (characterValues : D19CharacterValueBoundary ρ alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    TraceMultiplicityData :=
  ofMathlibCharacter ρ alpha beta gamma finrank_eq
    characterValues.character_eq_d19Linear reflection
    minus8_trivial_nonneg minus8_sign_nonneg

/-- Build the project multiplicity record from class-boundary data, deriving
the identity character value through mathlib. -/
def ofMathlibCharacterClassBoundary
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (characterClass : D19CharacterClassBoundary ρ alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    TraceMultiplicityData :=
  ofMathlibCharacter ρ alpha beta gamma finrank_eq
    (characterClass.character_eq_d19Linear finrank_eq) reflection
    minus8_trivial_nonneg minus8_sign_nonneg

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

/-- Build the full linear-character input from class-value data on identity,
nontrivial rotations, and reflections. -/
noncomputable def ofRepresentationCharacterValues
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (one_value :
      ρ.character (1 : DihedralGroup 19) =
        (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ))
    (rotation_value :
      ∀ d : ZMod 19, d ≠ 0 →
        ρ.character (DihedralGroup.r d) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (reflection_value :
      ∀ k : ZMod 19,
        ρ.character (DihedralGroup.sr k) = (alpha : ℚ) - (beta : ℚ))
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    D19LinearCharacterInput h :=
  ofRepresentationCharacterComponents (h := h) ρ alpha beta gamma
    finrank_eq trace_eq_character
    (character_eq_d19Linear_of_values ρ.character alpha beta gamma
      one_value rotation_value reflection_value)
    reflection minus8_trivial_nonneg minus8_sign_nonneg

/-- Build the full linear-character input from the structured D19
character-value boundary. -/
noncomputable def ofRepresentationCharacterValueBoundary
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (characterValues : D19CharacterValueBoundary ρ alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    D19LinearCharacterInput h :=
  ofRepresentationCharacterComponents (h := h) ρ alpha beta gamma
    finrank_eq trace_eq_character characterValues.character_eq_d19Linear
    reflection minus8_trivial_nonneg minus8_sign_nonneg

/-- Build the full linear-character input from class-boundary data, deriving
the identity value through `Representation.char_one`. -/
noncomputable def ofRepresentationCharacterClassBoundary
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (characterClass : D19CharacterClassBoundary ρ alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    D19LinearCharacterInput h :=
  ofRepresentationCharacterComponents (h := h) ρ alpha beta gamma
    finrank_eq trace_eq_character
    (characterClass.character_eq_d19Linear finrank_eq)
    reflection minus8_trivial_nonneg minus8_sign_nonneg

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

/-- Direct component-boundary constructor from class-value data on identity,
nontrivial rotations, and reflections. -/
theorem representationCharacterComponentsBoundary_of_representationCharacterValues
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (one_value :
      ρ.character (1 : DihedralGroup 19) =
        (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ))
    (rotation_value :
      ∀ d : ZMod 19, d ≠ 0 →
        ρ.character (DihedralGroup.r d) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (reflection_value :
      ∀ k : ZMod 19,
        ρ.character (DihedralGroup.sr k) = (alpha : ℚ) - (beta : ℚ))
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofRepresentationCharacterValues (h := h)
      ρ alpha beta gamma finrank_eq trace_eq_character
      one_value rotation_value reflection_value reflection
      minus8_trivial_nonneg minus8_sign_nonneg)
    |>.representationCharacterComponentsBoundary

/-- Direct component-boundary constructor from the structured D19
character-value boundary. -/
theorem representationCharacterComponentsBoundary_of_representationCharacterValueBoundary
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (characterValues : D19CharacterValueBoundary ρ alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofRepresentationCharacterValueBoundary (h := h)
      ρ alpha beta gamma finrank_eq trace_eq_character characterValues
      reflection minus8_trivial_nonneg minus8_sign_nonneg)
    |>.representationCharacterComponentsBoundary

/-- Direct component-boundary constructor from class-boundary data. -/
theorem representationCharacterComponentsBoundary_of_representationCharacterClassBoundary
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (characterClass : D19CharacterClassBoundary ρ alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofRepresentationCharacterClassBoundary (h := h)
      ρ alpha beta gamma finrank_eq trace_eq_character characterClass
      reflection minus8_trivial_nonneg minus8_sign_nonneg)
    |>.representationCharacterComponentsBoundary

end D19ActsOnMoore57

end Moore57
