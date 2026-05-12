import Moore57.D19OnMoore57.D19Core.RepresentationMathlibCharacterTools

/-!
# D19 character-value reductions

This file adds conservative mathlib-facing reductions for the D19 character
boundary.  Reflections are already one conjugacy class when `19` is odd, while
rotations are only identified with their inverses by conjugation.
-/

namespace Moore57

/-- Conjugating a rotation by the reflection `sr 0` inverts the rotation
exponent. -/
theorem dihedral19_rotation_conj_reflection_zero (d : ZMod 19) :
    DihedralGroup.sr (0 : ZMod 19) * DihedralGroup.r d *
        (DihedralGroup.sr (0 : ZMod 19))⁻¹ =
      DihedralGroup.r (-d) := by
  rw [DihedralGroup.inv_sr]
  simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]

/-- Mathlib character values on D19 rotations are equal on inverse rotation
pairs. -/
theorem representationCharacter_rotation_eq_rotation_neg
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) (d : ZMod 19) :
    ρ.character (DihedralGroup.r d) =
      ρ.character (DihedralGroup.r (-d)) := by
  rw [← dihedral19_rotation_conj_reflection_zero d]
  exact (Representation.char_conj ρ (DihedralGroup.r d)
    (DihedralGroup.sr (0 : ZMod 19))).symm

/-- A rotation-value obligation reduced to one representative of each inverse
pair.  For every nonzero `d`, it is enough to know the desired value either at
`r d` or at `r (-d)`. -/
structure D19RotationInversePairValueBoundary
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (target : ℚ) where
  pair_value :
    ∀ d : ZMod 19, d ≠ 0 →
      ρ.character (DihedralGroup.r d) = target ∨
        ρ.character (DihedralGroup.r (-d)) = target

namespace D19RotationInversePairValueBoundary

variable {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
variable {ρ : Representation ℚ (DihedralGroup 19) W}
variable {target : ℚ}

/-- Expand inverse-pair rotation data to all nontrivial rotations. -/
theorem rotation_value
    (boundary : D19RotationInversePairValueBoundary ρ target)
    (d : ZMod 19) (hd : d ≠ 0) :
    ρ.character (DihedralGroup.r d) = target := by
  rcases boundary.pair_value d hd with hvalue | hvalue
  · exact hvalue
  · rw [representationCharacter_rotation_eq_rotation_neg ρ d]
    exact hvalue

end D19RotationInversePairValueBoundary

/-- Full D19 value-boundary data reduced to identity, one representative from
each nonzero inverse rotation pair, and the reflection representative `sr 0`.
-/
structure D19CharacterValueInversePairBoundary
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ) where
  one_value :
    ρ.character (1 : DihedralGroup 19) =
      (alpha : ℚ) + (beta : ℚ) + 18 * (gamma : ℚ)
  rotation_pair :
    D19RotationInversePairValueBoundary ρ
      ((alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
  reflection_zero :
    ρ.character (DihedralGroup.sr 0) = (alpha : ℚ) - (beta : ℚ)

namespace D19CharacterValueInversePairBoundary

variable {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
variable {ρ : Representation ℚ (DihedralGroup 19) W}
variable {alpha beta gamma : ℕ}

/-- Expand inverse-pair value data to the existing value-boundary structure. -/
def toValueBoundary
    (boundary : D19CharacterValueInversePairBoundary ρ alpha beta gamma) :
    D19CharacterValueBoundary ρ alpha beta gamma where
  one_value := boundary.one_value
  rotation_value := boundary.rotation_pair.rotation_value
  reflection_zero := boundary.reflection_zero

/-- Convert reduced inverse-pair data to pointwise `d19LinearCharacter`
equality. -/
theorem character_eq_d19Linear
    (boundary : D19CharacterValueInversePairBoundary ρ alpha beta gamma) :
    ∀ g : DihedralGroup 19,
      ρ.character g = (d19LinearCharacter alpha beta gamma g : ℚ) :=
  boundary.toValueBoundary.character_eq_d19Linear

end D19CharacterValueInversePairBoundary

/-- Class-boundary data reduced to the dimension equation, one representative
from each nonzero inverse rotation pair, and `sr 0`. -/
structure D19CharacterClassInversePairBoundary
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ) where
  dimension : alpha + beta + 18 * gamma = 1729
  rotation_pair :
    D19RotationInversePairValueBoundary ρ
      ((alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
  reflection_zero :
    ρ.character (DihedralGroup.sr 0) = (alpha : ℚ) - (beta : ℚ)

namespace D19CharacterClassInversePairBoundary

variable {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
variable {ρ : Representation ℚ (DihedralGroup 19) W}
variable {alpha beta gamma : ℕ}

/-- Expand inverse-pair class data to the existing class-boundary structure. -/
def toClassBoundary
    (boundary : D19CharacterClassInversePairBoundary ρ alpha beta gamma) :
    D19CharacterClassBoundary ρ alpha beta gamma where
  dimension := boundary.dimension
  rotation_value := boundary.rotation_pair.rotation_value
  reflection_zero := boundary.reflection_zero

/-- Expand inverse-pair class data to the existing value-boundary structure,
deriving the identity value from `Representation.char_one`. -/
def toValueBoundary
    (boundary : D19CharacterClassInversePairBoundary ρ alpha beta gamma)
    (finrank_eq : Module.finrank ℚ W = 1729) :
    D19CharacterValueBoundary ρ alpha beta gamma :=
  boundary.toClassBoundary.toValueBoundary finrank_eq

/-- Convert reduced class data to pointwise `d19LinearCharacter` equality. -/
theorem character_eq_d19Linear
    (boundary : D19CharacterClassInversePairBoundary ρ alpha beta gamma)
    (finrank_eq : Module.finrank ℚ W = 1729) :
    ∀ g : DihedralGroup 19,
      ρ.character g = (d19LinearCharacter alpha beta gamma g : ℚ) :=
  (boundary.toValueBoundary finrank_eq).character_eq_d19Linear

end D19CharacterClassInversePairBoundary

end Moore57
