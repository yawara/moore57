import Moore57.D19OnMoore57.D19Core.RepresentationMathlibCharacterTools

/-!
# Constructors for D19 character boundaries

The main mathlib-facing bridge already turns structured D19 character
boundaries into pointwise `d19LinearCharacter` equalities.  This file records
the converse packaging direction for proofs that naturally establish the full
pointwise character identity first.
-/

namespace Moore57

noncomputable section

namespace D19CharacterValueBoundary

variable {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
variable {ρ : Representation ℚ (DihedralGroup 19) W}

/-- Package a full pointwise D19 linear-character identity as the value
boundary used by the downstream constructors. -/
def of_character_eq_d19Linear
    (alpha beta gamma : ℕ)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g = (d19LinearCharacter alpha beta gamma g : ℚ)) :
    D19CharacterValueBoundary ρ alpha beta gamma where
  one_value := by
    simpa [d19LinearCharacter_one] using
      character_eq_d19Linear (1 : DihedralGroup 19)
  rotation_value := by
    intro d hd
    simpa [d19LinearCharacter_rotation_ne alpha beta gamma hd] using
      character_eq_d19Linear (DihedralGroup.r d)
  reflection_zero := by
    simpa [d19LinearCharacter_reflection] using
      character_eq_d19Linear (DihedralGroup.sr 0)

end D19CharacterValueBoundary

namespace D19CharacterClassBoundary

variable {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
variable {ρ : Representation ℚ (DihedralGroup 19) W}

/-- Package a full pointwise D19 linear-character identity as a class boundary,
deriving the dimension equation from `Representation.char_one`. -/
def of_character_eq_d19Linear
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (character_eq_d19Linear :
      ∀ g : DihedralGroup 19,
        ρ.character g = (d19LinearCharacter alpha beta gamma g : ℚ)) :
    D19CharacterClassBoundary ρ alpha beta gamma where
  dimension :=
    dimension_eq_of_finrank_eq_of_character_eq
      ρ alpha beta gamma finrank_eq character_eq_d19Linear
  rotation_value := by
    intro d hd
    simpa [d19LinearCharacter_rotation_ne alpha beta gamma hd] using
      character_eq_d19Linear (DihedralGroup.r d)
  reflection_zero := by
    simpa [d19LinearCharacter_reflection] using
      character_eq_d19Linear (DihedralGroup.sr 0)

/-- A value boundary plus the dimension equation can be viewed as the
class-boundary form used for the E7 representation. -/
def of_valueBoundary
    (alpha beta gamma : ℕ)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (valueBoundary : D19CharacterValueBoundary ρ alpha beta gamma) :
    D19CharacterClassBoundary ρ alpha beta gamma where
  dimension := dimension
  rotation_value := valueBoundary.rotation_value
  reflection_zero := valueBoundary.reflection_zero

end D19CharacterClassBoundary

end

end Moore57
