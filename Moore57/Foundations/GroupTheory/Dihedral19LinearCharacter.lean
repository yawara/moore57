import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Elementary D19 character functions

This module is intentionally independent of Moore graphs.  It only records the
three integer-valued class functions on `DihedralGroup 19` used throughout the
project and their elementary values.
-/

namespace Moore57

/-! ### Small character-value functions for `D19` -/

/-- The trivial character of `D19`. -/
def d19TrivCharacter (_g : DihedralGroup 19) : ℤ :=
  1

/-- The sign character of `D19`: rotations have value `1`, reflections `-1`. -/
def d19SignCharacter : DihedralGroup 19 → ℤ
  | DihedralGroup.r _ => 1
  | DihedralGroup.sr _ => -1

/-- The 18-dimensional rational irreducible character used in the D19
obstruction: value `18` at the identity, `-1` at nontrivial rotations, and
`0` at reflections. -/
def d19RhoCharacter : DihedralGroup 19 → ℤ
  | DihedralGroup.r d => if d = 0 then 18 else -1
  | DihedralGroup.sr _ => 0

/-- The character-value function `α⋅1 + β⋅ε + γ⋅ρ`. -/
def d19LinearCharacter (alpha beta gamma : ℕ) (g : DihedralGroup 19) : ℤ :=
  (alpha : ℤ) * d19TrivCharacter g
    + (beta : ℤ) * d19SignCharacter g
    + (gamma : ℤ) * d19RhoCharacter g

@[simp] theorem d19TrivCharacter_apply (g : DihedralGroup 19) :
    d19TrivCharacter g = 1 :=
  rfl

@[simp] theorem d19SignCharacter_rotation (d : ZMod 19) :
    d19SignCharacter (DihedralGroup.r d) = 1 :=
  rfl

@[simp] theorem d19SignCharacter_reflection (d : ZMod 19) :
    d19SignCharacter (DihedralGroup.sr d) = -1 :=
  rfl

@[simp] theorem d19RhoCharacter_one :
    d19RhoCharacter (DihedralGroup.r (0 : ZMod 19)) = 18 := by
  simp [d19RhoCharacter]

@[simp] theorem d19RhoCharacter_rotation_ne {d : ZMod 19} (hd : d ≠ 0) :
    d19RhoCharacter (DihedralGroup.r d) = -1 := by
  simp [d19RhoCharacter, hd]

@[simp] theorem d19RhoCharacter_reflection (d : ZMod 19) :
    d19RhoCharacter (DihedralGroup.sr d) = 0 :=
  rfl

/-- Value of the linear D19 character at the identity. -/
theorem d19LinearCharacter_one (alpha beta gamma : ℕ) :
    d19LinearCharacter alpha beta gamma (1 : DihedralGroup 19) =
      (alpha : ℤ) + (beta : ℤ) + 18 * (gamma : ℤ) := by
  change d19LinearCharacter alpha beta gamma (DihedralGroup.r (0 : ZMod 19)) =
    (alpha : ℤ) + (beta : ℤ) + 18 * (gamma : ℤ)
  simp only [d19LinearCharacter, d19TrivCharacter_apply,
    d19SignCharacter_rotation, d19RhoCharacter_one]
  ring_nf

/-- Value of the linear D19 character at reflections. -/
theorem d19LinearCharacter_reflection (alpha beta gamma : ℕ) (d : ZMod 19) :
    d19LinearCharacter alpha beta gamma (DihedralGroup.sr d) =
      (alpha : ℤ) - (beta : ℤ) := by
  simp [d19LinearCharacter]
  ring_nf

/-- Value of the linear D19 character at nontrivial rotations. -/
theorem d19LinearCharacter_rotation_ne
    (alpha beta gamma : ℕ) {d : ZMod 19} (hd : d ≠ 0) :
    d19LinearCharacter alpha beta gamma (DihedralGroup.r d) =
      (alpha : ℤ) + (beta : ℤ) - (gamma : ℤ) := by
  simp [d19LinearCharacter, d19RhoCharacter_rotation_ne hd]
  ring_nf

end Moore57
