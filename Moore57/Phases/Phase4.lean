import Moore57.Foundations.GroupTheory.Dihedral19LinearCharacter

/-!
# Phase 4 prebuilt aliases for the D₁₉ rational character theory

The natural-language proof, Section 4, uses the three rational irreducible
characters of `DihedralGroup 19`:

* `1` — the trivial character (value `1` on every element).
* `ε` — the sign character (value `1` on rotations, `-1` on reflections).
* `ρ` — the 18-dimensional rational irreducible character (value `18` at the
  identity, `-1` at nontrivial rotations, `0` at reflections).

A general `D₁₉` rational virtual character then has the form
`α·1 + β·ε + γ·ρ` for non-negative integers `α, β, γ`, with class values

* at `1`:           `α + β + 18·γ`
* at reflections:   `α − β`
* at rotations≠1:   `α + β − γ`

This file exposes the elementary character functions and their evaluation
lemmas under stable `Phase4` names referenced in the representation-side
roadmap.  All three characters and their value lemmas are already proved in
`Moore57/GroupTheory/Dihedral19LinearCharacter.lean`; this file only renames
them.
-/

namespace Moore57

/-! ### Phase 4.1: the three rational characters of D₁₉ -/

/-- The trivial character of `D₁₉`. -/
abbrev phase4_trivCharacter : DihedralGroup 19 → ℤ :=
  d19TrivCharacter

/-- The sign character of `D₁₉`: rotations `↦ 1`, reflections `↦ −1`. -/
abbrev phase4_signCharacter : DihedralGroup 19 → ℤ :=
  d19SignCharacter

/-- The 18-dimensional rational irreducible character `ρ` of `D₁₉`. -/
abbrev phase4_rhoCharacter : DihedralGroup 19 → ℤ :=
  d19RhoCharacter

/-- The general rational virtual character `α·1 + β·ε + γ·ρ` on `D₁₉`. -/
abbrev phase4_linearCharacter (alpha beta gamma : ℕ) : DihedralGroup 19 → ℤ :=
  d19LinearCharacter alpha beta gamma

/-! ### Phase 4.2: class values of the linear character -/

/-- Phase 4.2 (identity): `(α·1 + β·ε + γ·ρ)(1) = α + β + 18·γ`. -/
theorem phase4_linearCharacter_one (alpha beta gamma : ℕ) :
    phase4_linearCharacter alpha beta gamma (1 : DihedralGroup 19) =
      (alpha : ℤ) + (beta : ℤ) + 18 * (gamma : ℤ) :=
  d19LinearCharacter_one alpha beta gamma

/-- Phase 4.2 (reflection): `(α·1 + β·ε + γ·ρ)(t) = α − β` on any reflection. -/
theorem phase4_linearCharacter_reflection
    (alpha beta gamma : ℕ) (d : ZMod 19) :
    phase4_linearCharacter alpha beta gamma (DihedralGroup.sr d) =
      (alpha : ℤ) - (beta : ℤ) :=
  d19LinearCharacter_reflection alpha beta gamma d

/-- Phase 4.2 (nontrivial rotation): `(α·1 + β·ε + γ·ρ)(r^d) = α + β − γ`
for `d ≠ 0`. -/
theorem phase4_linearCharacter_rotation_ne
    (alpha beta gamma : ℕ) {d : ZMod 19} (hd : d ≠ 0) :
    phase4_linearCharacter alpha beta gamma (DihedralGroup.r d) =
      (alpha : ℤ) + (beta : ℤ) - (gamma : ℤ) :=
  d19LinearCharacter_rotation_ne alpha beta gamma hd

end Moore57
