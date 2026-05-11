import Moore57.PhaseFourVertexDecomposition
import Moore57.PhaseThreePrebuilt
import Moore57.D19OnMoore57.D19Core.D19RepresentationCharacterDataBridge
import Moore57.D19OnMoore57.D19Core.D19RepresentationCharacterMathlibBridge
import Moore57.D19OnMoore57.E7Projection.E7ProjectionDimension
import Moore57.D19OnMoore57.E7Projection.E7CharacterClassTraceBoundary

/-!
# Phase 5 prebuilt: from vertex orbit decomposition to E₇ multiplicity data

This file packages the next representation-theoretic step in stable Phase 5
form.  Given the vertex orbit decomposition `π_V = 114·1 + 58·ε + 171·ρ`
(Phase 4.4) and the eigenspace identity `E₇` projection (Phase 2/3), Phase 5
constructs the multiplicity data `α, β, γ` for the E₇ representation:

* `α + β + 18·γ = 1729` (Tr(E₇) = 1729, Phase 2.2)
* `α − β = 33` (reflection χ₇(t) = 33, Phase 3.2)
* `α ≤ 113`, `β ≤ 58` (`(-8)`-eigenspace nonnegativity from Phase 4.4 split)

The remaining deep step — that for every nontrivial rotation `r^d`,
`Tr(E₇ P_{r^d}) = α + β − γ` for the SAME `α, β, γ` independent of `d` — is
the rational-character constancy property of the E₇ sub-representation.  It is
exposed here as the `rotationCharacterConstancy` input, to be supplied by the
natural-language Maschke / Galois argument:

  every rational sub-representation of `π_V` has rational character, and a
  rational character on `D₁₉` is constant on the rational conjugacy class of
  nontrivial rotations (which is the single Galois orbit of the 9 nontrivial
  rotation classes `{r^d, r^{-d}}`).

Once this constancy input is provided, the Phase 5 multiplicity data exists
and the downstream Phase 6/7 wiring reaches a contradiction through the
existing E₇ / `(-8)` projection pipeline.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Phase 5 input: the rational-character constancy property for the E₇
projection representation.

For every nontrivial rotation `r^d`, the matrix trace `Tr(E₇ P_{r^d})` equals a
fixed rational number `c` independent of `d`.  This is the Galois / Maschke
consequence that the E₇ sub-representation has rational character. -/
structure RotationCharacterConstancy (h : D19ActsOnMoore57 V Γ) where
  /-- The common rotation-class value of `Tr(E₇ P_{r^d})`. -/
  value : ℚ
  /-- The matrix trace is `value` on every nontrivial rotation. -/
  rotation_trace_eq :
    ∀ d : ZMod 19, d ≠ 0 →
      Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) = value

namespace RotationCharacterConstancy

variable {h : D19ActsOnMoore57 V Γ}

/-- The common rotation trace value is an integer (follows from rationality of
the E₇ character; here we record it as an additional input). -/
structure IntegerValue (rcc : RotationCharacterConstancy h) where
  /-- The integer the common rotation-trace value equals as a rational. -/
  intValue : ℤ
  /-- The cast of `intValue` to `ℚ` is the common rotation-trace value. -/
  value_eq : rcc.value = (intValue : ℚ)

end RotationCharacterConstancy

/-- Phase 5 (E₇ representation reflection value): the mathlib character of
`h.e7ProjectionRepresentation` at every reflection equals `33`. -/
theorem e7ProjectionRepresentation_character_reflection_eq_thirtyThree
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    (h.e7ProjectionRepresentation).character (DihedralGroup.sr k) =
      (33 : ℚ) := by
  rw [h.e7ProjectionRepresentation_character_eq_matrix_trace]
  exact h.reflection_E7_trace_eq_thirtyThree k

/-- Phase 5 (E₇ representation identity value): the mathlib character of
`h.e7ProjectionRepresentation` at the identity equals `1729`. -/
theorem e7ProjectionRepresentation_character_one_eq_1729
    (h : D19ActsOnMoore57 V Γ) :
    (h.e7ProjectionRepresentation).character (1 : DihedralGroup 19) =
      (1729 : ℚ) := by
  rw [Representation.char_one]
  exact_mod_cast h.finrank_E7Range_eq_1729

/-- Phase 5 (E₇ representation rotation value): under the constancy input, the
mathlib character of `h.e7ProjectionRepresentation` at every nontrivial
rotation equals the common value. -/
theorem e7ProjectionRepresentation_character_rotation_ne
    {h : D19ActsOnMoore57 V Γ}
    (rcc : RotationCharacterConstancy h) {d : ZMod 19} (hd : d ≠ 0) :
    (h.e7ProjectionRepresentation).character (DihedralGroup.r d) =
      rcc.value := by
  rw [h.e7ProjectionRepresentation_character_eq_matrix_trace]
  simpa [D19ActsOnMoore57.rotation] using rcc.rotation_trace_eq d hd

/-- Phase 5: from the rotation-character constancy input and integer value, build
the E₇ class-character boundary.  The multiplicities are determined by

* `α − β = 33` (Phase 3 reflection value);
* `α + β + 18·γ = 1729` (Phase 2 dimension);
* `α + β − γ = intValue` (rotation constancy integer value).

The (-8)-eigenspace nonnegativity bounds `α ≤ 113`, `β ≤ 58` come from the
Phase 4.4 vertex split `π_V = 114·1 + 58·ε + 171·ρ` and must be supplied
explicitly here (they are not implied by the rotation constancy alone). -/
noncomputable def d19CharacterClassBoundary_of_RotationCharacterConstancy
    {h : D19ActsOnMoore57 V Γ}
    (rcc : RotationCharacterConstancy h)
    (intval : rcc.IntegerValue)
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (rotation_int : (alpha : ℤ) + (beta : ℤ) - (gamma : ℤ) = intval.intValue) :
    D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma where
  dimension := dimension
  rotation_value := by
    intro d hd
    rw [e7ProjectionRepresentation_character_rotation_ne rcc hd, intval.value_eq]
    exact_mod_cast rotation_int.symm
  reflection_zero := by
    rw [h.e7ProjectionRepresentation_character_reflection_eq_thirtyThree 0]
    have hreflℚ : (alpha : ℚ) - (beta : ℚ) = (33 : ℚ) := by exact_mod_cast reflection
    linarith

/-- Phase 5: under the rotation-character constancy input and admissible
multiplicities, the representation-character components boundary exists. -/
theorem representationCharacterComponentsBoundary_of_RotationCharacterConstancy
    {h : D19ActsOnMoore57 V Γ}
    (rcc : RotationCharacterConstancy h)
    (intval : rcc.IntegerValue)
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (rotation_int : (alpha : ℤ) + (beta : ℤ) - (gamma : ℤ) = intval.intValue)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    RepresentationCharacterComponentsBoundary h :=
  representationCharacterComponentsBoundary_of_E7ProjectionCharacterClassBoundary
    h alpha beta gamma
    (d19CharacterClassBoundary_of_RotationCharacterConstancy rcc intval
      alpha beta gamma reflection dimension rotation_int)
    reflection minus8_trivial_nonneg minus8_sign_nonneg

end D19ActsOnMoore57

end Moore57
