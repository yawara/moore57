import Moore57.Phases.Phase5
import Moore57.Phases.Phase6
import Moore57.Phases.Phase3
import Moore57.D19OnMoore57.E7Projection.Minus8CharacterBoundariesFromRotationSplit

/-!
# Phase 7 prebuilt: construct `RotationCharacterConstancy` from raw action

The natural-language Lemma 9.2 (D₁₉ representation theory) is already
formalized in the codebase via the rotation-invariant / rotation-moving
submodule split (see `Moore57/GroupTheory/D19CharacterClassFromRotationSplit.lean`):

* For any rational representation `ρ : Representation ℚ (DihedralGroup 19) W`,
  - the rotation-invariant summand contributes `α + β` natural-numbered
    multiplicities of the trivial/sign characters (with reflection trace
    `α − β`);
  - the rotation-moving summand has dimension `18·γ` and rotation trace `-γ`
    on every nontrivial rotation (cyclotomic constraint).
* Combined, every nontrivial rotation has character `α + β − γ`, the same
  for every `d ≠ 0`.

Applied to the concrete `E₇` projection representation
`h.e7ProjectionRepresentation` (Phase 2: `finrank = 1729`; Phase 3: `χ_7(t) =
33`), this yields the Phase 5 `RotationCharacterConstancy h` frontier
constructively, removing it from the list of remaining deep gaps.

The remaining work is therefore the geometric side
(`AdjacentMovedReflectionComplementResidual38Witness`).
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Phase 7 packaged record: combines the rotation-character constancy data
with the integer common-value witness and the admissible side arithmetic. -/
structure RotationCharacterConstancyPackage (h : D19ActsOnMoore57 V Γ) where
  alpha : ℕ
  beta : ℕ
  gamma : ℕ
  e7Class :
    D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma
  reflection : (alpha : ℤ) - (beta : ℤ) = 33
  minus8_trivial_nonneg : alpha ≤ 113
  minus8_sign_nonneg : beta ≤ 58

namespace RotationCharacterConstancyPackage

variable {h : D19ActsOnMoore57 V Γ}

/-- The Phase 5 `RotationCharacterConstancy` extracted from the package. -/
noncomputable def toRotationCharacterConstancy
    (pkg : RotationCharacterConstancyPackage h) :
    RotationCharacterConstancy h where
  value := (pkg.alpha : ℚ) + (pkg.beta : ℚ) - (pkg.gamma : ℚ)
  rotation_trace_eq := by
    intro d hd
    calc
      Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d))
          = (h.e7ProjectionRepresentation).character (DihedralGroup.r d) := by
            simpa [D19ActsOnMoore57.rotation] using
              (h.e7ProjectionRepresentation_character_eq_matrix_trace
                (DihedralGroup.r d)).symm
      _ = (pkg.alpha : ℚ) + (pkg.beta : ℚ) - (pkg.gamma : ℚ) :=
            pkg.e7Class.rotation_value d hd

/-- The integer common-value witness for the rotation trace. -/
noncomputable def toIntegerValue (pkg : RotationCharacterConstancyPackage h) :
    pkg.toRotationCharacterConstancy.IntegerValue where
  intValue := (pkg.alpha : ℤ) + (pkg.beta : ℤ) - (pkg.gamma : ℤ)
  value_eq := by
    show (pkg.alpha : ℚ) + (pkg.beta : ℚ) - (pkg.gamma : ℚ) =
      (((pkg.alpha : ℤ) + (pkg.beta : ℤ) - (pkg.gamma : ℤ) : ℤ) : ℚ)
    push_cast
    ring

/-- The rotation-int equality consumed by Phase 6. -/
theorem rotation_int (pkg : RotationCharacterConstancyPackage h) :
    (pkg.alpha : ℤ) + (pkg.beta : ℤ) - (pkg.gamma : ℤ) =
      pkg.toIntegerValue.intValue := rfl

/-- The dimension constraint extracted from the E₇ class boundary. -/
theorem dimension (pkg : RotationCharacterConstancyPackage h) :
    pkg.alpha + pkg.beta + 18 * pkg.gamma = 1729 :=
  pkg.e7Class.dimension

end RotationCharacterConstancyPackage

/-- Phase 7: build the full rotation-character constancy package directly from
the ambient `D19ActsOnMoore57` witness. Uses the rotation-split character
construction with Phase 3 (reflection trace `33`) as input. -/
noncomputable def rotationCharacterConstancyPackage_of_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    RotationCharacterConstancyPackage h := by
  classical
  let data :=
    h.exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_E7_reflection_trace_eq_33
      (dt := 0) (h.reflection_E7_trace_eq_thirtyThree 0)
  refine
    { alpha := data.choose
      beta := data.choose_spec.choose
      gamma := data.choose_spec.choose_spec.choose
      e7Class := data.choose_spec.choose_spec.choose_spec.1
      reflection := data.choose_spec.choose_spec.choose_spec.2.1
      minus8_trivial_nonneg := data.choose_spec.choose_spec.choose_spec.2.2.1
      minus8_sign_nonneg := data.choose_spec.choose_spec.choose_spec.2.2.2 }

/-! ### Phase 7 final assembly: only the geometric witness remains -/

/-- Phase 7 (final): given the geometric compact adjacent-moved witness, the
ambient `D19ActsOnMoore57` witness produces `False`.

The representation-theoretic side (Phase 5 `RotationCharacterConstancy`) is
fully constructed by `rotationCharacterConstancyPackage_of_raw_action`, so the
only remaining input is the geometric
`AdjacentMovedReflectionComplementResidual38Witness h
(h.orbitBaseSelectionInput_of_raw_action)`. -/
theorem false_of_compactAdjacentMoved
    (h : D19ActsOnMoore57 V Γ)
    (adjacentMoved :
      AdjacentMovedReflectionComplementResidual38Witness h
        (h.orbitBaseSelectionInput_of_raw_action)) :
    False :=
  let pkg := h.rotationCharacterConstancyPackage_of_raw_action
  Moore57.D19ActsOnMoore57.false_of_RotationCharacterConstancy_and_compactAdjacentMoved
    h pkg.toRotationCharacterConstancy pkg.toIntegerValue
    pkg.alpha pkg.beta pkg.gamma pkg.reflection pkg.dimension pkg.rotation_int
    pkg.minus8_trivial_nonneg pkg.minus8_sign_nonneg adjacentMoved

end D19ActsOnMoore57

end Moore57
