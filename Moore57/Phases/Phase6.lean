import Moore57.Phases.Phase5
import Moore57.Phases.Phase1
import Moore57.D19OnMoore57.Orbit.BaseSelectionFromRawAction
import Moore57.D19OnMoore57.D19Core.OrbitContributionData
import Moore57.D19OnMoore57.Final.RepresentationCompact

/-!
# Phase 6 prebuilt: final assembly from Phase 5 + geometric pieces

Combining the Phase 5 rotation-character constancy frontier with the geometric
pieces already wired by Options A and B (the orbit-base selection and the
A-fiber cardinality `38`), Phase 6 closes the contradiction modulo the two
remaining deep inputs:

* `RotationCharacterConstancy h` (Phase 5) — the rational E₇ character is
  constant on the nontrivial rotation class.
* `a1_decomposition` for the chosen orbit base — the adjacent-moved count
  splits as `38 + 2·Σ_q (filter count)` for every nontrivial rotation.

This file packages the final assembly as a theorem that turns these two
inputs (plus the admissible multiplicities `α, β, γ`) into `False`.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Phase 6: build the reduced `D19TraceInput` from the Phase 5
representation-character data and the Phase 1 fixed-count bound. -/
noncomputable def d19TraceInput_of_RotationCharacterConstancy
    (h : D19ActsOnMoore57 V Γ)
    (rcc : RotationCharacterConstancy h)
    (intval : rcc.IntegerValue)
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (rotation_int : (alpha : ℤ) + (beta : ℤ) - (gamma : ℤ) = intval.intValue)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    D19TraceInput h :=
  (D19LinearCharacterInput.ofE7ProjectionCharacterClassBoundary h
      alpha beta gamma
      (d19CharacterClassBoundary_of_RotationCharacterConstancy rcc intval
        alpha beta gamma reflection dimension rotation_int)
      reflection minus8_trivial_nonneg minus8_sign_nonneg)
    |>.toD19RepresentationCharacterInput
    |>.toD19TraceInput (h.rotationFixedUpperBoundInput_of_raw_action)

/-- Phase 6: build a `D19OrbitContributionData` from Phase 5 multiplicity
inputs plus the geometric `a1_decomposition` over the canonical orbit base. -/
noncomputable def d19OrbitContributionData_of_RotationCharacterConstancy
    (h : D19ActsOnMoore57 V Γ)
    (rcc : RotationCharacterConstancy h)
    (intval : rcc.IntegerValue)
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (rotation_int : (alpha : ℤ) + (beta : ℤ) - (gamma : ℤ) = intval.intValue)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (a1_decomposition :
      ∀ d : ZMod 19, d ≠ 0 →
        h.a1 d =
          38 +
            2 * (∑ q : Fin 56,
              ((h.rotationOrbitFinset
                  ((h.orbitBaseSelectionInput_of_raw_action).base q)).filter
                  fun y => Γ.Adj y (h.rotation d y)).card)) :
    D19OrbitContributionData h where
  base := (h.orbitBaseSelectionInput_of_raw_action).base
  base_moved := (h.orbitBaseSelectionInput_of_raw_action).base_moved
  traceInput :=
    d19TraceInput_of_RotationCharacterConstancy h rcc intval
      alpha beta gamma reflection dimension rotation_int
      minus8_trivial_nonneg minus8_sign_nonneg
  fixedOrAContribution := fun _ => 38
  fixed_or_A_contribution := fun _ _ => rfl
  a1_decomposition := by
    intro d hd
    have h := a1_decomposition d hd
    simpa using h

/-- Phase 6 (final assembly): the two deep inputs together imply `False`.

* `rcc` + `intval` + admissible multiplicities = Phase 5 character data;
* `a1_decomposition` = geometric partition decomposition of adjacent-moved
  counts over the orbit-base family.

Given both, the existing `D19ActionOrbitConcreteData.not_nonempty` pipeline
produces a contradiction. -/
theorem false_of_RotationCharacterConstancy_and_a1Decomposition
    (h : D19ActsOnMoore57 V Γ)
    (rcc : RotationCharacterConstancy h)
    (intval : rcc.IntegerValue)
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (rotation_int : (alpha : ℤ) + (beta : ℤ) - (gamma : ℤ) = intval.intValue)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (a1_decomposition :
      ∀ d : ZMod 19, d ≠ 0 →
        h.a1 d =
          38 +
            2 * (∑ q : Fin 56,
              ((h.rotationOrbitFinset
                  ((h.orbitBaseSelectionInput_of_raw_action).base q)).filter
                  fun y => Γ.Adj y (h.rotation d y)).card)) :
    False :=
  D19ActionOrbitConcreteData.not_nonempty h
    ⟨(d19OrbitContributionData_of_RotationCharacterConstancy h rcc intval
        alpha beta gamma reflection dimension rotation_int
        minus8_trivial_nonneg minus8_sign_nonneg
        a1_decomposition).toActionOrbitConcreteData⟩

/-! ### Compact criterion form of Phase 6

The same final assembly using the existing
`D19FinalRepresentationCountCompactInputs`, which packages the geometric gap
as the smaller `AdjacentMovedReflectionComplementResidual38Witness`.  This
form pins the remaining geometric obligation to a single compact criterion:
cross-disjointness of the 56 base orbits and their reflections, plus the
constant filtered cardinality `38` of the canonical complement residual. -/

/-- Phase 6 (compact form): turn the Phase 5 representation data plus the
compact complement-residual adjacent-moved witness over the canonical orbit
base into a `D19FinalRepresentationCountCompactInputs`. -/
noncomputable def d19FinalRepresentationCountCompactInputs_of_RotationCharacterConstancy
    (h : D19ActsOnMoore57 V Γ)
    (rcc : RotationCharacterConstancy h)
    (intval : rcc.IntegerValue)
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (rotation_int : (alpha : ℤ) + (beta : ℤ) - (gamma : ℤ) = intval.intValue)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (adjacentMoved :
      AdjacentMovedReflectionComplementResidual38Witness h
        (h.orbitBaseSelectionInput_of_raw_action)) :
    D19FinalRepresentationCountCompactInputs h where
  representation :=
    (D19LinearCharacterInput.ofE7ProjectionCharacterClassBoundary h
        alpha beta gamma
        (d19CharacterClassBoundary_of_RotationCharacterConstancy rcc intval
          alpha beta gamma reflection dimension rotation_int)
        reflection minus8_trivial_nonneg minus8_sign_nonneg)
      |>.toD19RepresentationCharacterInput
  rotationOne_fixed_count := by
    have h1 : fixedVertexCount (h.smulEquiv (DihedralGroup.r 1)) = 1 :=
      h.rotationFixedCountOne_smulEquiv 1 (by decide)
    simpa [D19ActsOnMoore57.rotation] using h1
  orbitBase := h.orbitBaseSelectionInput_of_raw_action
  adjacentMoved := adjacentMoved

/-- Phase 6 (compact form, final): the compact adjacent-moved witness plus the
Phase 5 representation data imply `False`. -/
theorem false_of_RotationCharacterConstancy_and_compactAdjacentMoved
    (h : D19ActsOnMoore57 V Γ)
    (rcc : RotationCharacterConstancy h)
    (intval : rcc.IntegerValue)
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (rotation_int : (alpha : ℤ) + (beta : ℤ) - (gamma : ℤ) = intval.intValue)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (adjacentMoved :
      AdjacentMovedReflectionComplementResidual38Witness h
        (h.orbitBaseSelectionInput_of_raw_action)) :
    False :=
  D19FinalRepresentationCountCompactInputs.not_nonempty h
    ⟨d19FinalRepresentationCountCompactInputs_of_RotationCharacterConstancy
      h rcc intval alpha beta gamma reflection dimension rotation_int
      minus8_trivial_nonneg minus8_sign_nonneg adjacentMoved⟩

end D19ActsOnMoore57

end Moore57
