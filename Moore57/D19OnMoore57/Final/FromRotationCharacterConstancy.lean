import Moore57.D19OnMoore57.E7Projection.RotationCharacterConstancy
import Moore57.D19OnMoore57.Rotation.FixedCountOneFrontier
import Moore57.D19OnMoore57.Orbit.BaseSelectionFromRawAction
import Moore57.D19OnMoore57.D19Core.OrbitContributionData
import Moore57.D19OnMoore57.Final.RepresentationCompact

/-!
# Final assembly from a `RotationCharacterConstancy` witness

Combining the rotation-character constancy frontier with the geometric pieces
(orbit-base selection and the A-fiber cardinality `38`), this file closes the
contradiction modulo the two remaining deep inputs:

* `RotationCharacterConstancy h` — the rational E₇ character is constant on
  the nontrivial rotation class.
* `a1_decomposition` for the chosen orbit base — the adjacent-moved count
  splits as `38 + 2·Σ_q (filter count)` for every nontrivial rotation.

The compact form replaces `a1_decomposition` by the smaller
`AdjacentMovedReflectionComplementResidual38Witness`, pinning the geometric
obligation to a single compact criterion: cross-disjointness of the 56 base
orbits and their reflections, plus the constant filtered cardinality `38` of
the canonical complement residual.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Build the reduced `D19TraceInput` from the rotation-character constancy
data and the fixed-count bound. -/
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
    |>.toD19TraceInput (RotationFixedUpperBoundInput.of_provedRotationFixedCountOne h)

/-- Build a `D19OrbitContributionData` from the rotation-character constancy
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

/-- The rotation-character constancy data + the geometric `a1_decomposition`
together imply `False` via `D19ActionOrbitConcreteData.not_nonempty`. -/
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

/-! ### Compact criterion form

The same final assembly using `D19FinalRepresentationCountCompactInputs`,
which packages the geometric gap as the smaller
`AdjacentMovedReflectionComplementResidual38Witness`. -/

/-- Compact form: turn the rotation-character constancy data plus the compact
complement-residual adjacent-moved witness over the canonical orbit base into
a `D19FinalRepresentationCountCompactInputs`. -/
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

/-- Compact form, final: the compact adjacent-moved witness plus the
rotation-character constancy data imply `False`. -/
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
