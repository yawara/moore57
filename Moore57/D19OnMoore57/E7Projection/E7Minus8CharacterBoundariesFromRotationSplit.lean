import Moore57.Foundations.GroupTheory.D19CharacterClassFromRotationSplit
import Moore57.D19OnMoore57.E7Projection.E7Minus8CharacterInputBridge
import Moore57.D19OnMoore57.Rotation.RotationFixedCountOneFrontier
import Moore57.D19OnMoore57.Fixed.FixedInducedStrongStarBridge
import Moore57.D19OnMoore57.Reflection.ReflectionTraceCandidateLowerBoundBridge
import Moore57.D19OnMoore57.Reflection.ReflectionTraceThirtyThreeFixedCount

/-!
# Concrete E7 and `(-8)` character boundaries from the rotation split

The abstract rotation-invariant / moving-summand decomposition applies directly
to the concrete E7 projection representation, and to the complementary `(-8)`
projection representation.  This removes the representation-decomposition
assumption from the E7 side; the remaining concrete inputs are the raw
fixed-count and adjacent-moved-count facts used to evaluate the E7 reflection
trace and the complementary permutation character.
-/

namespace Moore57

noncomputable section

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

theorem exists_e7ProjectionCharacterClassBoundary_from_rotation_split
    (h : D19ActsOnMoore57 V Γ) :
    ∃ alpha beta gamma : ℕ,
      D19CharacterClassBoundary h.e7ProjectionRepresentation
        alpha beta gamma :=
  exists_d19CharacterClassBoundary_from_rotation_split
    h.e7ProjectionRepresentation h.finrank_E7Range_eq_1729

theorem exists_minus8ProjectionCharacterValueBoundary_from_rotation_split
    (h : D19ActsOnMoore57 V Γ) :
    ∃ A B C : ℕ,
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C :=
  exists_d19CharacterValueBoundary_from_rotation_split
    h.minus8ProjectionRepresentation

/-- The abstract rotation split supplies both concrete projection character
packages. -/
theorem exists_e7_and_minus8_characterBoundaries_from_rotation_split
    (h : D19ActsOnMoore57 V Γ) :
    ∃ alpha beta gamma A B C : ℕ,
      D19CharacterClassBoundary h.e7ProjectionRepresentation
        alpha beta gamma ∧
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C := by
  rcases h.exists_e7ProjectionCharacterClassBoundary_from_rotation_split with
    ⟨alpha, beta, gamma, e7Class⟩
  rcases h.exists_minus8ProjectionCharacterValueBoundary_from_rotation_split with
    ⟨A, B, C, minus8Values⟩
  exact ⟨alpha, beta, gamma, A, B, C, e7Class, minus8Values⟩

/-- Once the standard raw count inputs are supplied, the rotation-split
character packages give the exact side arithmetic consumed downstream. -/
theorem exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    ∃ alpha beta gamma : ℕ,
      D19CharacterClassBoundary h.e7ProjectionRepresentation
        alpha beta gamma ∧
      (alpha : ℤ) - (beta : ℤ) = 33 ∧
      alpha ≤ 113 ∧ beta ≤ 58 := by
  rcases h.exists_e7_and_minus8_characterBoundaries_from_rotation_split with
    ⟨alpha, beta, gamma, A, B, C, e7Class, minus8Values⟩
  have hreflection :
      (alpha : ℤ) - (beta : ℤ) = 33 :=
    h.reflection_eq_of_E7_characterClassBoundary alpha beta gamma e7Class
      hreflection_a0 hreflection_a1
  have hbounds :=
    h.alpha_beta_gamma_le_of_E7_minus8_characterBoundaries
      alpha beta gamma A B C e7Class minus8Values
      hreflection_a0 hrotation_a0
  exact ⟨alpha, beta, gamma, e7Class, hreflection, hbounds.1,
    hbounds.2.1⟩

/-- The rotation fixed count is already proved from the ambient action, and
`fixedVertexCount = 56` for a reflection supplies `adjacentMovedCount = 112`
through the fixed-star bridge.  Thus a single raw reflection fixed-count input
is enough for the E7 side arithmetic. -/
theorem exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_reflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56) :
    ∃ alpha beta gamma : ℕ,
      D19CharacterClassBoundary h.e7ProjectionRepresentation
        alpha beta gamma ∧
      (alpha : ℤ) - (beta : ℤ) = 33 ∧
      alpha ≤ 113 ∧ beta ≤ 58 :=
  let hStar :=
    h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56
      dt hreflection_a0
  h.exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic
    hreflection_a0 (hStar.adjacentMovedCount_eq_112 h.isMoore)
    h.rotationFixedCountOne_smulEquiv

/-- The trace-refined reflection candidates mean that a lower bound of `47`
already supplies the single raw reflection fixed-count input needed by the
rotation-split character route. -/
theorem exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_reflectionFixedCount_ge_fortySeven
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (hlower :
      47 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt))) :
    ∃ alpha beta gamma : ℕ,
      D19CharacterClassBoundary h.e7ProjectionRepresentation
        alpha beta gamma ∧
      (alpha : ℤ) - (beta : ℤ) = 33 ∧
      alpha ≤ 113 ∧ beta ≤ 58 :=
  h.exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_reflectionFixedCount
    (h.fixedVertexCount_reflection_eq_56_of_ge_fortySeven dt hlower)

/-- Uniform `47`-lower-bound package version of the rotation-split E7 side
arithmetic bridge. -/
theorem exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_reflectionFixedCountLower47
    (h : D19ActsOnMoore57 V Γ)
    (bounds : ReflectionFixedCountLower47 h)
    (dt : ZMod 19) :
    ∃ alpha beta gamma : ℕ,
      D19CharacterClassBoundary h.e7ProjectionRepresentation
        alpha beta gamma ∧
      (alpha : ℤ) - (beta : ℤ) = 33 ∧
      alpha ≤ 113 ∧ beta ≤ 58 :=
  h.exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_reflectionFixedCount_ge_fortySeven
    (bounds.lower dt)

/-- A single E7 reflection trace value `33` supplies the reflection fixed count
needed by the rotation-split character route. -/
theorem exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_E7_reflection_trace_eq_33
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (htrace33 :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr dt))) =
        (33 : ℚ)) :
    ∃ alpha beta gamma : ℕ,
      D19CharacterClassBoundary h.e7ProjectionRepresentation
        alpha beta gamma ∧
      (alpha : ℤ) - (beta : ℤ) = 33 ∧
      alpha ≤ 113 ∧ beta ≤ 58 :=
  h.exists_e7ProjectionCharacterClassBoundary_and_sideArithmetic_of_reflectionFixedCount
    (h.fixedVertexCount_reflection_eq_56_of_E7_trace_eq_33 dt htrace33)

/-- A representation-free nonempty constructor for the old linear-character
input, conditional only on the raw fixed-count and adjacent-moved-count facts. -/
theorem nonempty_d19LinearCharacterInput_of_rotation_split_and_counts
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    Nonempty (D19LinearCharacterInput h) := by
  rcases h.exists_e7_and_minus8_characterBoundaries_from_rotation_split with
    ⟨alpha, beta, gamma, A, B, C, e7Class, minus8Values⟩
  exact ⟨D19LinearCharacterInput.ofE7AndMinus8CharacterBoundaries
    h alpha beta gamma A B C e7Class minus8Values
    hreflection_a0 hreflection_a1 hrotation_a0⟩

/-- Representation decomposition plus the already-proved rotation count reduce
the old linear-character input to one raw reflection fixed-count fact. -/
theorem nonempty_d19LinearCharacterInput_of_rotation_split_and_reflectionFixedCount
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56) :
    Nonempty (D19LinearCharacterInput h) :=
  let hStar :=
    h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56
      dt hreflection_a0
  h.nonempty_d19LinearCharacterInput_of_rotation_split_and_counts
    hreflection_a0 (hStar.adjacentMovedCount_eq_112 h.isMoore)
    h.rotationFixedCountOne_smulEquiv

/-- The current representation-free character input route now only needs the
weaker trace-refined lower bound `fixedVertexCount ≥ 47` for one reflection. -/
theorem nonempty_d19LinearCharacterInput_of_rotation_split_and_reflectionFixedCount_ge_fortySeven
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (hlower :
      47 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt))) :
    Nonempty (D19LinearCharacterInput h) :=
  h.nonempty_d19LinearCharacterInput_of_rotation_split_and_reflectionFixedCount
    (h.fixedVertexCount_reflection_eq_56_of_ge_fortySeven dt hlower)

/-- Uniform `47`-lower-bound package version of the rotation-split constructor
for the old linear-character input. -/
theorem nonempty_d19LinearCharacterInput_of_rotation_split_and_reflectionFixedCountLower47
    (h : D19ActsOnMoore57 V Γ)
    (bounds : ReflectionFixedCountLower47 h)
    (dt : ZMod 19) :
    Nonempty (D19LinearCharacterInput h) :=
  h.nonempty_d19LinearCharacterInput_of_rotation_split_and_reflectionFixedCount_ge_fortySeven
    (bounds.lower dt)

/-- A single E7 reflection trace value `33` is enough to build the old
linear-character input from the rotation-split character construction. -/
theorem nonempty_d19LinearCharacterInput_of_rotation_split_and_E7_reflection_trace_eq_33
    (h : D19ActsOnMoore57 V Γ)
    {dt : ZMod 19}
    (htrace33 :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr dt))) =
        (33 : ℚ)) :
    Nonempty (D19LinearCharacterInput h) :=
  h.nonempty_d19LinearCharacterInput_of_rotation_split_and_reflectionFixedCount
    (h.fixedVertexCount_reflection_eq_56_of_E7_trace_eq_33 dt htrace33)

end D19ActsOnMoore57

end

end Moore57
