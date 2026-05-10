import Moore57.E7ProjectionDimension
import Moore57.ReflectionFixedCountRawCandidates
import Mathlib.Tactic

/-!
# Character constraints for raw small reflection candidates

This file records representation-theoretic trace constraints which do not use
the full `D19LinearCharacterInput`.  The E7 reflection trace is treated only as
the trace of an involution on a `1729`-dimensional `ℚ`-space, and then compared
with the Higman numerator for the raw fixed-count candidates.
-/

namespace Moore57

noncomputable section

namespace LinearMap

variable {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]

/-- The trace of an involutive endomorphism over `ℚ` has the same parity as the
dimension and lies in the interval `[-dim, dim]`. -/
theorem exists_int_trace_parity_and_range_of_involutive
    (f : W →ₗ[ℚ] W) (hf : f * f = 1) :
    ∃ z : ℤ,
      _root_.LinearMap.trace ℚ W f = (z : ℚ) ∧
        z ≡ (Module.finrank ℚ W : ℤ) [ZMOD 2] ∧
        -(Module.finrank ℚ W : ℤ) ≤ z ∧ z ≤ (Module.finrank ℚ W : ℤ) := by
  let r : ℕ :=
    Module.finrank ℚ
      (_root_.LinearMap.range (Moore57.LinearMap.involutionProjection f))
  let n : ℕ := Module.finrank ℚ W
  refine ⟨2 * (r : ℤ) - (n : ℤ), ?_, ?_, ?_, ?_⟩
  · simpa [r, n] using
      Moore57.LinearMap.trace_eq_two_finrank_involutionProjection_sub_finrank f hf
  · rw [Int.modEq_iff_dvd]
    refine ⟨(n : ℤ) - (r : ℤ), ?_⟩
    ring
  · have hrle : r ≤ n := by
      simpa [r, n] using
        (_root_.LinearMap.finrank_range_le
          (Moore57.LinearMap.involutionProjection f))
    omega
  · have hrle : r ≤ n := by
      simpa [r, n] using
        (_root_.LinearMap.finrank_range_le
          (Moore57.LinearMap.involutionProjection f))
    omega

end LinearMap

namespace ReflectionSmallCandidateCharacterConstraints

/-- Arithmetic package for the E7 involution trace constraints after inserting
the Higman numerator. -/
def HigmanNumeratorTraceAllowed (a0 a1 : ℤ) : Prop :=
  ∃ z : ℤ,
    8 * a0 + a1 - 65 = 15 * z ∧
      z ≡ 1729 [ZMOD 2] ∧ -1729 ≤ z ∧ z ≤ 1729

/-- Star-edge formula specialization: `a₁ = 3248 - 56*a₀`. -/
def StarTraceAllowed (a0 : ℤ) : Prop :=
  HigmanNumeratorTraceAllowed a0 (3248 - 56 * a0)

/-- Regular fixed-induced specialization with explicit edge count `e`. -/
def RegularTraceAllowed (a0 e : ℤ) : Prop :=
  HigmanNumeratorTraceAllowed a0 (3250 - 58 * a0 + 2 * e)

/-- Concrete trace value for the star formula. -/
theorem star_trace_value_iff {a0 z : ℤ} :
    8 * a0 + (3248 - 56 * a0) - 65 = 15 * z ↔
      1061 - 16 * a0 = 5 * z := by
  constructor <;> intro h <;> omega

/-- The raw star candidates all satisfy the involution trace parity/range
constraints.  The corresponding traces are
`193, 161, 129, 97, 65, 33`. -/
theorem star_candidates_survive_trace_parity_range
    {a0 : ℤ}
    (hcand :
      a0 = 6 ∨ a0 = 16 ∨ a0 = 26 ∨ a0 = 36 ∨ a0 = 46 ∨ a0 = 56) :
    StarTraceAllowed a0 := by
  rcases hcand with h6 | h16 | h26 | h36 | h46 | h56
  · subst a0
    refine ⟨193, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [StarTraceAllowed, HigmanNumeratorTraceAllowed, Int.ModEq]
  · subst a0
    refine ⟨161, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [StarTraceAllowed, HigmanNumeratorTraceAllowed, Int.ModEq]
  · subst a0
    refine ⟨129, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [StarTraceAllowed, HigmanNumeratorTraceAllowed, Int.ModEq]
  · subst a0
    refine ⟨97, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [StarTraceAllowed, HigmanNumeratorTraceAllowed, Int.ModEq]
  · subst a0
    refine ⟨65, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [StarTraceAllowed, HigmanNumeratorTraceAllowed, Int.ModEq]
  · subst a0
    refine ⟨33, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [StarTraceAllowed, HigmanNumeratorTraceAllowed, Int.ModEq]

/-- The regular `a₀ = 2`, degree `1`, edge-count `1` candidate is already
incompatible with E7 trace integrality. -/
theorem regular_two_candidate_not_trace_integral :
    ¬ ∃ z : ℤ,
      8 * (2 : ℤ) + (3250 - 58 * (2 : ℤ) + 2 * 1) - 65 = 15 * z := by
  rintro ⟨z, hz⟩
  omega

/-- The regular `a₀ = 2`, degree `1`, edge-count `1` candidate is incompatible
with the stronger parity/range package. -/
theorem regular_two_candidate_not_trace_allowed :
    ¬ RegularTraceAllowed 2 1 := by
  intro h
  exact regular_two_candidate_not_trace_integral ⟨h.choose, h.choose_spec.1⟩

/-- The regular `a₀ = 10`, degree `3`, edge-count `15` candidate satisfies the
E7 involution trace parity/range constraints, with trace `181`. -/
theorem regular_ten_candidate_survives_trace_parity_range :
    RegularTraceAllowed 10 15 := by
  refine ⟨181, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [RegularTraceAllowed, HigmanNumeratorTraceAllowed, Int.ModEq]

/-- For the two regular raw candidates, E7 involution trace constraints exclude
only the `a₀ = 2` case. -/
theorem regular_candidates_trace_allowed_iff
    {a0 e : ℤ}
    (hcand : (a0 = 2 ∧ e = 1) ∨ (a0 = 10 ∧ e = 15)) :
    RegularTraceAllowed a0 e ↔ a0 = 10 ∧ e = 15 := by
  constructor
  · intro hallowed
    rcases hcand with ⟨ha0, he⟩ | h10
    · subst a0
      subst e
      exact False.elim (regular_two_candidate_not_trace_allowed hallowed)
    · exact h10
  · intro h10
    rcases h10 with ⟨ha0, he⟩
    subst a0
    subst e
    exact regular_ten_candidate_survives_trace_parity_range

end ReflectionSmallCandidateCharacterConstraints

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

open ReflectionSmallCandidateCharacterConstraints

variable (h : D19ActsOnMoore57 V Γ)

/-- A reflection E7 trace satisfies the parity and range constraints for an
involution on a `1729`-dimensional `ℚ`-space. -/
theorem exists_int_E7Matrix_mul_permMatrix_reflection_trace_parity_and_range
    (k : ZMod 19) :
    ∃ z : ℤ,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
          (z : ℚ) ∧
        z ≡ 1729 [ZMOD 2] ∧ -1729 ≤ z ∧ z ≤ 1729 := by
  have hsq :
      h.e7ProjectionRepresentation (DihedralGroup.sr k) *
          h.e7ProjectionRepresentation (DihedralGroup.sr k) =
        1 := by
    rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
  obtain ⟨z, hztrace, hzparity, hzlower, hzupper⟩ :=
    Moore57.LinearMap.exists_int_trace_parity_and_range_of_involutive
      (h.e7ProjectionRepresentation (DihedralGroup.sr k)) hsq
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · rw [← h.e7ProjectionRepresentation_character_eq_matrix_trace]
    simpa [Representation.character] using hztrace
  · simpa [h.finrank_e7ProjectionRepresentation_eq_1729] using hzparity
  · simpa [h.finrank_e7ProjectionRepresentation_eq_1729] using hzlower
  · simpa [h.finrank_e7ProjectionRepresentation_eq_1729] using hzupper

/-- Higman's trace formula converts the E7 reflection trace parity/range
constraints into constraints on the numerator `8*a₀ + a₁ - 65`. -/
theorem reflection_higmanNumeratorTraceAllowed
    (k : ZMod 19) :
    HigmanNumeratorTraceAllowed
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ)
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) := by
  obtain ⟨z, htrace, hzparity, hzlower, hzupper⟩ :=
    h.exists_int_E7Matrix_mul_permMatrix_reflection_trace_parity_and_range k
  refine ⟨z, ?_, hzparity, hzlower, hzupper⟩
  have hformula :=
    h.isMoore.higman_trace_formula (h.smulEquiv (DihedralGroup.sr k))
  have hnumℚ :
      8 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℚ) +
          (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℚ) -
            65 =
        15 * (z : ℚ) := by
    rw [htrace] at hformula
    linarith
  exact_mod_cast hnumℚ

end D19ActsOnMoore57

end

end Moore57
