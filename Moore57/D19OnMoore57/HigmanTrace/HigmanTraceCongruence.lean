import Moore57.D19OnMoore57.LinearCharacter.D19LinearCharacterInput
import Moore57.D19Contradiction

/-!
# Higman trace congruence

Macaj-Siran Lemma 3 records the congruence
`a₁(x) ≡ 7 a₀(x) + 5 (mod 15)`, obtained from Higman's trace formula once the
`7`-eigenspace trace is known to be an integer.  This file keeps that
arithmetic step separate from the harder representation-theoretic integrality
input.
-/

namespace Moore57

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace IsMoore57

/-- Higman's trace formula gives the standard congruence once the trace is an
integer.  This is the `ℤ`-valued form, convenient for algebraic manipulation. -/
theorem higman_trace_int_intModEq
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) {z : ℤ}
    (htrace :
      Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ)) :
    (adjacentMovedCount Γ σ : ℤ) ≡
      7 * (fixedVertexCount σ : ℤ) + 5 [ZMOD 15] := by
  have hformula := hΓ.higman_trace_formula σ
  rw [htrace] at hformula
  have hnumℚ :
      8 * (fixedVertexCount σ : ℚ) +
          (adjacentMovedCount Γ σ : ℚ) - 65 =
        15 * (z : ℚ) := by
    linarith
  have hnumℤ :
      8 * (fixedVertexCount σ : ℤ) +
          (adjacentMovedCount Γ σ : ℤ) - 65 =
        15 * z := by
    exact_mod_cast hnumℚ
  rw [Int.modEq_iff_dvd]
  refine ⟨(fixedVertexCount σ : ℤ) - z - 4, ?_⟩
  omega

/-- Natural-number form of the Higman congruence. -/
theorem higman_trace_int_natModEq
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) {z : ℤ}
    (htrace :
      Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ)) :
    adjacentMovedCount Γ σ ≡ 7 * fixedVertexCount σ + 5 [MOD 15] := by
  exact Int.natCast_modEq_iff.mp
    (by
      simpa using hΓ.higman_trace_int_intModEq σ htrace)

end IsMoore57

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

namespace D19LinearCharacterInput

/-- A packaged linear-character input supplies the reflection instance of
Higman's congruence: the reflection character value is the integer
`α - β`. -/
theorem reflection_higman_natModEq
    (hin : D19LinearCharacterInput h) (k : ZMod 19) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) ≡
      7 * fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) + 5 [MOD 15] := by
  apply h.isMoore.higman_trace_int_natModEq
    (σ := h.smulEquiv (DihedralGroup.sr k))
    (z := (hin.multiplicity.alpha : ℤ) - (hin.multiplicity.beta : ℤ))
  rw [hin.linear_character, d19LinearCharacter_reflection]

end D19LinearCharacterInput

end D19ActsOnMoore57

end

end Moore57
