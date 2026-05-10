import Moore57.ReflectionRegularTenTraceArithmetic
import Moore57.D19LinearCharacterInput

/-!
# Character boundary for the regular-10 reflection branch

The regular-`10` branch has E7 trace `181` on a reflection.  Any full D19
linear-character description of the E7 trace would therefore force
`alpha - beta = 181` on that reflection.  This file records that boundary and
the immediate incompatibility with the current `TraceMultiplicityData`, whose
reflection equation is `alpha - beta = 33`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace ReflectionRegularTenAllCenterNeighborOrbitsPreserved

variable {h : D19ActsOnMoore57 V Γ} {k : ZMod 19}

/-- If the E7 trace is a full D19 linear character, the regular-`10` branch
forces reflection character value `181`. -/
theorem alpha_sub_beta_eq_181_of_e7_linear_character
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    (alpha beta gamma : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ)) :
    (alpha : ℤ) - (beta : ℤ) = 181 := by
  have htrace := hreg.trace_E7Matrix_mul_permMatrix_eq_181
  have hchar := h7 (DihedralGroup.sr k)
  rw [d19LinearCharacter_reflection] at hchar
  have hq : (((alpha : ℤ) - (beta : ℤ) : ℤ) : ℚ) = (181 : ℚ) := by
    linarith
  exact_mod_cast hq

/-- The regular-`10` branch is incompatible with a full
`D19LinearCharacterInput`, whose packaged reflection character value is `33`. -/
theorem not_d19LinearCharacterInput
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    ¬ Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) := by
  rintro ⟨hin⟩
  have h181 :
      (hin.multiplicity.alpha : ℤ) - (hin.multiplicity.beta : ℤ) = 181 :=
    hreg.alpha_sub_beta_eq_181_of_e7_linear_character
      hin.multiplicity.alpha hin.multiplicity.beta hin.multiplicity.gamma
      hin.linear_character
  have h33 :
      (hin.multiplicity.alpha : ℤ) - (hin.multiplicity.beta : ℤ) = 33 :=
    hin.multiplicity.reflection
  have hbad : (181 : ℤ) = 33 := h181.symm.trans h33
  norm_num at hbad

end ReflectionRegularTenAllCenterNeighborOrbitsPreserved

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- D19 namespace wrapper for the regular-`10` reflection character value. -/
theorem reflectionRegularTen_alpha_sub_beta_eq_181_of_e7_linear_character
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k)
    (alpha beta gamma : ℕ)
    (h7 : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ)) :
    (alpha : ℤ) - (beta : ℤ) = 181 :=
  hreg.alpha_sub_beta_eq_181_of_e7_linear_character alpha beta gamma h7

/-- D19 namespace wrapper: regular-`10` contradicts full linear-character
input. -/
theorem reflectionRegularTen_not_d19LinearCharacterInput
    (k : ZMod 19)
    (hreg : ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k) :
    ¬ Nonempty (D19ActsOnMoore57.D19LinearCharacterInput h) :=
  hreg.not_d19LinearCharacterInput

end D19ActsOnMoore57

end

end Moore57
