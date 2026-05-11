import Moore57.GroupTheory.D19ReflectionTraceOnInvariants
import Moore57.GroupTheory.D19CyclotomicTrace

/-!
# The cyclotomic constraint on the D19 moving summand

The moving summand is the kernel of the rotation-average projection.  On this
summand a nontrivial rotation has no fixed vector.  Since its nineteenth power
is the identity, the `X - 1` factor can be cancelled from `X^19 - 1`, giving the
`Φ₁₉` annihilator needed for the rational 18-dimensional block.
-/

namespace Moore57

open Polynomial

noncomputable section

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

private theorem exists_nsmul_eq_zmod19_of_ne_zero {d e : ZMod 19} (hd : d ≠ 0) :
    ∃ n : ℕ, n • d = e := by
  refine ⟨(e * d⁻¹).val, ?_⟩
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  calc
    (e * d⁻¹) * d = e * (d⁻¹ * d) := by rw [mul_assoc]
    _ = e * 1 := by rw [inv_mul_cancel₀ hd]
    _ = e := by rw [mul_one]

theorem d19RotationMoving_fixedBy_nonzero_rotation_eq_zero
    (ρ : Representation ℚ (DihedralGroup 19) W) {d : ZMod 19} (hd : d ≠ 0)
    (x : d19RotationMovingSubmodule ρ)
    (hfix : d19RotationMovingRepresentation ρ (DihedralGroup.r d) x = x) :
    x = 0 := by
  have hpowfix : ∀ n : ℕ,
      (d19RotationMovingRepresentation ρ (DihedralGroup.r d) ^ n) x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ']
        change d19RotationMovingRepresentation ρ (DihedralGroup.r d)
          ((d19RotationMovingRepresentation ρ (DihedralGroup.r d) ^ n) x) = x
        rw [ih, hfix]
  have hxinv : x ∈ d19RotationInvariantSubmodule (d19RotationMovingRepresentation ρ) := by
    rw [Representation.mem_invariants]
    intro c
    rcases c with ⟨g, hg⟩
    rcases hg with ⟨e, rfl⟩
    obtain ⟨n, hn⟩ := exists_nsmul_eq_zmod19_of_ne_zero (d := d) (e := e) hd
    have hpow : (DihedralGroup.r d : DihedralGroup 19) ^ n = DihedralGroup.r e := by
      rw [DihedralGroup.r_pow]
      rw [← hn]
      simp [nsmul_eq_mul, mul_comm]
    change (d19RotationMovingRepresentation ρ (DihedralGroup.r e)) x = x
    rw [← hpow, map_pow]
    exact hpowfix n
  have hxbot : x ∈ (⊥ : Submodule ℚ (d19RotationMovingSubmodule ρ)) := by
    rw [← d19RotationMovingRepresentation_invariants_eq_bot ρ]
    exact hxinv
  simpa using hxbot

theorem d19RotationMoving_rotation_pow_nineteen
    (ρ : Representation ℚ (DihedralGroup 19) W) (d : ZMod 19) :
    (d19RotationMovingRepresentation ρ (DihedralGroup.r d)) ^ 19 = 1 := by
  rw [← map_pow]
  rw [DihedralGroup.r_pow]
  change (d19RotationMovingRepresentation ρ)
    (DihedralGroup.r (d * (19 : ZMod 19))) = 1
  have hd19 : d * (19 : ZMod 19) = 0 := by
    rw [show (19 : ZMod 19) = 0 from ZMod.natCast_self 19, mul_zero]
  rw [hd19]
  ext x
  simp [DihedralGroup.r_zero]

theorem d19RotationMoving_rotation_aeval_cyclotomic19_eq_zero
    (ρ : Representation ℚ (DihedralGroup 19) W) {d : ZMod 19} (hd : d ≠ 0) :
    Polynomial.aeval (d19RotationMovingRepresentation ρ (DihedralGroup.r d))
        (Polynomial.cyclotomic 19 ℚ) = 0 := by
  let T := d19RotationMovingRepresentation ρ (DihedralGroup.r d)
  have hker : LinearMap.ker (T - 1) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hsub : T x - x = 0 := by
      simpa [T, sub_eq_add_neg] using (LinearMap.mem_ker.mp hx)
    have hfix : T x = x := sub_eq_zero.mp hsub
    exact by
      have := d19RotationMoving_fixedBy_nonzero_rotation_eq_zero ρ hd x hfix
      simpa using this
  have hpow : T ^ 19 = 1 := by
    dsimp [T]
    exact d19RotationMoving_rotation_pow_nineteen ρ d
  have hX : Polynomial.aeval T ((X : ℚ[X]) ^ 19 - 1) = 0 := by
    simp [hpow]
  have hprod : (X - 1 : ℚ[X]) * Polynomial.cyclotomic 19 ℚ = (X : ℚ[X]) ^ 19 - 1 := by
    rw [mul_comm]
    exact Polynomial.cyclotomic_prime_mul_X_sub_one ℚ 19
  have hzero : Polynomial.aeval T ((X - 1 : ℚ[X]) * Polynomial.cyclotomic 19 ℚ) = 0 := by
    rw [hprod]
    exact hX
  rw [map_mul] at hzero
  apply LinearMap.ext
  intro x
  have hx :=
    congrArg (fun f : Module.End ℚ (d19RotationMovingSubmodule ρ) => f x) hzero
  have hxker :
      Polynomial.aeval T (Polynomial.cyclotomic 19 ℚ) x ∈ LinearMap.ker (T - 1) := by
    change (T - 1) (Polynomial.aeval T (Polynomial.cyclotomic 19 ℚ) x) = 0
    simpa using hx
  have hxbot :
      Polynomial.aeval T (Polynomial.cyclotomic 19 ℚ) x ∈
        (⊥ : Submodule ℚ (d19RotationMovingSubmodule ρ)) := by
    rw [← hker]
    exact hxker
  simpa using hxbot

theorem exists_gamma_finrank_d19RotationMovingSubmodule
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    ∃ gamma : ℕ, Module.finrank ℚ (d19RotationMovingSubmodule ρ) = 18 * gamma := by
  exact finrank_eq_eighteen_mul_of_cyclotomic19_aeval_eq_zero
    (T := d19RotationMovingRepresentation ρ (DihedralGroup.r (1 : ZMod 19)))
    (d19RotationMoving_rotation_aeval_cyclotomic19_eq_zero ρ one_ne_zero)

/-- The moving summand has the rational `18`-dimensional cyclotomic character
trace: every nontrivial rotation has trace `-γ` on it, where its dimension is
`18γ`. -/
theorem exists_gamma_trace_d19RotationMovingSubmodule
    [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W) :
    ∃ gamma : ℕ,
      Module.finrank ℚ (d19RotationMovingSubmodule ρ) = 18 * gamma ∧
        ∀ d : ZMod 19, d ≠ 0 →
          _root_.LinearMap.trace ℚ (d19RotationMovingSubmodule ρ)
            (d19RotationMovingRepresentation ρ (DihedralGroup.r d)) =
              -(gamma : ℚ) := by
  rcases trace_package_of_cyclotomic19_aeval_eq_zero
      (T := d19RotationMovingRepresentation ρ (DihedralGroup.r (1 : ZMod 19)))
      (d19RotationMoving_rotation_aeval_cyclotomic19_eq_zero ρ one_ne_zero) with
    ⟨gamma, hfin, htrace_one⟩
  refine ⟨gamma, hfin, ?_⟩
  intro d hd
  rcases trace_package_of_cyclotomic19_aeval_eq_zero
      (T := d19RotationMovingRepresentation ρ (DihedralGroup.r d))
      (d19RotationMoving_rotation_aeval_cyclotomic19_eq_zero ρ hd) with
    ⟨gamma_d, hfin_d, htrace_d⟩
  have hgamma : gamma_d = gamma := by
    omega
  simpa [hgamma] using htrace_d

end

end Moore57
