import Moore57.Foundations.GroupTheory.CyclotomicPrimeTrace

/-!
# Cyclotomic trace input for the rational `D19` summand (legacy thin wrapper)

`CyclotomicPrimeTrace.lean` の generic 版 (任意の素数 `p`) を `p = 19` に
特殊化した薄いラッパー. 既存の downstream (例: `D19RotationMovingCyclotomic.lean`)
が利用していた名前を維持する.
-/

namespace Moore57

noncomputable section

open Polynomial

private theorem nat_prime_nineteen : Nat.Prime 19 := by
  norm_num [Nat.Prime]

private instance : Fact (Nat.Prime 19) := ⟨nat_prime_nineteen⟩

/-- The 19th cyclotomic polynomial over `ℚ` is the expected geometric sum. -/
theorem cyclotomic19_rat_eq_geom_sum :
    Polynomial.cyclotomic 19 ℚ = ∑ i ∈ Finset.range 19, (X : ℚ[X]) ^ i :=
  cyclotomic_prime_rat_eq_geom_sum 19

/-- The degree of `Φ₁₉` over `ℚ` is `18`. -/
theorem natDegree_cyclotomic19_rat :
    (Polynomial.cyclotomic 19 ℚ).natDegree = 18 := by
  simpa using natDegree_cyclotomic_prime_rat 19

/-- The coefficient of `X^17` in `Φ₁₉` over `ℚ` is `1`. -/
theorem coeff_cyclotomic19_rat_seventeen :
    (Polynomial.cyclotomic 19 ℚ).coeff 17 = 1 := by
  simpa using coeff_cyclotomic_prime_rat_pred_pred 19

/-- `Φ₁₉` is irreducible over `ℚ`. -/
theorem irreducible_cyclotomic19_rat :
    Irreducible (Polynomial.cyclotomic 19 ℚ) :=
  irreducible_cyclotomic_prime_rat 19

/-- The next-to-leading coefficient of `Φ₁₉` over `ℚ` is `1`. -/
theorem nextCoeff_cyclotomic19_rat :
    (Polynomial.cyclotomic 19 ℚ).nextCoeff = 1 :=
  nextCoeff_cyclotomic_prime_rat 19

/-- The next-to-leading coefficient of `(Φ₁₉)^γ` over `ℚ` is `γ`. -/
theorem nextCoeff_cyclotomic19_rat_pow (gamma : ℕ) :
    ((Polynomial.cyclotomic 19 ℚ) ^ gamma).nextCoeff = (gamma : ℚ) :=
  nextCoeff_cyclotomic_prime_rat_pow 19 gamma

/-- The trace of a primitive 19th root in `ℚ[X] / (Φ₁₉)` is `-1`. -/
theorem trace_adjoinRoot_root_cyclotomic19 :
    Algebra.trace ℚ (AdjoinRoot (Polynomial.cyclotomic 19 ℚ))
        (AdjoinRoot.root (Polynomial.cyclotomic 19 ℚ)) = -1 :=
  trace_adjoinRoot_root_cyclotomic_prime 19

/-- The same root trace stated with the quotient-ring spelling used by the
torsion-by-`Φ₁₉` module structure. -/
theorem trace_quotient_cyclotomic19_X_eq_neg_one :
    Algebra.trace ℚ
      (Polynomial ℚ ⧸
        Ideal.span ({Polynomial.cyclotomic 19 ℚ} : Set (Polynomial ℚ)))
      (Ideal.Quotient.mk
        (Ideal.span ({Polynomial.cyclotomic 19 ℚ} : Set (Polynomial ℚ)))
        (X : Polynomial ℚ)) = -1 :=
  trace_quotient_cyclotomic_prime_X_eq_neg_one 19

/-- If an endomorphism is annihilated by `Φ₁₉`, then the underlying rational
dimension is a multiple of `18`. -/
theorem finrank_eq_eighteen_mul_of_cyclotomic19_aeval_eq_zero
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M)
    (hT : Polynomial.aeval T (Polynomial.cyclotomic 19 ℚ) = 0) :
    ∃ gamma : ℕ, Module.finrank ℚ M = 18 * gamma := by
  simpa using finrank_eq_pred_mul_of_cyclotomic_prime_aeval_eq_zero 19 T hT

/-- If an endomorphism is annihilated by `Φ₁₉`, then the rational dimension is
`18γ` and the trace is `-γ`.

The proof views the space as a module over the quotient field
`ℚ[X] / (Φ₁₉)`, where `T` becomes scalar multiplication by the image of `X`. -/
theorem trace_package_of_cyclotomic19_aeval_eq_zero
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M)
    (hT : Polynomial.aeval T (Polynomial.cyclotomic 19 ℚ) = 0) :
    ∃ gamma : ℕ,
      Module.finrank ℚ M = 18 * gamma ∧
        _root_.LinearMap.trace ℚ M T = -(gamma : ℚ) := by
  simpa using trace_package_of_cyclotomic_prime_aeval_eq_zero 19 T hT

/-- If the characteristic polynomial is exactly `Φ₁₉`, then the trace is `-1`. -/
theorem trace_eq_neg_one_of_charpoly_eq_cyclotomic19
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M)
    (hchar : T.charpoly = Polynomial.cyclotomic 19 ℚ) :
    _root_.LinearMap.trace ℚ M T = -1 :=
  trace_eq_neg_one_of_charpoly_eq_cyclotomic_prime 19 T hchar

/-- If the characteristic polynomial is exactly `Φ₁₉`, then the dimension is `18`. -/
theorem finrank_eq_eighteen_of_charpoly_eq_cyclotomic19
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M)
    (hchar : T.charpoly = Polynomial.cyclotomic 19 ℚ) :
    Module.finrank ℚ M = 18 := by
  simpa using finrank_eq_pred_of_charpoly_eq_cyclotomic_prime 19 T hchar

/-- A one-copy version of the target trace package, under the stronger
characteristic-polynomial hypothesis. -/
theorem trace_package_of_charpoly_eq_cyclotomic19
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M)
    (hchar : T.charpoly = Polynomial.cyclotomic 19 ℚ) :
    ∃ gamma : ℕ,
      Module.finrank ℚ M = 18 * gamma ∧
        _root_.LinearMap.trace ℚ M T = -(gamma : ℚ) := by
  simpa using trace_package_of_charpoly_eq_cyclotomic_prime 19 T hchar

/-- If the characteristic polynomial is a power of `Φ₁₉`, then the dimension
is `18` times the exponent. -/
theorem finrank_eq_eighteen_mul_of_charpoly_eq_cyclotomic19_pow
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M) (gamma : ℕ)
    (hchar : T.charpoly = (Polynomial.cyclotomic 19 ℚ) ^ gamma) :
    Module.finrank ℚ M = 18 * gamma := by
  simpa using finrank_eq_pred_mul_of_charpoly_eq_cyclotomic_prime_pow 19 T gamma hchar

/-- If the characteristic polynomial is a power of `Φ₁₉`, then the trace is
the negative of the exponent. -/
theorem trace_eq_neg_of_charpoly_eq_cyclotomic19_pow
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M) (gamma : ℕ)
    (hchar : T.charpoly = (Polynomial.cyclotomic 19 ℚ) ^ gamma) :
    _root_.LinearMap.trace ℚ M T = -(gamma : ℚ) :=
  trace_eq_neg_of_charpoly_eq_cyclotomic_prime_pow 19 T gamma hchar

/-- The target trace package, under the characteristic-polynomial power
hypothesis.  The remaining gap to the requested annihilator-only statement is
showing that `Polynomial.aeval T (Φ₁₉) = 0` forces this characteristic-polynomial
shape. -/
theorem trace_package_of_charpoly_eq_cyclotomic19_pow
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M) (gamma : ℕ)
    (hchar : T.charpoly = (Polynomial.cyclotomic 19 ℚ) ^ gamma) :
    ∃ gamma : ℕ,
      Module.finrank ℚ M = 18 * gamma ∧
        _root_.LinearMap.trace ℚ M T = -(gamma : ℚ) := by
  simpa using trace_package_of_charpoly_eq_cyclotomic_prime_pow 19 T gamma hchar

end

end Moore57
