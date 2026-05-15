import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic

/-!
# Cyclotomic trace input for the rational `Φ_p`-isotypic summand

任意の素数 `p` について `Φ_p = Polynomial.cyclotomic p ℚ` が annihilator となる
Q-線形作用素について, 次元 `(p-1) γ`, trace `-γ` の trace package を与える generic 版.

`D19CyclotomicTrace.lean` (p=19) と `C11CyclotomicTrace` 相当 (p=11) はこの
generic 版の thin wrapper として実装される.
-/

namespace Moore57

noncomputable section

open Polynomial

/-- The `p`-th cyclotomic polynomial over `ℚ` is the geometric sum (for `p` prime). -/
theorem cyclotomic_prime_rat_eq_geom_sum (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Polynomial.cyclotomic p ℚ = ∑ i ∈ Finset.range p, (X : ℚ[X]) ^ i := by
  simpa using (Polynomial.cyclotomic_prime ℚ p)

/-- The degree of `Φ_p` over `ℚ` is `p - 1`. -/
theorem natDegree_cyclotomic_prime_rat (p : ℕ) [hp : Fact (Nat.Prime p)] :
    (Polynomial.cyclotomic p ℚ).natDegree = p - 1 := by
  rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hp.out]

/-- The coefficient of `X^(p-2)` in `Φ_p` over `ℚ` is `1` (for `p` prime). -/
theorem coeff_cyclotomic_prime_rat_pred_pred (p : ℕ) [hp : Fact (Nat.Prime p)] :
    (Polynomial.cyclotomic p ℚ).coeff (p - 2) = 1 := by
  rw [cyclotomic_prime_rat_eq_geom_sum]
  have hp2 : 2 ≤ p := hp.out.two_le
  have hmem : p - 2 ∈ Finset.range p := by
    rw [Finset.mem_range]; omega
  -- coeff (Σ X^i) (p-2) = 1 since exactly i = p-2 contributes
  simp only [finset_sum_coeff, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single (p - 2)]
  · simp
  · intro b hb hne
    rw [if_neg]
    intro h
    exact hne h.symm
  · intro hne
    exact absurd hmem hne

/-- `Φ_p` is irreducible over `ℚ` (for `p` prime, hence `p ≠ 1`). -/
theorem irreducible_cyclotomic_prime_rat (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Irreducible (Polynomial.cyclotomic p ℚ) :=
  Polynomial.cyclotomic.irreducible_rat hp.out.one_lt.le

/-- The next-to-leading coefficient of `Φ_p` over `ℚ` is `1` (for `p` prime, `p ≥ 2`). -/
theorem nextCoeff_cyclotomic_prime_rat (p : ℕ) [hp : Fact (Nat.Prime p)] :
    (Polynomial.cyclotomic p ℚ).nextCoeff = 1 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  rw [Polynomial.nextCoeff, natDegree_cyclotomic_prime_rat]
  have hp1ne : p - 1 ≠ 0 := by omega
  rw [if_neg hp1ne]
  have hsub : p - 1 - 1 = p - 2 := by omega
  rw [hsub, coeff_cyclotomic_prime_rat_pred_pred]

/-- The next-to-leading coefficient of `(Φ_p)^γ` over `ℚ` is `γ`. -/
theorem nextCoeff_cyclotomic_prime_rat_pow (p : ℕ) [hp : Fact (Nat.Prime p)]
    (gamma : ℕ) :
    ((Polynomial.cyclotomic p ℚ) ^ gamma).nextCoeff = (gamma : ℚ) := by
  rw [(Polynomial.cyclotomic.monic p ℚ).nextCoeff_pow,
    nextCoeff_cyclotomic_prime_rat]
  simp

private theorem matrix_trace_comp_diagonal_leftMulMatrix
    {R A : Type*} [Field R] [Field A] [Algebra R A]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (bA : Module.Basis ι R A) (a : A) :
    Matrix.trace
        (Matrix.comp κ κ ι ι R
          ((Matrix.diagonal (fun _ : κ => a)).map (Algebra.leftMulMatrix bA))) =
      Fintype.card κ • Algebra.trace R A a := by
  rw [Algebra.trace_eq_matrix_trace bA]
  simp [Matrix.trace, Matrix.diag, Matrix.comp_apply,
    Fintype.sum_prod_type, Finset.sum_const]

namespace LinearMap

/-- Trace of scalar multiplication after restricting scalars through a finite
field extension. -/
theorem trace_restrictScalars_lsmul
    {R A M : Type*} [Field R] [Field A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [FiniteDimensional R A] [FiniteDimensional A M] (a : A) :
    _root_.LinearMap.trace R M
        ((_root_.LinearMap.lsmul A M a).restrictScalars R) =
      Module.finrank A M • Algebra.trace R A a := by
  classical
  let bA := Module.Free.chooseBasis R A
  let bM := Module.Free.chooseBasis A M
  have hmat := _root_.LinearMap.restrictScalars_toMatrix
    (R := R) (A := A) (M := M) bA bM (_root_.LinearMap.lsmul A M a)
  have hdiag :
      _root_.LinearMap.toMatrix bM bM (_root_.LinearMap.lsmul A M a) =
        Matrix.diagonal (fun _ => a) :=
    toMatrix_distrib_mul_action_toLinearMap bM a
  rw [_root_.LinearMap.trace_eq_matrix_trace R (bA.smulTower' bM), hmat, hdiag]
  rw [matrix_trace_comp_diagonal_leftMulMatrix bA a]
  rw [Module.finrank_eq_card_basis bM]

end LinearMap

/-- The trace of a primitive `p`-th root in `ℚ[X] / (Φ_p)` is `-1`. -/
theorem trace_adjoinRoot_root_cyclotomic_prime
    (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Algebra.trace ℚ (AdjoinRoot (Polynomial.cyclotomic p ℚ))
        (AdjoinRoot.root (Polynomial.cyclotomic p ℚ)) = -1 := by
  let P : Polynomial ℚ := Polynomial.cyclotomic p ℚ
  have hmonic : P.Monic := Polynomial.cyclotomic.monic p ℚ
  haveI : Fact (Irreducible P) :=
    ⟨by simpa [P] using irreducible_cyclotomic_prime_rat p⟩
  have hroot : minpoly ℚ (AdjoinRoot.root P) = P := by
    simpa [hmonic.leadingCoeff] using
      (AdjoinRoot.minpoly_root (K := ℚ) (f := P) hmonic.ne_zero)
  have htrace :
      Algebra.trace ℚ (AdjoinRoot P) (AdjoinRoot.root P) = -P.nextCoeff := by
    calc
      Algebra.trace ℚ (AdjoinRoot P) (AdjoinRoot.root P)
          = Algebra.trace ℚ (AdjoinRoot P)
              (AdjoinRoot.powerBasis hmonic.ne_zero).gen := by
              rw [AdjoinRoot.powerBasis_gen]
      _ = -(minpoly ℚ (AdjoinRoot.powerBasis hmonic.ne_zero).gen).nextCoeff := by
              rw [PowerBasis.trace_gen_eq_nextCoeff_minpoly]
      _ = -P.nextCoeff := by
              rw [AdjoinRoot.powerBasis_gen, hroot]
  simpa [P, nextCoeff_cyclotomic_prime_rat] using htrace

/-- The same root trace stated with the quotient-ring spelling. -/
theorem trace_quotient_cyclotomic_prime_X_eq_neg_one
    (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Algebra.trace ℚ
      (Polynomial ℚ ⧸
        Ideal.span ({Polynomial.cyclotomic p ℚ} : Set (Polynomial ℚ)))
      (Ideal.Quotient.mk
        (Ideal.span ({Polynomial.cyclotomic p ℚ} : Set (Polynomial ℚ)))
        (X : Polynomial ℚ)) = -1 := by
  change
    Algebra.trace ℚ (AdjoinRoot (Polynomial.cyclotomic p ℚ))
      (AdjoinRoot.root (Polynomial.cyclotomic p ℚ)) = -1
  exact trace_adjoinRoot_root_cyclotomic_prime p

/-- If an endomorphism is annihilated by `Φ_p`, then the underlying rational
dimension is a multiple of `p - 1`. -/
theorem finrank_eq_pred_mul_of_cyclotomic_prime_aeval_eq_zero
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M)
    (hT : Polynomial.aeval T (Polynomial.cyclotomic p ℚ) = 0) :
    ∃ gamma : ℕ, Module.finrank ℚ M = (p - 1) * gamma := by
  let instPoly : Module (Polynomial ℚ) (Module.AEval ℚ M T) :=
    Module.AEval.instModulePolynomial T
  letI : Module (Polynomial ℚ) (Module.AEval ℚ M T) := instPoly
  let instRat : Module ℚ (Module.AEval ℚ M T) := inferInstance
  letI : Module ℚ (Module.AEval ℚ M T) := instRat
  let P : Polynomial ℚ := Polynomial.cyclotomic p ℚ
  have htor : Module.IsTorsionBy (Polynomial ℚ) (Module.AEval ℚ M T) P := by
    intro x
    apply (Module.AEval.of ℚ M T).symm.injective
    rw [Module.AEval.of_symm_smul]
    change Polynomial.aeval T (Polynomial.cyclotomic p ℚ) _ = 0
    rw [hT]
    rfl
  haveI hmax : (Ideal.span ({P} : Set (Polynomial ℚ))).IsMaximal := by
    dsimp [P]
    exact PrincipalIdealRing.isMaximal_of_irreducible (irreducible_cyclotomic_prime_rat p)
  let instField : Field (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ))) :=
    Ideal.Quotient.field (Ideal.span ({P} : Set (Polynomial ℚ)))
  letI : Field (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ))) := instField
  let instQuot : Module (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ)))
      (Module.AEval ℚ M T) :=
    @Module.IsTorsionBy.module (Polynomial ℚ) (Module.AEval ℚ M T)
      inferInstance inferInstance instPoly P inferInstance htor
  letI : Module (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ)))
      (Module.AEval ℚ M T) := instQuot
  haveI : IsScalarTower ℚ (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ)))
      (Module.AEval ℚ M T) :=
    @Module.IsTorsionBySet.isScalarTower (Polynomial ℚ) (Module.AEval ℚ M T)
      inferInstance inferInstance instPoly (Ideal.span ({P} : Set (Polynomial ℚ)))
      inferInstance
      ((Module.isTorsionBySet_span_singleton_iff
        (M := Module.AEval ℚ M T) P).mpr htor)
      ℚ inferInstance inferInstance inferInstance inferInstance
  have hfinA :
      Module.finrank ℚ (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ))) = p - 1 := by
    dsimp [P]
    rw [finrank_quotient_span_eq_natDegree']
    · exact natDegree_cyclotomic_prime_rat p
    · exact Polynomial.cyclotomic.monic p ℚ
  let gamma := Module.finrank (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ)))
    (Module.AEval ℚ M T)
  refine ⟨gamma, ?_⟩
  let instFree : Module.Free (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ)))
      (Module.AEval ℚ M T) :=
    @Module.Free.of_divisionRing
      (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ)))
      (Module.AEval ℚ M T) inferInstance inferInstance instQuot
  letI : Module.Free (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ)))
      (Module.AEval ℚ M T) := instFree
  have hmul := Module.finrank_mul_finrank ℚ
    (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ)))
    (Module.AEval ℚ M T)
  rw [hfinA] at hmul
  have hMN : Module.finrank ℚ M = Module.finrank ℚ (Module.AEval ℚ M T) :=
    LinearEquiv.finrank_eq (Module.AEval.of ℚ M T)
  rw [hMN, ← hmul]

/-- If an endomorphism is annihilated by `Φ_p`, then the rational dimension is
`(p-1)γ` and the trace is `-γ`. -/
theorem trace_package_of_cyclotomic_prime_aeval_eq_zero
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M)
    (hT : Polynomial.aeval T (Polynomial.cyclotomic p ℚ) = 0) :
    ∃ gamma : ℕ,
      Module.finrank ℚ M = (p - 1) * gamma ∧
        _root_.LinearMap.trace ℚ M T = -(gamma : ℚ) := by
  let instPoly : Module (Polynomial ℚ) (Module.AEval ℚ M T) :=
    Module.AEval.instModulePolynomial T
  letI : Module (Polynomial ℚ) (Module.AEval ℚ M T) := instPoly
  let instRat : Module ℚ (Module.AEval ℚ M T) := inferInstance
  letI : Module ℚ (Module.AEval ℚ M T) := instRat
  let instFiniteRat : Module.Finite ℚ (Module.AEval ℚ M T) := inferInstance
  letI : Module.Finite ℚ (Module.AEval ℚ M T) := instFiniteRat
  let P : Polynomial ℚ := Polynomial.cyclotomic p ℚ
  have htor : Module.IsTorsionBy (Polynomial ℚ) (Module.AEval ℚ M T) P := by
    intro x
    apply (Module.AEval.of ℚ M T).symm.injective
    rw [Module.AEval.of_symm_smul]
    change Polynomial.aeval T (Polynomial.cyclotomic p ℚ) _ = 0
    rw [hT]
    rfl
  haveI hmax : (Ideal.span ({P} : Set (Polynomial ℚ))).IsMaximal := by
    dsimp [P]
    exact PrincipalIdealRing.isMaximal_of_irreducible (irreducible_cyclotomic_prime_rat p)
  let instField : Field (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ))) :=
    Ideal.Quotient.field (Ideal.span ({P} : Set (Polynomial ℚ)))
  letI : Field (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ))) := instField
  let instQuot : Module (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ)))
      (Module.AEval ℚ M T) :=
    @Module.IsTorsionBy.module (Polynomial ℚ) (Module.AEval ℚ M T)
      inferInstance inferInstance instPoly P inferInstance htor
  letI : Module (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ)))
      (Module.AEval ℚ M T) := instQuot
  haveI : IsScalarTower ℚ (Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ)))
      (Module.AEval ℚ M T) :=
    @Module.IsTorsionBySet.isScalarTower (Polynomial ℚ) (Module.AEval ℚ M T)
      inferInstance inferInstance instPoly (Ideal.span ({P} : Set (Polynomial ℚ)))
      inferInstance
      ((Module.isTorsionBySet_span_singleton_iff
        (M := Module.AEval ℚ M T) P).mpr htor)
      ℚ inferInstance inferInstance inferInstance inferInstance
  have hmk_smul (x : Module.AEval ℚ M T) :
      ((Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial ℚ)))
          (X : Polynomial ℚ) :
          Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ))) • x) =
        (X : Polynomial ℚ) • x :=
    rfl
  let A := Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ))
  let instFiniteBase : Module.Finite ℚ A := by
    dsimp [A, P]
    exact (Polynomial.cyclotomic.monic p ℚ).finite_quotient
  letI : Module.Finite ℚ A := instFiniteBase
  let instFree : Module.Free A (Module.AEval ℚ M T) :=
    @Module.Free.of_divisionRing A (Module.AEval ℚ M T)
      inferInstance inferInstance instQuot
  letI : Module.Free A (Module.AEval ℚ M T) := instFree
  let instFinite : Module.Finite A (Module.AEval ℚ M T) :=
    Module.Finite.of_restrictScalars_finite ℚ A (Module.AEval ℚ M T)
  letI : Module.Finite A (Module.AEval ℚ M T) := instFinite
  let gamma := Module.finrank A (Module.AEval ℚ M T)
  refine ⟨gamma, ?_, ?_⟩
  · let instFreeA : Module.Free ℚ A := by infer_instance
    haveI : Module.Free ℚ A := instFreeA
    have hfinA : Module.finrank ℚ A = p - 1 := by
      dsimp [A, P]
      rw [finrank_quotient_span_eq_natDegree']
      · exact natDegree_cyclotomic_prime_rat p
      · exact Polynomial.cyclotomic.monic p ℚ
    have hmul := Module.finrank_mul_finrank ℚ A (Module.AEval ℚ M T)
    rw [hfinA] at hmul
    have hMN :
        Module.finrank ℚ M = Module.finrank ℚ (Module.AEval ℚ M T) :=
      LinearEquiv.finrank_eq (Module.AEval.of ℚ M T)
    rw [hMN, ← hmul]
  · let rootA : A :=
      Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial ℚ))) X
    let e : M ≃ₗ[ℚ] Module.AEval ℚ M T := Module.AEval.of ℚ M T
    let scalarRoot : Module.AEval ℚ M T →ₗ[A] Module.AEval ℚ M T :=
      _root_.LinearMap.lsmul A (Module.AEval ℚ M T) rootA
    have hconj :
        e.conj T = scalarRoot.restrictScalars ℚ := by
      apply LinearMap.ext
      intro x
      apply e.symm.injective
      change T (e.symm x) = e.symm ((rootA : A) • x)
      change T (e.symm x) = e.symm
          ((Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial ℚ)))
              (X : Polynomial ℚ) :
              Polynomial ℚ ⧸ Ideal.span ({P} : Set (Polynomial ℚ))) • x)
      rw [hmk_smul x]
      rw [Module.AEval.of_symm_X_smul]
      rfl
    have htraceConj :=
      @_root_.LinearMap.trace_conj' ℚ inferInstance M inferInstance inferInstance
        (Module.AEval ℚ M T) inferInstance instRat T e
    calc
      _root_.LinearMap.trace ℚ M T
          = _root_.LinearMap.trace ℚ (Module.AEval ℚ M T)
              (e.conj T) := htraceConj.symm
      _ = _root_.LinearMap.trace ℚ (Module.AEval ℚ M T)
            (scalarRoot.restrictScalars ℚ) := by
        rw [hconj]
      _ = (Module.finrank A (Module.AEval ℚ M T) : ℚ) •
            Algebra.trace ℚ A rootA := by
        dsimp [scalarRoot]
        simpa using
          (@LinearMap.trace_restrictScalars_lsmul ℚ A (Module.AEval ℚ M T)
            inferInstance instField inferInstance inferInstance instRat instQuot
            inferInstance instFiniteBase instFinite rootA)
      _ = -(gamma : ℚ) := by
        have hroot : Algebra.trace ℚ A rootA = -1 := by
          dsimp [A, rootA, P]
          exact trace_quotient_cyclotomic_prime_X_eq_neg_one p
        rw [hroot]
        simp [gamma]

/-! ### Charpoly-flavored corollaries -/

/-- Linear-map trace as the negative next-to-leading coefficient of the
characteristic polynomial.  (Generic, not depending on `p`.) -/
theorem LinearMap.trace_eq_neg_charpoly_nextCoeff
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M) :
    _root_.LinearMap.trace ℚ M T = -T.charpoly.nextCoeff := by
  let b := Module.Free.chooseBasis ℚ M
  calc
    _root_.LinearMap.trace ℚ M T = Matrix.trace (_root_.LinearMap.toMatrix b b T) := by
      rw [_root_.LinearMap.trace_eq_matrix_trace ℚ b]
    _ = -((_root_.LinearMap.toMatrix b b T).charpoly.nextCoeff) := by
      rw [Matrix.trace_eq_neg_charpoly_nextCoeff]
    _ = -T.charpoly.nextCoeff := by
      rw [_root_.LinearMap.charpoly_toMatrix]

/-- If the characteristic polynomial is exactly `Φ_p`, then the trace is `-1`. -/
theorem trace_eq_neg_one_of_charpoly_eq_cyclotomic_prime
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M)
    (hchar : T.charpoly = Polynomial.cyclotomic p ℚ) :
    _root_.LinearMap.trace ℚ M T = -1 := by
  rw [LinearMap.trace_eq_neg_charpoly_nextCoeff T, hchar,
    nextCoeff_cyclotomic_prime_rat]

/-- If the characteristic polynomial is exactly `Φ_p`, then the dimension is `p - 1`. -/
theorem finrank_eq_pred_of_charpoly_eq_cyclotomic_prime
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M)
    (hchar : T.charpoly = Polynomial.cyclotomic p ℚ) :
    Module.finrank ℚ M = p - 1 := by
  have hdeg := _root_.LinearMap.charpoly_natDegree (R := ℚ) (M := M) T
  rw [hchar, natDegree_cyclotomic_prime_rat] at hdeg
  exact hdeg.symm

/-- One-copy version of the target trace package, under the stronger
characteristic-polynomial hypothesis. -/
theorem trace_package_of_charpoly_eq_cyclotomic_prime
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M)
    (hchar : T.charpoly = Polynomial.cyclotomic p ℚ) :
    ∃ gamma : ℕ,
      Module.finrank ℚ M = (p - 1) * gamma ∧
        _root_.LinearMap.trace ℚ M T = -(gamma : ℚ) := by
  refine ⟨1, ?_, ?_⟩
  · simpa using finrank_eq_pred_of_charpoly_eq_cyclotomic_prime p T hchar
  · simpa using trace_eq_neg_one_of_charpoly_eq_cyclotomic_prime p T hchar

/-- If the characteristic polynomial is a power of `Φ_p`, then the dimension
is `(p-1)` times the exponent. -/
theorem finrank_eq_pred_mul_of_charpoly_eq_cyclotomic_prime_pow
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M) (gamma : ℕ)
    (hchar : T.charpoly = (Polynomial.cyclotomic p ℚ) ^ gamma) :
    Module.finrank ℚ M = (p - 1) * gamma := by
  have hdeg := _root_.LinearMap.charpoly_natDegree (R := ℚ) (M := M) T
  rw [hchar, (Polynomial.cyclotomic.monic p ℚ).natDegree_pow,
    natDegree_cyclotomic_prime_rat] at hdeg
  rw [hdeg.symm, Nat.mul_comm]

/-- If the characteristic polynomial is a power of `Φ_p`, then the trace is
the negative of the exponent. -/
theorem trace_eq_neg_of_charpoly_eq_cyclotomic_prime_pow
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M) (gamma : ℕ)
    (hchar : T.charpoly = (Polynomial.cyclotomic p ℚ) ^ gamma) :
    _root_.LinearMap.trace ℚ M T = -(gamma : ℚ) := by
  rw [LinearMap.trace_eq_neg_charpoly_nextCoeff T, hchar,
    nextCoeff_cyclotomic_prime_rat_pow]

/-- The target trace package, under the characteristic-polynomial power
hypothesis. -/
theorem trace_package_of_charpoly_eq_cyclotomic_prime_pow
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M) (gamma : ℕ)
    (hchar : T.charpoly = (Polynomial.cyclotomic p ℚ) ^ gamma) :
    ∃ gamma : ℕ,
      Module.finrank ℚ M = (p - 1) * gamma ∧
        _root_.LinearMap.trace ℚ M T = -(gamma : ℚ) := by
  refine ⟨gamma, ?_, ?_⟩
  · exact finrank_eq_pred_mul_of_charpoly_eq_cyclotomic_prime_pow p T gamma hchar
  · exact trace_eq_neg_of_charpoly_eq_cyclotomic_prime_pow p T gamma hchar

end

end Moore57
