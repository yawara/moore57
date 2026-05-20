import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Trace.Basic
import Moore57.Foundations.GroupTheory.CyclotomicPrimeTrace

/-!
# Trace integrality of cyclotomic-annihilated endomorphisms (generic `d`)

**Roadmap [B4.3] Step 4 full — composite-order generalization.**

This module generalizes `CyclotomicPrimeTrace.lean`'s
`trace_package_of_cyclotomic_prime_aeval_eq_zero` (prime `p`) to any
`d ≥ 1`:

> If `T : M →ₗ[ℚ] M` satisfies `aeval T (cyclotomic d ℚ) = 0`
> (with `0 < d`), then `trace ℚ M T ∈ ℤ`.

The proof follows the same `Module.AEval` + `Module.IsTorsionBy` +
quotient-field structure as the prime case, using:

* `Polynomial.cyclotomic.irreducible_rat hd` (Mathlib) for the quotient
  to be a field
* `Polynomial.natDegree_cyclotomic d ℚ = Nat.totient d` (Mathlib) for
  the dimension count
* `PowerBasis.trace_gen_eq_nextCoeff_minpoly` for the trace formula
* `map_cyclotomic_int` for the ℤ-integrality of cyclotomic coefficients.

Unlike the prime case, we do not assert the explicit `μ(d)` value of
the per-block trace — we just need integrality, and that follows from
`nextCoeff (cyclotomic d ℚ) ∈ image(ℤ → ℚ)`.

## Main result

* `trace_int_of_cyclotomic_aeval_eq_zero` — `aeval T (cyclotomic d ℚ) = 0`
  with `0 < d` ⟹ `∃ k : ℤ, trace ℚ M T = k`.
-/

open Polynomial

namespace Moore57

/-- `nextCoeff (cyclotomic d ℚ)` is the image of an integer.

Combined with the trace formula for `[X]` in `ℚ[X]/(Φ_d)`, this is the
key integrality input. -/
theorem nextCoeff_cyclotomic_rat_isInt (d : ℕ) :
    ∃ k : ℤ, (Polynomial.cyclotomic d ℚ).nextCoeff = (k : ℚ) := by
  refine ⟨(Polynomial.cyclotomic d ℤ).nextCoeff, ?_⟩
  have hinj : Function.Injective ((Int.castRingHom ℚ) : ℤ → ℚ) := Int.cast_injective
  rw [← map_cyclotomic_int d ℚ, Polynomial.nextCoeff_map hinj]
  rfl

/-- The trace of "multiplication by `X`" in the quotient ring
`ℚ[X] / (cyclotomic d ℚ)` is the negative of `nextCoeff (cyclotomic d ℚ)`,
and in particular an integer. -/
theorem trace_quotient_cyclotomic_X_isInt (d : ℕ) (hd : 0 < d) :
    ∃ k : ℤ, Algebra.trace ℚ
        (Polynomial ℚ ⧸
          Ideal.span ({Polynomial.cyclotomic d ℚ} : Set (Polynomial ℚ)))
        (Ideal.Quotient.mk
          (Ideal.span ({Polynomial.cyclotomic d ℚ} : Set (Polynomial ℚ)))
          (X : Polynomial ℚ)) = (k : ℚ) := by
  let P : Polynomial ℚ := Polynomial.cyclotomic d ℚ
  have hmonic : P.Monic := Polynomial.cyclotomic.monic d ℚ
  haveI : Fact (Irreducible P) :=
    ⟨by simpa [P] using Polynomial.cyclotomic.irreducible_rat hd⟩
  have hroot : minpoly ℚ (AdjoinRoot.root P) = P := by
    simpa [hmonic.leadingCoeff] using
      (AdjoinRoot.minpoly_root (K := ℚ) (f := P) hmonic.ne_zero)
  -- Convert quotient form to AdjoinRoot form
  have heq :
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
  obtain ⟨k, hk⟩ := nextCoeff_cyclotomic_rat_isInt d
  refine ⟨-k, ?_⟩
  change
    Algebra.trace ℚ (AdjoinRoot (Polynomial.cyclotomic d ℚ))
        (AdjoinRoot.root (Polynomial.cyclotomic d ℚ)) = _
  rw [heq, hk]
  push_cast
  ring

/-- **B4.3 Step 4 main (per-block)**: If a ℚ-linear endomorphism `T` of a
finite-dimensional ℚ-vector space is annihilated by `cyclotomic d ℚ`
(for `0 < d`), then its trace is an integer.

This generalizes `trace_package_of_cyclotomic_prime_aeval_eq_zero`
(prime `p`) to any `d ≥ 1`.  The proof reuses the Module.AEval +
IsTorsionBy + quotient-field structure of the prime case, parameterised
on `Polynomial.cyclotomic.irreducible_rat`. -/
theorem trace_int_of_cyclotomic_aeval_eq_zero
    (d : ℕ) (hd : 0 < d)
    {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M)
    (hT : Polynomial.aeval T (Polynomial.cyclotomic d ℚ) = 0) :
    ∃ k : ℤ, LinearMap.trace ℚ M T = (k : ℚ) := by
  let instPoly : Module (Polynomial ℚ) (Module.AEval ℚ M T) :=
    Module.AEval.instModulePolynomial T
  letI : Module (Polynomial ℚ) (Module.AEval ℚ M T) := instPoly
  let instRat : Module ℚ (Module.AEval ℚ M T) := inferInstance
  letI : Module ℚ (Module.AEval ℚ M T) := instRat
  let P : Polynomial ℚ := Polynomial.cyclotomic d ℚ
  have htor : Module.IsTorsionBy (Polynomial ℚ) (Module.AEval ℚ M T) P := by
    intro x
    apply (Module.AEval.of ℚ M T).symm.injective
    rw [Module.AEval.of_symm_smul]
    change Polynomial.aeval T (Polynomial.cyclotomic d ℚ) _ = 0
    rw [hT]
    rfl
  haveI hmax : (Ideal.span ({P} : Set (Polynomial ℚ))).IsMaximal := by
    dsimp [P]
    exact PrincipalIdealRing.isMaximal_of_irreducible
      (Polynomial.cyclotomic.irreducible_rat hd)
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
    exact (Polynomial.cyclotomic.monic d ℚ).finite_quotient
  letI : Module.Finite ℚ A := instFiniteBase
  let instFree : Module.Free A (Module.AEval ℚ M T) :=
    @Module.Free.of_divisionRing A (Module.AEval ℚ M T)
      inferInstance inferInstance instQuot
  letI : Module.Free A (Module.AEval ℚ M T) := instFree
  let instFinite : Module.Finite A (Module.AEval ℚ M T) :=
    Module.Finite.of_restrictScalars_finite ℚ A (Module.AEval ℚ M T)
  letI : Module.Finite A (Module.AEval ℚ M T) := instFinite
  let gamma := Module.finrank A (Module.AEval ℚ M T)
  -- trace ℚ M T  =  γ • Algebra.trace ℚ A [X]
  let rootA : A :=
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
  have htrace_eq :
      _root_.LinearMap.trace ℚ M T =
        (gamma : ℚ) * Algebra.trace ℚ A rootA := by
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
      _ = (gamma : ℚ) * Algebra.trace ℚ A rootA := by
        dsimp [gamma]
  -- Algebra.trace ℚ A [X] ∈ ℤ
  obtain ⟨t, ht⟩ := trace_quotient_cyclotomic_X_isInt d hd
  refine ⟨gamma * t, ?_⟩
  rw [htrace_eq]
  -- rootA is exactly the quotient mk of X
  change (gamma : ℚ) * Algebra.trace ℚ A
    (Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial ℚ))) X) = _
  rw [ht]
  push_cast
  ring

end Moore57
