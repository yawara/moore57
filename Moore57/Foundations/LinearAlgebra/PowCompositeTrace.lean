import Moore57.Foundations.LinearAlgebra.PowPrimeTrace
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Order.SupIndep

/-!
# Trace of a finite-order linear endomorphism (composite order, Steps 1-3 done)

**Roadmap [B4.3] composite-order Galois cyclotomic decomp** — gradual
build-out.  This module generalizes `Foundations/LinearAlgebra/PowPrimeTrace.lean`
(prime-order trace integrality) toward arbitrary `f^n = 1` (composite `n`).

The main result `exists_int_trace_of_pow_eq_one` (proved in a later step)
will state that any `f : W →ₗ[ℚ] W` with `f^n = 1` (n > 0) has integer
trace.  The strategy follows the classical Galois–Möbius argument:

* `X^n - 1 = ∏_{d ∣ n} Φ_d(X)` (cyclotomic decomposition,
  `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`).
* Hence `aeval f (X^n - 1) = f^n - 1 = 0`.
* Generalized eigenspace decomposition: `W = ⊕_{d ∣ n} ker(Φ_d(f))`
  (each block is `f`-invariant, by CRT on `ℚ[X] / (X^n - 1)`).
* Trace on each `ker(Φ_d(f))`-block equals `μ(d) · γ_d` where `γ_d` is
  the block's multiplicity and `μ` is the Möbius function (sum of
  primitive `d`-th roots of unity).
* Total trace = `Σ_{d ∣ n} μ(d) · γ_d ∈ ℤ`.

## Step 1: the basic annihilation lemma

* `aeval_X_pow_sub_one_eq_zero` — `f^n = 1` ⟹ `aeval f (X^n - 1) = 0`.
* `aeval_prod_cyclotomic_eq_zero` — `f^n = 1` ⟹ `aeval f (∏_{d ∣ n} Φ_d) = 0`.

## Step 2: kernel sum decomposition

* `sup_ker_aeval_cyclotomic_eq_ker_aeval_prod` — for any finite set
  `s ⊆ ℕ`, `⨆ d ∈ s, ker(aeval f Φ_d) = ker(aeval f (∏_{d ∈ s} Φ_d))`
  (pairwise cyclotomic coprimality + `sup_ker_aeval_eq_ker_aeval_mul_of_coprime`).
* `sup_ker_aeval_cyclotomic_divisors_eq_top` — `f^n = 1` (n > 0) ⟹
  `⨆_{d ∣ n} ker(aeval f Φ_d) = ⊤` (kernels span `W`).

## Step 3: pairwise disjointness ⟹ internal direct sum

* `disjoint_ker_aeval_cyclotomic_iSup_of_not_mem` — for `a ∉ s`,
  `Disjoint (ker(aeval f Φ_a)) (⨆ d ∈ s, ker(aeval f Φ_d))` (Step 2
  + Mathlib's `disjoint_ker_aeval_of_isCoprime`).
* `supIndep_ker_aeval_cyclotomic` — `s.SupIndep (fun d => ker(aeval f Φ_d))`
  for any `s : Finset ℕ` (the disjoint helper packaged as a
  `Finset.SupIndep`).
* `iSupIndep_ker_aeval_cyclotomic_divisors` — `iSupIndep` form of the
  cyclotomic-kernel family, indexed by `↑(Nat.divisors n)`.
* `isInternal_ker_aeval_cyclotomic_divisors` — `f^n = 1` (n > 0) ⟹
  `DirectSum.IsInternal` for the family `(ker(aeval f Φ_d))_{d ∣ n}`
  (Mathlib's `isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`).

## Future steps (deferred)

* Step 4: per-block trace formula = `μ(d) · γ_d`.
* Step 5: specialise to `n = 25` for the Lemma 13 `p = 5` starred rows.
* Step 6: apply via `Moore57Graph/Aut/TraceIntegrality.lean` and close
  `lem13_starred_row_5_*_no_integer_trace`.
-/

namespace Moore57

namespace LinearMap

noncomputable section

open Polynomial

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- For `f : W →ₗ[ℚ] W` with `f^n = 1`,
`Polynomial.aeval f (X^n - 1) = 0`. -/
theorem aeval_X_pow_sub_one_eq_zero
    (f : W →ₗ[ℚ] W) {n : ℕ} (hf : f ^ n = 1) :
    Polynomial.aeval f (X ^ n - 1 : ℚ[X]) = 0 := by
  rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hf, sub_self]

/-- Equivalent reformulation: `f^n = 1` ⟹ `f` satisfies the polynomial
`X^n - 1`.  The polynomial decomposition
`X^n - 1 = ∏_{d ∣ n} Φ_d(X)` (Mathlib's
`Polynomial.prod_cyclotomic_eq_X_pow_sub_one`) will then route the
analysis through the cyclotomic factors. -/
theorem aeval_prod_cyclotomic_eq_zero
    (f : W →ₗ[ℚ] W) {n : ℕ} (hn : 0 < n) (hf : f ^ n = 1) :
    Polynomial.aeval f
        (∏ d ∈ Nat.divisors n, Polynomial.cyclotomic d ℚ) = 0 := by
  rw [Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℚ]
  exact aeval_X_pow_sub_one_eq_zero f hf

/-! ### Step 2: kernel sum decomposition over divisors of `n` -/

/-- **B4.3 Step 2 helper**: For any `Finset ℕ`, the supremum of the kernels of
`aeval f (cyclotomic d ℚ)` over `d ∈ s` equals the kernel of `aeval f`
applied to the product `∏ d ∈ s, cyclotomic d ℚ`.

Proof: Finset induction on `s`.  The inductive step uses pairwise
coprimality of cyclotomic polynomials over `ℚ`
(`Polynomial.cyclotomic.isCoprime_rat`) and the kernel-product splitting
`Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime`. -/
theorem sup_ker_aeval_cyclotomic_eq_ker_aeval_prod
    (f : W →ₗ[ℚ] W) (s : Finset ℕ) :
    (⨆ d ∈ s, LinearMap.ker (Polynomial.aeval f (Polynomial.cyclotomic d ℚ))) =
      LinearMap.ker (Polynomial.aeval f (∏ d ∈ s, Polynomial.cyclotomic d ℚ)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Module.End.one_eq_id, LinearMap.ker_id]
  | insert a s' ha ih =>
      rw [Finset.prod_insert ha, Finset.iSup_insert]
      have hcop :
          IsCoprime (Polynomial.cyclotomic a ℚ)
            (∏ d ∈ s', Polynomial.cyclotomic d ℚ) := by
        refine IsCoprime.prod_right ?_
        intro d hd
        exact Polynomial.cyclotomic.isCoprime_rat
          (fun heq => ha (heq ▸ hd))
      rw [← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop, ih]

/-- **B4.3 Step 2 main**: If `f^n = 1` with `n > 0`, then the kernels of
`aeval f (cyclotomic d ℚ)` for `d ∣ n` span all of `W`.

This is the "kernels span" half of the generalized eigenspace
decomposition `W = ⨁_{d ∣ n} ker(aeval f Φ_d)`.  The complementary
"kernels are disjoint" half (Step 3) plus the per-block trace formula
(Step 4) close out the cyclotomic trace argument. -/
theorem sup_ker_aeval_cyclotomic_divisors_eq_top
    (f : W →ₗ[ℚ] W) {n : ℕ} (hn : 0 < n) (hf : f ^ n = 1) :
    (⨆ d ∈ Nat.divisors n,
        LinearMap.ker (Polynomial.aeval f (Polynomial.cyclotomic d ℚ))) = ⊤ := by
  rw [sup_ker_aeval_cyclotomic_eq_ker_aeval_prod f (Nat.divisors n),
      Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℚ,
      aeval_X_pow_sub_one_eq_zero f hf, LinearMap.ker_zero]

/-! ### Step 3: pairwise disjointness ⟹ internal direct sum -/

/-- **B4.3 Step 3 helper**: For `a ∉ s`, the kernel of `aeval f Φ_a` is
disjoint from the supremum of the kernels of `aeval f Φ_d` for `d ∈ s`. -/
theorem disjoint_ker_aeval_cyclotomic_iSup_of_not_mem
    (f : W →ₗ[ℚ] W) {a : ℕ} {s : Finset ℕ} (ha : a ∉ s) :
    Disjoint (LinearMap.ker (Polynomial.aeval f (Polynomial.cyclotomic a ℚ)))
      (⨆ d ∈ s, LinearMap.ker (Polynomial.aeval f (Polynomial.cyclotomic d ℚ))) := by
  rw [sup_ker_aeval_cyclotomic_eq_ker_aeval_prod f s]
  refine Polynomial.disjoint_ker_aeval_of_isCoprime f ?_
  refine IsCoprime.prod_right ?_
  intro d hd
  exact Polynomial.cyclotomic.isCoprime_rat (fun heq => ha (heq ▸ hd))

/-- **Finset-`SupIndep` packaging**: for any `Finset ℕ`, the family
`(ker(aeval f Φ_d))_{d ∈ s}` is independent in the Finset sense. -/
theorem supIndep_ker_aeval_cyclotomic
    (f : W →ₗ[ℚ] W) (s : Finset ℕ) :
    s.SupIndep
      (fun d : ℕ => LinearMap.ker (Polynomial.aeval f (Polynomial.cyclotomic d ℚ))) := by
  classical
  rw [Finset.supIndep_iff_disjoint_erase]
  intro d _hd
  rw [Finset.sup_eq_iSup]
  exact disjoint_ker_aeval_cyclotomic_iSup_of_not_mem f (Finset.notMem_erase _ _)

/-- **B4.3 Step 3 (iSupIndep form)**: the cyclotomic-kernel family
`(ker(aeval f Φ_d))_{d ∣ n}` is independent in the complete-lattice
sense, indexed by the subtype `↑(Nat.divisors n)`. -/
theorem iSupIndep_ker_aeval_cyclotomic_divisors
    (f : W →ₗ[ℚ] W) (n : ℕ) :
    iSupIndep (fun d : (Nat.divisors n : Finset ℕ) =>
      LinearMap.ker (Polynomial.aeval f (Polynomial.cyclotomic d.val ℚ))) := by
  classical
  exact (supIndep_ker_aeval_cyclotomic f (Nat.divisors n)).independent

/-- **B4.3 Step 3 main**: `f^n = 1` (n > 0) ⟹ the cyclotomic-kernel
family `(ker(aeval f Φ_d))_{d ∣ n}` forms an internal direct sum
decomposition of `W`. -/
theorem isInternal_ker_aeval_cyclotomic_divisors
    (f : W →ₗ[ℚ] W) {n : ℕ} (hn : 0 < n) (hf : f ^ n = 1) :
    DirectSum.IsInternal
      (fun d : (Nat.divisors n : Finset ℕ) =>
        LinearMap.ker (Polynomial.aeval f (Polynomial.cyclotomic d.val ℚ))) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨iSupIndep_ker_aeval_cyclotomic_divisors f n, ?_⟩
  rw [show (⨆ d : (Nat.divisors n : Finset ℕ),
        LinearMap.ker (Polynomial.aeval f (Polynomial.cyclotomic d.val ℚ))) =
        (⨆ d ∈ Nat.divisors n,
          LinearMap.ker (Polynomial.aeval f (Polynomial.cyclotomic d ℚ))) from
      iSup_subtype]
  exact sup_ker_aeval_cyclotomic_divisors_eq_top f hn hf

end

end LinearMap

end Moore57
