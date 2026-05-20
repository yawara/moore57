import Moore57.Foundations.LinearAlgebra.PowPrimeTrace
import Moore57.Foundations.GroupTheory.CyclotomicGenericTrace
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Order.SupIndep

/-!
# Trace of a finite-order linear endomorphism (composite order, Steps 1-4 partial)

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

## Step 4 (partial): trace decomposition over the direct sum

* `aeval_apply_comm_f` — `aeval f p (f v) = f (aeval f p v)` (any
  polynomial in `f` commutes with `f`, since the image of `ℚ[X]` in
  `Module.End ℚ W` is a commutative subring).
* `mapsTo_f_ker_aeval_cyclotomic` — `f` preserves each `ker(aeval f Φ_d)`.
* `trace_eq_sum_trace_restrict_ker_aeval_cyclotomic_divisors`
  (`[FiniteDimensional ℚ W]`) — `f^n = 1` (n > 0) ⟹
  `trace f = ∑_{d ∣ n} trace(f.restrict (ker(aeval f Φ_d)))`
  (Mathlib's `DirectSum.IsInternal.trace_eq_sum_trace_restrict`
  applied to Step 3 main).

## Future steps (deferred)

* Step 4 (full): per-block trace formula
  `trace(f.restrict ker(Φ_d)) = (dim(ker Φ_d) / φ(d)) · μ(d)`
  via ℚ(ζ_d)-module structure on each block.
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

/-! ### Step 4 (partial): trace decomposition over the direct sum -/

/-- **Polynomial-in-`f` commutes with `f`**: for any `p : ℚ[X]`,
`aeval f p` commutes with `f` (both are polynomials in `f`, and the
image of `ℚ[X]` in `Module.End ℚ W` is a commutative subring). -/
lemma aeval_apply_comm_f (f : W →ₗ[ℚ] W) (p : ℚ[X]) (v : W) :
    Polynomial.aeval f p (f v) = f (Polynomial.aeval f p v) := by
  have h1 :
      Polynomial.aeval f p (f v)
        = Polynomial.aeval f (p * Polynomial.X) v := by
    rw [map_mul, Polynomial.aeval_X]
    rfl
  have h2 :
      Polynomial.aeval f (Polynomial.X * p) v = f (Polynomial.aeval f p v) := by
    rw [map_mul, Polynomial.aeval_X]
    rfl
  rw [h1, mul_comm, h2]

/-- **B4.3 Step 4 helper**: `f` preserves the kernel of `aeval f Φ_d`. -/
lemma mapsTo_f_ker_aeval_cyclotomic (f : W →ₗ[ℚ] W) (d : ℕ) :
    Set.MapsTo f
      (LinearMap.ker (Polynomial.aeval f (Polynomial.cyclotomic d ℚ)) : Set W)
      (LinearMap.ker (Polynomial.aeval f (Polynomial.cyclotomic d ℚ)) : Set W) := by
  intro x hx
  simp only [SetLike.mem_coe, LinearMap.mem_ker] at hx ⊢
  rw [aeval_apply_comm_f, hx, map_zero]

/-- **B4.3 Step 4 main**: `f^n = 1` (n > 0) ⟹ the trace of `f`
decomposes as a sum over divisors `d ∣ n` of the per-block traces of
the restrictions `f|_{ker(aeval f Φ_d)}`.

This is the structural input for the Möbius-weighted trace formula
(Step 4 full): each per-block trace will turn out to equal
`(dim(ker Φ_d) / φ(d)) · μ(d) ∈ ℤ`. -/
theorem trace_eq_sum_trace_restrict_ker_aeval_cyclotomic_divisors
    [FiniteDimensional ℚ W]
    (f : W →ₗ[ℚ] W) {n : ℕ} (hn : 0 < n) (hf : f ^ n = 1) :
    LinearMap.trace ℚ W f =
      ∑ d : (Nat.divisors n : Finset ℕ),
        LinearMap.trace ℚ _
          (f.restrict (mapsTo_f_ker_aeval_cyclotomic f d.val)) := by
  exact _root_.LinearMap.trace_eq_sum_trace_restrict
    (isInternal_ker_aeval_cyclotomic_divisors f hn hf)
    (fun d => mapsTo_f_ker_aeval_cyclotomic f d.val)

/-! ### Step 4 (full): per-block trace is an integer ⟹ total trace is an integer -/

/-- Generic `aeval`-restriction commutativity: for any polynomial `p`,
applying `aeval (f.restrict) p` and then coercing to `W` matches
`aeval f p` applied to the coerced argument. -/
theorem aeval_restrict_apply
    (f : W →ₗ[ℚ] W) (S : Submodule ℚ W)
    (hmaps : Set.MapsTo f S S) (p : ℚ[X]) (v : S) :
    (Polynomial.aeval (f.restrict hmaps) p v : W) =
      Polynomial.aeval f p (v : W) := by
  rw [Polynomial.aeval_endomorphism, Polynomial.aeval_endomorphism]
  -- Expand the `Polynomial.sum` on both sides as Finset sums, then push `(↑·)` inside.
  rw [Polynomial.sum_def, Polynomial.sum_def, Submodule.coe_sum]
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [Submodule.coe_smul]
  congr 1
  exact restrict_pow_apply f S hmaps n v

/-- `aeval (f.restrict mapsTo) (cyclotomic d ℚ) = 0`: the restriction of
`f` to its `(aeval f Φ_d)`-kernel is annihilated by `cyclotomic d ℚ`. -/
theorem aeval_cyclotomic_f_restrict_eq_zero
    (f : W →ₗ[ℚ] W) (d : ℕ) :
    Polynomial.aeval
        (f.restrict (mapsTo_f_ker_aeval_cyclotomic f d))
        (Polynomial.cyclotomic d ℚ) = 0 := by
  apply LinearMap.ext
  intro ⟨v, hv⟩
  have heq := aeval_restrict_apply f _
    (mapsTo_f_ker_aeval_cyclotomic f d) (Polynomial.cyclotomic d ℚ) ⟨v, hv⟩
  apply Subtype.val_injective
  simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero]
  rw [heq]
  exact hv

/-- **B4.3 Step 4 full (per-block)**: for each `d ∣ n` with `0 < d`, the
trace of `f.restrict (mapsTo to ker(aeval f Φ_d))` is an integer.

For `d = 0` we get the trivial case from `cyclotomic 0 ℚ = 1`
(annihilation forces the underlying module to be zero, hence trace zero). -/
theorem trace_restrict_ker_aeval_cyclotomic_isInt
    [FiniteDimensional ℚ W]
    (f : W →ₗ[ℚ] W) {d : ℕ} (hd : 0 < d) :
    ∃ k : ℤ, LinearMap.trace ℚ _
        (f.restrict (mapsTo_f_ker_aeval_cyclotomic f d)) = (k : ℚ) := by
  apply Moore57.trace_int_of_cyclotomic_aeval_eq_zero d hd
  exact aeval_cyclotomic_f_restrict_eq_zero f d

/-- **B4.3 Step 4 full (main)**: `f^n = 1` with `n > 0` ⟹
`LinearMap.trace ℚ W f` is a rational-integer.

This is the composite-order generalization of B4.1's
`exists_int_trace_of_pow_prime_eq_one`.  The proof combines:
* Step 4 partial: trace `f` decomposes as sum over `d ∣ n` of per-block traces.
* Step 4 full (per-block): each per-block trace is an integer
  (`trace_int_of_cyclotomic_aeval_eq_zero` from
  `CyclotomicGenericTrace.lean`).
* Sum of integers is an integer. -/
theorem trace_int_of_pow_eq_one
    [FiniteDimensional ℚ W]
    (f : W →ₗ[ℚ] W) {n : ℕ} (hn : 0 < n) (hf : f ^ n = 1) :
    ∃ k : ℤ, LinearMap.trace ℚ W f = (k : ℚ) := by
  classical
  rw [trace_eq_sum_trace_restrict_ker_aeval_cyclotomic_divisors f hn hf]
  -- Each summand is an integer (via Step 4 per-block), so the sum is an integer.
  have hper : ∀ d : (Nat.divisors n : Finset ℕ),
      ∃ k : ℤ, LinearMap.trace ℚ _
          (f.restrict (mapsTo_f_ker_aeval_cyclotomic f d.val)) = (k : ℚ) := by
    intro ⟨d, hd⟩
    have hpos : 0 < d := Nat.pos_of_mem_divisors hd
    exact trace_restrict_ker_aeval_cyclotomic_isInt f hpos
  -- Choose integers per index and sum them.
  choose ks hks using hper
  refine ⟨∑ d, ks d, ?_⟩
  push_cast
  exact Finset.sum_congr rfl (fun d _ => hks d)

end

end LinearMap

end Moore57
