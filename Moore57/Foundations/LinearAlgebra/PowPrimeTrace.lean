import Moore57.Foundations.LinearAlgebra.ProjectionTrace
import Moore57.Foundations.GroupTheory.CyclotomicPrimeTrace
import Mathlib.Tactic

/-!
# Trace of a finite-order linear endomorphism (prime order)

This module generalizes `exists_int_trace_of_involutive`
(`Foundations/LinearAlgebra/InvolutionTrace.lean`) from order-2 to
prime-order linear endomorphisms over `ℚ`.

The key facts:

* The "averaging" element `s := 1 + f + f² + ⋯ + f^{p-1}` satisfies
  `s² = p · s` when `f^p = 1`, so `s / p` is an idempotent projector.
* The projector projects onto `ker(f - 1)` (the fixed subspace).
* The projector commutes with `f`.
* The kernel of the projector is annihilated by the `p`-th cyclotomic
  polynomial `Φ_p(x) = 1 + x + … + x^{p-1}` (for `p` prime).
* Hence by the cyclotomic-block trace formula
  `trace_package_of_cyclotomic_prime_aeval_eq_zero`, the trace on the
  kernel equals `-γ` where the kernel has rational dimension `(p-1)·γ`.
* Total trace = `dim(fix) - γ ∈ ℤ`.

The main result `exists_int_trace_of_pow_prime_eq_one` provides the
existence of an integer trace given `f^p = 1`.
-/

namespace Moore57

namespace LinearMap

noncomputable section

open Polynomial

variable {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]

/-- The cyclic averaging element `s = 1 + f + f² + ⋯ + f^{p-1}`. -/
def cyclicSum (f : W →ₗ[ℚ] W) (p : ℕ) : W →ₗ[ℚ] W :=
  ∑ i ∈ Finset.range p, f ^ i

/-- The cyclic projection `s / p`, used when `f^p = 1` to project onto
the fixed subspace `ker(f - 1)`. -/
def cyclicProjection (f : W →ₗ[ℚ] W) (p : ℕ) : W →ₗ[ℚ] W :=
  ((p : ℚ)⁻¹ : ℚ) • cyclicSum f p

omit [FiniteDimensional ℚ W] in
/-- `(f - 1) · s = 0` (i.e. `f · s = s`) when `f^p = 1`.

Uses `mul_geom_sum` to rewrite the LHS as `f^p - 1`. -/
theorem sub_one_mul_cyclicSum
    (f : W →ₗ[ℚ] W) {p : ℕ} (hf : f ^ p = 1) :
    (f - 1) * cyclicSum f p = 0 := by
  unfold cyclicSum
  -- mul_geom_sum (x - 1) * ∑ x^i = x^n - 1
  have h := mul_geom_sum (R := W →ₗ[ℚ] W) f p
  rw [h, hf, sub_self]

omit [FiniteDimensional ℚ W] in
/-- `f · s = s` when `f^p = 1`. -/
theorem f_mul_cyclicSum
    (f : W →ₗ[ℚ] W) {p : ℕ} (hf : f ^ p = 1) :
    f * cyclicSum f p = cyclicSum f p := by
  have h := sub_one_mul_cyclicSum f hf
  rw [sub_mul, one_mul] at h
  exact sub_eq_zero.mp h

omit [FiniteDimensional ℚ W] in
/-- `s · f = s` (right side multiplication; uses `cyclicSum` commutes with `f`
since it's a polynomial in `f`). -/
theorem cyclicSum_mul_f
    (f : W →ₗ[ℚ] W) {p : ℕ} (hf : f ^ p = 1) :
    cyclicSum f p * f = cyclicSum f p := by
  have h := geom_sum_mul (R := W →ₗ[ℚ] W) f p
  -- h : (∑ i ∈ range p, f ^ i) * (f - 1) = f^p - 1
  unfold cyclicSum
  rw [hf, sub_self] at h
  rw [mul_sub, mul_one] at h
  exact sub_eq_zero.mp h

omit [FiniteDimensional ℚ W] in
/-- Each `s · f^i = s` when `f^p = 1` and `0 ≤ i`. -/
theorem cyclicSum_mul_pow
    (f : W →ₗ[ℚ] W) {p : ℕ} (hf : f ^ p = 1) (i : ℕ) :
    cyclicSum f p * f ^ i = cyclicSum f p := by
  induction i with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, cyclicSum_mul_f f hf]

omit [FiniteDimensional ℚ W] in
/-- `s² = p · s` when `f^p = 1`. -/
theorem cyclicSum_sq
    (f : W →ₗ[ℚ] W) {p : ℕ} (hf : f ^ p = 1) :
    cyclicSum f p * cyclicSum f p = (p : ℚ) • cyclicSum f p := by
  -- Expand the second factor (keep first factor as `cyclicSum f p`).
  have hexpand : cyclicSum f p * cyclicSum f p =
      ∑ i ∈ Finset.range p, cyclicSum f p * f ^ i := by
    rw [show cyclicSum f p = ∑ i ∈ Finset.range p, f ^ i from rfl,
        Finset.mul_sum]
  rw [hexpand]
  -- ∑ i, s * f^i = ∑ i, s
  have hsum :
      (∑ i ∈ Finset.range p, cyclicSum f p * f ^ i) =
        ∑ _ ∈ Finset.range p, cyclicSum f p :=
    Finset.sum_congr rfl (fun i _ => cyclicSum_mul_pow f hf i)
  rw [hsum, Finset.sum_const, Finset.card_range]
  -- p • s = (p : ℚ) • s
  exact (Nat.cast_smul_eq_nsmul (R := ℚ) p (cyclicSum f p)).symm

omit [FiniteDimensional ℚ W] in
/-- `cyclicProjection f p` is idempotent when `f^p = 1` and `p ≥ 1`. -/
theorem cyclicProjection_isIdempotentElem
    (f : W →ₗ[ℚ] W) {p : ℕ} (hp : 0 < p) (hf : f ^ p = 1) :
    IsIdempotentElem (cyclicProjection f p) := by
  rw [IsIdempotentElem]
  unfold cyclicProjection
  rw [smul_mul_smul_comm, cyclicSum_sq f hf]
  -- ((p⁻¹ * p⁻¹) : ℚ) • ((p : ℚ) • s) = (p⁻¹ : ℚ) • s
  rw [smul_smul]
  have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  congr 1
  field_simp

omit [FiniteDimensional ℚ W] in
/-- `f · cyclicProjection = cyclicProjection`.

Direct consequence of `f · cyclicSum = cyclicSum`. -/
theorem f_mul_cyclicProjection
    (f : W →ₗ[ℚ] W) {p : ℕ} (hf : f ^ p = 1) :
    f * cyclicProjection f p = cyclicProjection f p := by
  unfold cyclicProjection
  rw [mul_smul_comm, f_mul_cyclicSum f hf]

omit [FiniteDimensional ℚ W] in
/-- `cyclicProjection · f = cyclicProjection`. -/
theorem cyclicProjection_mul_f
    (f : W →ₗ[ℚ] W) {p : ℕ} (hf : f ^ p = 1) :
    cyclicProjection f p * f = cyclicProjection f p := by
  unfold cyclicProjection
  rw [smul_mul_assoc, cyclicSum_mul_f f hf]

omit [FiniteDimensional ℚ W] in
/-- `cyclicProjection f p` commutes with `f`. -/
theorem cyclicProjection_commute_f
    (f : W →ₗ[ℚ] W) {p : ℕ} (hf : f ^ p = 1) :
    Commute (cyclicProjection f p) f := by
  unfold Commute SemiconjBy
  rw [cyclicProjection_mul_f f hf, f_mul_cyclicProjection f hf]

omit [FiniteDimensional ℚ W] in
/-- For `f^p = 1` and `p ≥ 1`, `cyclicProjection f p ∘ f = cyclicProjection f p`.
LinearMap `comp` version of `cyclicProjection_mul_f`. -/
theorem cyclicProjection_comp_f
    (f : W →ₗ[ℚ] W) {p : ℕ} (hf : f ^ p = 1) :
    cyclicProjection f p ∘ₗ f = cyclicProjection f p := by
  exact cyclicProjection_mul_f f hf

/-! ### Trace formula

We use the fact that the projector `cyclicProjection f p` is idempotent,
commutes with `f`, and satisfies `cyclicProjection ∘ f = cyclicProjection`,
so `trace(f|_{range proj}) = trace(proj)` via the projection-trace lemma.

Combined with the trace decomposition over `W = range ⊕ ker`, and the
kernel block being annihilated by `cyclicSum = cyclotomic_p` (for prime
`p`), we get `trace(f) ∈ ℤ`. -/

/-- The maps-to property: `f` maps `range (cyclicProjection f p)` into itself. -/
theorem cyclicProjection_range_invariant
    (f : W →ₗ[ℚ] W) {p : ℕ} (hp : 0 < p) (hf : f ^ p = 1) :
    Set.MapsTo f (_root_.LinearMap.range (cyclicProjection f p))
      (_root_.LinearMap.range (cyclicProjection f p)) := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, ?_⟩
  have h := f_mul_cyclicProjection f hf
  have hfxx := congrArg (fun g : W →ₗ[ℚ] W => g y) h
  change f (cyclicProjection f p y) = cyclicProjection f p y at hfxx
  rw [hy] at hfxx
  -- hfxx : f x = x
  exact hy.trans hfxx.symm

omit [FiniteDimensional ℚ W] in
/-- `f` acts as the identity on `range (cyclicProjection f p)`.

For `v ∈ range(proj)`, we have `v = proj w` for some `w`, then
`f v = f (proj w) = (f * proj) w = proj w = v`. -/
theorem f_eq_id_on_cyclicProjection_range
    (f : W →ₗ[ℚ] W) {p : ℕ} (hf : f ^ p = 1)
    {v : W} (hv : v ∈ _root_.LinearMap.range (cyclicProjection f p)) :
    f v = v := by
  obtain ⟨w, hw⟩ := hv
  have h := f_mul_cyclicProjection f hf
  have := congrArg (fun g : W →ₗ[ℚ] W => g w) h
  change f (cyclicProjection f p w) = cyclicProjection f p w at this
  rw [hw] at this
  exact this

/-- The trace of `f` restricted to `range (cyclicProjection f p)` equals
the dimension of that range. -/
theorem trace_f_restrict_cyclicProjection_range
    (f : W →ₗ[ℚ] W) {p : ℕ} (hp : 0 < p) (hf : f ^ p = 1) :
    _root_.LinearMap.trace ℚ (_root_.LinearMap.range (cyclicProjection f p))
      (f.restrict (cyclicProjection_range_invariant f hp hf)) =
        (Module.finrank ℚ (_root_.LinearMap.range (cyclicProjection f p)) : ℚ) := by
  -- f restricted to range(proj) is the identity.
  have hid :
      f.restrict (cyclicProjection_range_invariant f hp hf) =
        (1 : _root_.LinearMap.range (cyclicProjection f p) →ₗ[ℚ]
              _root_.LinearMap.range (cyclicProjection f p)) := by
    ext ⟨v, hv⟩
    change f v = v
    exact f_eq_id_on_cyclicProjection_range f hf hv
  rw [hid, _root_.LinearMap.trace_one]

/-! ### Kernel-side characterization

The kernel of `cyclicProjection f p` is exactly `ker (cyclicSum f p)`
(since `p ≠ 0`).  For `p` prime, `cyclicSum f p = aeval f (cyclotomic p ℚ)`
(geometric sum identification). -/

omit [FiniteDimensional ℚ W] in
/-- The kernel of `cyclicProjection` equals the kernel of `cyclicSum`. -/
theorem ker_cyclicProjection_eq_ker_cyclicSum
    (f : W →ₗ[ℚ] W) {p : ℕ} (hp : 0 < p) :
    _root_.LinearMap.ker (cyclicProjection f p) =
      _root_.LinearMap.ker (cyclicSum f p) := by
  unfold cyclicProjection
  have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hinv_ne : (p : ℚ)⁻¹ ≠ 0 := inv_ne_zero hp_ne
  ext v
  simp only [_root_.LinearMap.mem_ker, _root_.LinearMap.smul_apply, smul_eq_zero]
  exact ⟨fun h => h.resolve_left hinv_ne, fun h => Or.inr h⟩

omit [FiniteDimensional ℚ W] in
/-- `f` maps `ker (cyclicProjection f p)` into itself. -/
theorem cyclicProjection_ker_invariant
    (f : W →ₗ[ℚ] W) {p : ℕ} (hp : 0 < p) (hf : f ^ p = 1) :
    Set.MapsTo f (_root_.LinearMap.ker (cyclicProjection f p))
      (_root_.LinearMap.ker (cyclicProjection f p)) := by
  intro v hv
  rw [ker_cyclicProjection_eq_ker_cyclicSum f hp] at hv ⊢
  rw [SetLike.mem_coe, _root_.LinearMap.mem_ker] at hv ⊢
  have h := cyclicSum_mul_f f hf
  have hcong := congrArg (fun g : W →ₗ[ℚ] W => g v) h
  change cyclicSum f p (f v) = cyclicSum f p v at hcong
  rw [hcong, hv]

omit [FiniteDimensional ℚ W] in
/-- `cyclicSum f p = aeval f (cyclotomic p ℚ)` for `p` prime. -/
theorem cyclicSum_eq_aeval_cyclotomic
    (f : W →ₗ[ℚ] W) (p : ℕ) [Fact (Nat.Prime p)] :
    cyclicSum f p = Polynomial.aeval f (Polynomial.cyclotomic p ℚ) := by
  unfold cyclicSum
  rw [cyclotomic_prime_rat_eq_geom_sum, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_pow, Polynomial.aeval_X]

omit [FiniteDimensional ℚ W] in
/-- Auxiliary: pow on restricted map matches pow on original. -/
theorem restrict_pow_apply
    (f : W →ₗ[ℚ] W) (S : Submodule ℚ W)
    (hmaps : Set.MapsTo f S S) (n : ℕ) (v : S) :
    (((f.restrict hmaps) ^ n) v : W) = (f ^ n) (v : W) := by
  induction n generalizing v with
  | zero =>
      change ((1 : S →ₗ[ℚ] S) v : W) = (1 : W →ₗ[ℚ] W) (v : W)
      simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      change ((((f.restrict hmaps) ^ k) * f.restrict hmaps) v : W) =
        ((f ^ k) * f) (v : W)
      rw [Module.End.mul_apply, Module.End.mul_apply]
      change ((((f.restrict hmaps) ^ k) ((f.restrict hmaps) v)) : W) =
        (f ^ k) (f (v : W))
      have hres : ((f.restrict hmaps) v : W) = f (v : W) := by
        have h := _root_.LinearMap.restrict_apply hmaps v
        exact congrArg Subtype.val h
      rw [ih ((f.restrict hmaps) v), hres]

omit [FiniteDimensional ℚ W] in
/-- `cyclicSum (f.restrict h)` applied to `v` matches `cyclicSum f` on the
underlying vector. -/
theorem cyclicSum_restrict_apply
    (f : W →ₗ[ℚ] W) (S : Submodule ℚ W)
    (hmaps : Set.MapsTo f S S) (p : ℕ) (v : S) :
    (cyclicSum (f.restrict hmaps) p v : W) = cyclicSum f p (v : W) := by
  unfold cyclicSum
  rw [_root_.LinearMap.coe_sum, _root_.LinearMap.coe_sum]
  rw [Finset.sum_apply, Finset.sum_apply]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact restrict_pow_apply f S hmaps i v

/-- `aeval (f.restrict ker) (cyclotomic p ℚ) = 0` for `f^p = 1`, `p` prime. -/
theorem aeval_cyclotomic_f_restrict_ker_eq_zero
    (f : W →ₗ[ℚ] W) {p : ℕ} [Fact (Nat.Prime p)] (hp : 0 < p) (hf : f ^ p = 1) :
    Polynomial.aeval
        (f.restrict (cyclicProjection_ker_invariant f hp hf))
        (Polynomial.cyclotomic p ℚ) = 0 := by
  -- Rewrite aeval cyclotomic_p = cyclicSum on both sides.
  rw [← cyclicSum_eq_aeval_cyclotomic]
  ext ⟨v, hv⟩
  have hv' : cyclicSum f p v = 0 := by
    rw [ker_cyclicProjection_eq_ker_cyclicSum f hp] at hv
    rwa [_root_.LinearMap.mem_ker] at hv
  -- Goal: ↑(cyclicSum (f.restrict) p ⟨v, hv⟩) = ↑(0 ⟨v, hv⟩)
  rw [cyclicSum_restrict_apply f _ (cyclicProjection_ker_invariant f hp hf) p ⟨v, hv⟩]
  change cyclicSum f p v = ↑((0 : _root_.LinearMap.ker (cyclicProjection f p) →ₗ[ℚ]
        _root_.LinearMap.ker (cyclicProjection f p)) ⟨v, hv⟩)
  rw [hv']
  rfl

/-! ### Main result: integer trace for finite prime-order endomorphisms -/

/-- **Main result**: For a `ℚ`-linear endomorphism `f` of order `p` prime
(`f^p = 1`), the trace of `f` is an integer.

Proof: decompose `W = range proj ⊕ ker proj` where `proj = cyclicProjection f p`.

* On `range proj`: `f` acts as the identity, trace = `dim(range proj)`.
* On `ker proj`: `f` is annihilated by `cyclotomic p ℚ`, so by
  `trace_package_of_cyclotomic_prime_aeval_eq_zero`, trace = `-γ`
  where `dim(ker proj) = (p-1) · γ`.

Total: `trace f = dim(range proj) - γ ∈ ℤ`. -/
theorem exists_int_trace_of_pow_prime_eq_one
    (f : W →ₗ[ℚ] W) (p : ℕ) [Fact (Nat.Prime p)] (hf : f ^ p = 1) :
    ∃ z : ℤ, _root_.LinearMap.trace ℚ W f = (z : ℚ) := by
  classical
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  -- Set up the direct sum decomposition Bool → Submodule via cyclicProjection.
  let p_proj := cyclicProjection f p
  have hidem : IsIdempotentElem p_proj := cyclicProjection_isIdempotentElem f hp hf
  -- IsCompl range and ker.
  have hcompl : IsCompl (_root_.LinearMap.range p_proj) (_root_.LinearMap.ker p_proj) :=
    _root_.LinearMap.IsIdempotentElem.isCompl hidem
  -- IsInternal of Bool-indexed family.
  let N : Bool → Submodule ℚ W :=
    fun b => if b then _root_.LinearMap.ker p_proj else _root_.LinearMap.range p_proj
  have hInternal : DirectSum.IsInternal N := by
    refine (DirectSum.isInternal_submodule_iff_isCompl N (i := false) (j := true)
      (by decide) (by ext b; cases b <;> simp [N])).mpr ?_
    exact hcompl
  -- f maps each component to itself.
  have hmaps : ∀ b, Set.MapsTo f (N b) (N b) := by
    intro b
    cases b
    · exact cyclicProjection_range_invariant f hp hf
    · exact cyclicProjection_ker_invariant f hp hf
  -- Trace decomposition.
  have htrace_decomp :=
    _root_.LinearMap.trace_eq_sum_trace_restrict hInternal hmaps
  -- trace = trace_false + trace_true = trace_range + trace_ker.
  rw [Fintype.sum_bool] at htrace_decomp
  -- trace on range: f acts as id, trace = dim(range).
  have htrace_range : _root_.LinearMap.trace ℚ (N false)
      (f.restrict (hmaps false)) = (Module.finrank ℚ (N false) : ℚ) := by
    have hid : f.restrict (hmaps false) = (1 : N false →ₗ[ℚ] N false) := by
      ext ⟨v, hv⟩
      change f v = v
      simp only [N] at hv
      exact f_eq_id_on_cyclicProjection_range f hf hv
    rw [hid, _root_.LinearMap.trace_one]
  -- trace on ker: via trace_package_of_cyclotomic_prime_aeval_eq_zero.
  have hker_aeval : Polynomial.aeval (f.restrict (hmaps true))
      (Polynomial.cyclotomic p ℚ) = 0 := by
    convert aeval_cyclotomic_f_restrict_ker_eq_zero f hp hf using 1
  -- Now apply trace_package on the kernel component.
  obtain ⟨γ, hdim_eq, htrace_eq⟩ :=
    trace_package_of_cyclotomic_prime_aeval_eq_zero p
      (f.restrict (hmaps true)) hker_aeval
  -- Construct integer.
  refine ⟨(Module.finrank ℚ (N false) : ℤ) - (γ : ℤ), ?_⟩
  rw [htrace_decomp, htrace_range, htrace_eq]
  push_cast
  ring

end

end LinearMap

end Moore57
