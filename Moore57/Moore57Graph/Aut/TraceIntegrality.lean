import Moore57.Moore57Graph.E7Matrix.PermutationCommutation
import Moore57.D19OnMoore57.E7Projection.ProjectionTraceBridge
import Moore57.D19OnMoore57.E7Projection.ProjectionRepresentationSkeleton
import Moore57.Foundations.LinearAlgebra.InvolutionTrace
import Moore57.Foundations.LinearAlgebra.PowPrimeTrace
import Moore57.Foundations.LinearAlgebra.PowCompositeTrace

/-!
# E7-projection trace integrality for an involutive Moore57 automorphism (Tier 2)

For an involutive automorphism `σ : Equiv.Perm V` of a Moore57 graph,
`Matrix.trace (E7Matrix Γ * permMatrix σ)` is an integer. The proof uses

* `E7Matrix Γ` is idempotent (`E7Matrix_toLin'_isIdempotentElem`);
* `permMatrix σ` commutes with `E7Matrix Γ` (since σ is an automorphism);
* the restriction of `(permMatrix σ).toLin'` to the range of `E7Matrix.toLin'`
  is well-defined and squares to the identity when σ² = 1;
* `Moore57.LinearMap.exists_int_trace_of_involutive` gives the trace as an integer;
* `trace_restrict_E7Range_permMatrix_toLin'_eq_matrix_trace` bridges the
  linear-map trace and the matrix trace.

This abstract version is used by both the existing D₁₉ reflection pipeline
and the upcoming C₃₈ argument.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- For any involutive automorphism `σ` of a Moore57 graph,
`Matrix.trace (E7Matrix Γ * permMatrix σ)` is an integer. -/
theorem aut_involution_E7_trace_int
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ) :
    ∃ z : ℤ, Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ) := by
  classical
  -- The range of the E7 projection (an `ℚ`-submodule of `V → ℚ`).
  let W := LinearMap.range (E7Matrix Γ).toLin'
  -- The commutation `E7Matrix.toLin' ∘ (permMatrix σ).toLin' =
  -- (permMatrix σ).toLin' ∘ E7Matrix.toLin'`.
  have hcomm :
      Commute (E7Matrix Γ).toLin' (permMatrix σ).toLin' :=
    E7Matrix_toLin'_commute_permMatrix_toLin' Γ σ haut
  -- The range is invariant under `(permMatrix σ).toLin'`.
  have hmaps :
      ∀ x ∈ W, (permMatrix σ).toLin' x ∈ W := by
    intro x hx
    exact ((Module.End.mem_invtSubmodule_iff_mapsTo
      (f := (permMatrix σ).toLin')).mp
        ((LinearMap.IsIdempotentElem.commute_iff
          (E7Matrix_toLin'_isIdempotentElem hΓ)
          (T := (permMatrix σ).toLin')).mp hcomm).1) hx
  -- Restrict `(permMatrix σ).toLin'` to `W`.
  let f : W →ₗ[ℚ] W := (permMatrix σ).toLin'.restrict hmaps
  -- Show `f * f = 1` using σ involutive.
  have hσ_sq : σ * σ = 1 := by
    ext v
    simpa using hinv v
  have hperm_sq : permMatrix σ * permMatrix σ = (1 : Matrix V V ℚ) := by
    rw [← moore57_permMatrix_mul, hσ_sq, moore57_permMatrix_one]
  have hlin_sq :
      (permMatrix σ).toLin' * (permMatrix σ).toLin' = 1 := by
    rw [Module.End.mul_eq_comp, ← matrix_toLin'_mul, hperm_sq, Matrix.toLin'_one]
    rfl
  have hsq : f * f = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hf2 :
        ((f * f) x : V → ℚ) = (permMatrix σ).toLin' ((permMatrix σ).toLin' x.1) := rfl
    have hone : ((1 : (W →ₗ[ℚ] W)) x : V → ℚ) = x.1 := rfl
    rw [hf2, hone]
    have := congr_arg (fun g => g x.1) hlin_sq
    simpa using this
  -- Apply the abstract integer-trace lemma for involutive endomorphisms.
  obtain ⟨z, hz⟩ := Moore57.LinearMap.exists_int_trace_of_involutive f hsq
  refine ⟨z, ?_⟩
  rw [← hz]
  exact (trace_restrict_E7Range_permMatrix_toLin'_eq_matrix_trace hΓ σ haut).symm

/-- Helper: `(permMatrix σ)^n = permMatrix (σ^n)` (Moore57 hom). -/
private theorem permMatrix_pow_eq_local (σ : Equiv.Perm V) (n : ℕ) :
    (permMatrix σ : Matrix V V ℚ) ^ n = permMatrix (σ ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, moore57_permMatrix_one]
  | succ k ih => rw [pow_succ, ih, pow_succ, moore57_permMatrix_mul]

/-- **Composite-order generalization** (Phase 2.1).  For any automorphism σ
of a Moore57 graph with `σ^n = 1` (n > 0), `Matrix.trace (E7Matrix Γ *
permMatrix σ)` is an integer.

This generalizes `aut_pow_prime_E7_trace_int` (prime n case) to arbitrary
positive order, using the composite-order cyclotomic-block trace theory
(`Foundations/LinearAlgebra/PowCompositeTrace.lean`, specifically
`trace_int_of_pow_eq_one`).

The infrastructure is identical to the prime case (idempotent commutation,
range restriction, restrict-pow-apply) — only the final integer-trace
appeal changes from `exists_int_trace_of_pow_prime_eq_one` to the
composite-version `trace_int_of_pow_eq_one`. -/
theorem aut_pow_E7_trace_int_composite
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (n : ℕ) (hn : 0 < n) (hpow : σ ^ n = 1) :
    ∃ z : ℤ, Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ) := by
  classical
  let W := LinearMap.range (E7Matrix Γ).toLin'
  have hcomm :
      Commute (E7Matrix Γ).toLin' (permMatrix σ).toLin' :=
    E7Matrix_toLin'_commute_permMatrix_toLin' Γ σ haut
  have hmaps :
      ∀ x ∈ W, (permMatrix σ).toLin' x ∈ W := by
    intro x hx
    exact ((Module.End.mem_invtSubmodule_iff_mapsTo
      (f := (permMatrix σ).toLin')).mp
        ((LinearMap.IsIdempotentElem.commute_iff
          (E7Matrix_toLin'_isIdempotentElem hΓ)
          (T := (permMatrix σ).toLin')).mp hcomm).1) hx
  let f : W →ₗ[ℚ] W := (permMatrix σ).toLin'.restrict hmaps
  -- σ^n = 1 ⟹ permMatrix σ ^ n = 1 as matrix.
  have hperm_pow : (permMatrix σ : Matrix V V ℚ) ^ n = 1 := by
    rw [permMatrix_pow_eq_local, hpow, moore57_permMatrix_one]
  -- ⟹ (permMatrix σ).toLin' ^ n = 1 as linear map.
  have hlin_pow : ((permMatrix σ).toLin' : Module.End ℚ (V → ℚ)) ^ n = 1 := by
    have h := Matrix.toLin'_pow (permMatrix σ) n
    rw [hperm_pow, Matrix.toLin'_one] at h
    exact h.symm
  -- ⟹ f^n = 1 on subspace W.
  have hf_pow : f ^ n = 1 := by
    apply LinearMap.ext
    intro ⟨x, hx⟩
    apply Subtype.ext
    change ((f ^ n) ⟨x, hx⟩ : V → ℚ) = x
    have key : ((f ^ n) ⟨x, hx⟩ : V → ℚ) =
        ((permMatrix σ).toLin' ^ n) x := by
      change ((((permMatrix σ).toLin'.restrict hmaps) ^ n) ⟨x, hx⟩ : V → ℚ) = _
      exact Moore57.LinearMap.restrict_pow_apply
        (permMatrix σ).toLin' W hmaps n ⟨x, hx⟩
    rw [key, hlin_pow]
    rfl
  -- Apply the composite-order integer-trace lemma.
  obtain ⟨z, hz⟩ := Moore57.LinearMap.trace_int_of_pow_eq_one f hn hf_pow
  refine ⟨z, ?_⟩
  rw [← hz]
  exact (trace_restrict_E7Range_permMatrix_toLin'_eq_matrix_trace hΓ σ haut).symm

/-- For any prime-order automorphism `σ` of a Moore57 graph
(`σ^p = 1`, `p` prime), `Matrix.trace (E7Matrix Γ * permMatrix σ)` is an integer.

This generalizes `aut_involution_E7_trace_int` (the `p = 2` case) to
arbitrary prime order, using cyclotomic-block trace theory
(`Foundations/LinearAlgebra/PowPrimeTrace.lean`). -/
theorem aut_pow_prime_E7_trace_int
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (p : ℕ) [Fact (Nat.Prime p)] (hpow : σ ^ p = 1) :
    ∃ z : ℤ, Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ) := by
  classical
  let W := LinearMap.range (E7Matrix Γ).toLin'
  have hcomm :
      Commute (E7Matrix Γ).toLin' (permMatrix σ).toLin' :=
    E7Matrix_toLin'_commute_permMatrix_toLin' Γ σ haut
  have hmaps :
      ∀ x ∈ W, (permMatrix σ).toLin' x ∈ W := by
    intro x hx
    exact ((Module.End.mem_invtSubmodule_iff_mapsTo
      (f := (permMatrix σ).toLin')).mp
        ((LinearMap.IsIdempotentElem.commute_iff
          (E7Matrix_toLin'_isIdempotentElem hΓ)
          (T := (permMatrix σ).toLin')).mp hcomm).1) hx
  let f : W →ₗ[ℚ] W := (permMatrix σ).toLin'.restrict hmaps
  -- σ^p = 1 ⟹ permMatrix σ ^ p = 1 as matrix.
  have hperm_pow : (permMatrix σ : Matrix V V ℚ) ^ p = 1 := by
    rw [permMatrix_pow_eq_local, hpow, moore57_permMatrix_one]
  -- ⟹ (permMatrix σ).toLin' ^ p = 1 as linear map.
  have hlin_pow : ((permMatrix σ).toLin' : Module.End ℚ (V → ℚ)) ^ p = 1 := by
    have h := Matrix.toLin'_pow (permMatrix σ) p
    rw [hperm_pow, Matrix.toLin'_one] at h
    -- h : (1 : V → ℚ →ₗ V → ℚ) = (permMatrix σ).toLin' ^ p ... wait check direction
    -- toLin'_pow : (M^k).toLin' = M.toLin'^k
    -- After rw [hperm_pow]: (1 : Matrix V V ℚ).toLin' = (permMatrix σ).toLin'^p
    -- After rw [Matrix.toLin'_one]: 1 = (permMatrix σ).toLin' ^ p
    -- So h.symm gives what we want.
    exact h.symm
  -- ⟹ f^p = 1 on subspace W.
  have hf_pow : f ^ p = 1 := by
    apply LinearMap.ext
    intro ⟨x, hx⟩
    apply Subtype.ext
    -- Goal (after Subtype.ext): ↑((f ^ p) ⟨x, hx⟩) = ↑((1 : W →ₗ[ℚ] W) ⟨x, hx⟩) = x
    show ((f ^ p) ⟨x, hx⟩ : V → ℚ) = x
    have key : ((f ^ p) ⟨x, hx⟩ : V → ℚ) =
        ((permMatrix σ).toLin' ^ p) x := by
      change ((((permMatrix σ).toLin'.restrict hmaps) ^ p) ⟨x, hx⟩ : V → ℚ) = _
      exact Moore57.LinearMap.restrict_pow_apply
        (permMatrix σ).toLin' W hmaps p ⟨x, hx⟩
    rw [key, hlin_pow]
    rfl
  -- Apply the abstract integer-trace lemma.
  obtain ⟨z, hz⟩ := Moore57.LinearMap.exists_int_trace_of_pow_prime_eq_one f p hf_pow
  refine ⟨z, ?_⟩
  rw [← hz]
  exact (trace_restrict_E7Range_permMatrix_toLin'_eq_matrix_trace hΓ σ haut).symm

end Moore57
