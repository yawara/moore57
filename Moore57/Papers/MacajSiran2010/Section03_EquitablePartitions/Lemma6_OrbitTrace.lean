import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Lemma 6

> Let `O` be an orbit of `X` and let `x ∈ X` contribute to `O` (i.e., for
> some `v ∈ O`, `vˣ ∼ v`). Then
>
> (1) `x⁻¹` contributes to `O`;
>
> (2) if `|X|` is odd, then `Tr(X)` is even;
>
> (3) if `x` is central in `X`, then `Tr(O) ≤ 2`;
>
> (4) `Tr(O)² < |O|`.

`Tr(O)` is the average degree of the subgraph induced by `O`.

Status:
* (1) **proven** — abstract counting argument (graph symmetry +
  orbit invariance).
* (2)–(4) [deferred-heavy] — require formalising `Tr(O)` and `Tr(X)`
  as concrete numerical quantities, plus pairing / centraliser arguments.
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 6 (1) (inverse also contributes).**

If `x` is an automorphism of `Γ`, `O ⊆ V` is invariant under `x`
(i.e. `x · v ∈ O` for `v ∈ O`), and there exists `v ∈ O` with
`Γ.Adj v (x v)`, then there also exists `w ∈ O` with `Γ.Adj w (x⁻¹ w)`.

Proof: take `w := x v`. By orbit invariance, `w ∈ O`; and
`x⁻¹ w = v`. Since `Γ.Adj v (x v) ↔ Γ.Adj (x v) v` (graph symmetry),
we have `Γ.Adj w (x⁻¹ w)`. -/
theorem lem6_inverse_contributes
    (x : Equiv.Perm V) (O : Set V)
    (hO_inv : ∀ v ∈ O, x v ∈ O)
    (hcontrib : ∃ v ∈ O, Γ.Adj v (x v)) :
    ∃ w ∈ O, Γ.Adj w (x⁻¹ w) := by
  obtain ⟨v, hv, hadj⟩ := hcontrib
  refine ⟨x v, hO_inv v hv, ?_⟩
  -- Goal: Γ.Adj (x v) (x⁻¹ (x v)) = Γ.Adj (x v) v
  have hxinv : x⁻¹ (x v) = v := by simp
  rw [hxinv]
  exact hadj.symm

/-- **Lemma 6 (2) (odd `|X|` ⇒ `Tr(X)` even).** [deferred-heavy]

Pairing argument: each `x ∈ X` with `x ≠ x⁻¹` contributes paired
counts; for `|X|` odd, only `x = 1` is self-inverse, and its
contribution is `0`. -/
theorem lem6_trace_even_of_odd_order (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 6 (3) (central ⇒ `Tr(O) ≤ 2`).** [deferred-heavy] -/
theorem lem6_central_trace_le_two (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 6 (4) (`Tr(O)² < |O|`).** [deferred-heavy] -/
theorem lem6_trace_sq_lt_size (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S3
