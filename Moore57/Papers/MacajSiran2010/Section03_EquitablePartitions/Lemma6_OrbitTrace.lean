import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition
import Moore57.Foundations.GraphTheory.InducedTrace

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

open Moore57

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

/-- **Lemma 6 (2) (odd `|X|` ⇒ `Σ_{x ∈ X} a₁(x)` even).**

Pairing argument: for `X` a subgroup of `Equiv.Perm V` with odd order,
the involution `x ↦ x⁻¹` is fixed-point-free except at `x = 1`
(odd-order groups have no order-2 elements: `orderOf x ∣ |X|` is
odd, so `orderOf x` is odd, hence `≠ 2`).  Each non-trivial pair
`{x, x⁻¹}` contributes `a₁(x) + a₁(x⁻¹) = 2 · a₁(x)` via
`adjacentMovedCount_inv`.  The fixed point `x = 1` contributes
`a₁(1) = 0`.

This is the paper's "Tr(X) even" claim with the equivalent ℕ-form
`Σ_{x ∈ X} a₁(x) is even` (since `|X| · Tr(X) = Σ a₁(x)` by Lem 9 (2)).

No Moore57 hypothesis is needed; this is a pure consequence of the
adjacency-symmetry pairing structure. -/
theorem lem6_trace_even_of_odd_order
    (X : Subgroup (Equiv.Perm V)) [Fintype X]
    (hX_odd : Odd (Fintype.card X)) :
    Even (∑ x : X, adjacentMovedCount Γ (x : Equiv.Perm V)) :=
  Moore57.sum_adjacentMovedCount_even_of_subgroup_odd_card X hX_odd

/-- **Lemma 6 (3) (central ⇒ `Tr(O) ≤ 2`).** [deferred-heavy] -/
theorem lem6_central_trace_le_two (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 6 (4) (`Tr(O)² < |O|`).** [deferred-heavy] -/
theorem lem6_trace_sq_lt_size (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S3
