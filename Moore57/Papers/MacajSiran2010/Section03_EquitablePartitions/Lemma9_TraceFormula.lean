import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Lemma 9

> (1) Let `O` be an orbit of `X` and let `v ∈ O`. Then
> ```
> Tr(O) = |{x ∈ X : v ∼ vˣ}| · |O| / |X|.
> ```
>
> (2) ```
> |X| · Tr(X) = |{(x, v) ∈ X × Γ : v ∼ vˣ}| = Σ_{x ∈ X} a₁(x).
> ```

Status:
* (2) **proven**: the double-counting identity
  `Σ_{x ∈ X} a₁(x) = |{(x, v) : Γ.Adj v (x v)}|` is a direct
  consequence of swapping sums (`Finset.sum_filter`).
* (1) [deferred-heavy] — requires defining `Tr(O)` and connecting to
  the orbit-stabilizer rewrite.
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 9 (1) (orbit trace formula).** [deferred-heavy] -/
theorem lem9_orbit_trace_formula (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 9 (2) (double-counting: `Σ_x a₁(x) = |{(x, v) : v ~ x v}|`).**

Pure double-counting identity (no Moore57 hypothesis needed).  The
RHS counts pairs `(x, v)` with `v ~ x v`, where `x` ranges over a
finite set `X` of permutations.  By `Finset.card_filter` and
`Finset.sum_product`, this equals `Σ_{x ∈ X} a₁(x)`. -/
theorem lem9_global_trace_formula
    {X : Finset (Equiv.Perm V)} :
    (((X ×ˢ (Finset.univ : Finset V)).filter
        (fun p => Γ.Adj p.2 (p.1 p.2))).card : ℕ) =
      ∑ x ∈ X, adjacentMovedCount Γ x := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  unfold adjacentMovedCount
  rw [Finset.card_filter]

end Moore57.Papers.MacajSiran2010.S3
