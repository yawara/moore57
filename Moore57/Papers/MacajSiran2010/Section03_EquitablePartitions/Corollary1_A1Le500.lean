import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Lemma10_TraceBounds
import Moore57.Moore57Graph.AdjMovedSet

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Corollary 1

> For any `x ∈ X`, `a₁(x) ≤ 500`.

Proof: let `S = {v ∈ Γ : v ∼ vˣ}`. Then `Tr(S) ≤ 2` (no-quadrangle
argument using `λ = 0`, `μ = 1` of Moore57), and by Lemma 10
(Mohar lower bound), `|S| ≤ 50 (8 + 2) = 500`.

The full proof is `Moore57.adjacentMovedCount_le_500` in
`Moore57Graph/AdjMovedSet.lean`.

This bound is used repeatedly in §5 to constrain the table of `a₁`'s.
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Corollary 1 (`a₁(x) ≤ 500`).** [done]

For any automorphism `x` of a Moore57 graph, `a₁(x) ≤ 500`.

Wraps `Moore57.adjacentMovedCount_le_500` (which combines the Mohar
lower trace bound from Lemma 10 with the `Tr(S) ≤ 2` no-quadrangle
argument). -/
theorem cor1_a1_le_500 (hΓ : IsMoore57 Γ) (x : Equiv.Perm V)
    (hx : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (x a) (x b)) :
    Moore57.adjacentMovedCount Γ x ≤ 500 :=
  Moore57.adjacentMovedCount_le_500 hΓ hx

/-- **Corollary 1 (alternative name: `adjacentMovedCount Γ x ≤ 500`).** [done]
Re-export of `cor1_a1_le_500` under the `adjacentMovedCount`-prefixed name. -/
theorem cor1_adjacentMovedCount_le_500
    (hΓ : IsMoore57 Γ) (x : Equiv.Perm V)
    (hx : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (x a) (x b)) :
    Moore57.adjacentMovedCount Γ x ≤ 500 :=
  cor1_a1_le_500 hΓ x hx

end Moore57.Papers.MacajSiran2010.S3
