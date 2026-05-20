import Moore57.Moore57Graph.Moore57Definition
import Moore57.Papers.Higman1964.Lemma01_PairedOrbits
import Moore57.Foundations.GroupTheory.RankAndOrbital

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Higman 1964, Lemma 3 (§2, Self-paired ⇔ even)

> If `|G|` is even, then `Δ(a)` and `Γ(a)` are both self-paired.
> If `|G|` is odd, then `Δ'(a) = Γ(a)`, hence `k = l`, `n = 2k + 1`,
> `λ = μ`.

Combined with Lemma 1: a rank-3 group has the two non-trivial orbits
self-paired ⇔ `|G|` is even.

**Corollary.**
* If `|G|` even, `a ∈ Δ(b) ⇒ b ∈ Δ(a)` (the "graph" `b ∈ Δ(a)` is symmetric).
* If `|G|` odd, `a ∈ Δ(b) ⇒ b ∈ Γ(a)`.

[deferred-heavy]

Status:
* `lem3_self_paired_iff_even`, `cor_lem3_symmetric_delta_of_even`:
  paper-stubs (rank-3 paired-orbit framework, deferred-heavy).
* `lem3_odd_order_arithmetic`: **proven** — pure ℕ arithmetic
  packaging the `n = 2k + 1` identity from odd-order case.
* `lem3_moore57_no_odd_aut_via_n_parity`: **proven** — Moore57's
  `n = 3250` is even, so it cannot satisfy `n = 2k + 1` for any `k`,
  hence the odd-order rank-3 case cannot apply to Moore57.
* `lem3_paired_orbital_neighborhood_card_eq`: **proven** (D3.2 backbone)
  — if `swapOrbital O₁ = O₂` (paired orbitals), then the reverse
  neighborhood of `O₁` at any `a` coincides with the forward
  neighborhood of `O₂` at `a`.  This is the structural identity
  behind the paper's "Δ'(a) = Γ(a)" claim.
* `lem3_subdegree_G_invariant`: **proven** (D3.2 backbone) — the
  subdegree (cardinality of an orbital neighborhood) is `G`-invariant
  under the diagonal action.
-/

namespace Moore57.Papers.Higman1964

/-- **Lemma 3 backbone: paired orbital subdegrees coincide via reverse neighborhood**. [done]

If `swapOrbital O₁ = O₂` (i.e., `O₁, O₂` are paired orbitals), then for
any base point `a ∈ Ω`, the reverse orbital neighborhood `{c | (c, a) ∈ O₁}`
coincides with the forward orbital neighborhood `{c | (a, c) ∈ O₂}`.

This is the precise paper-faithful expression of "the relation defined by
`O₁` reverses to the relation defined by `O₂`".  For Higman 1964 Lem 3:
under odd order + rank 3, the two non-diagonal orbitals are paired
(swap maps one to the other), and this identity is the structural step
toward `k = l`.

Wraps `Moore57.lem3_reverseNeighborhood_eq_neighborhood_of_paired`. -/
theorem lem3_paired_orbital_neighborhood_card_eq
    (G Ω : Type*) [Group G] [MulAction G Ω]
    {O₁ O₂ : Moore57.orbital G Ω} (h : Moore57.swapOrbital G Ω O₁ = O₂)
    (a : Ω) :
    Moore57.orbitalReverseNeighborhood G Ω O₁ a =
    Moore57.orbitalNeighborhood G Ω O₂ a :=
  Moore57.lem3_reverseNeighborhood_eq_neighborhood_of_paired G Ω h a

/-- **Lemma 3 backbone: subdegree is `G`-invariant**. [done]

The cardinality of an orbital neighborhood `|N_O(a)|` (the
"subdegree" of `O` at base point `a`) is invariant under the diagonal
`G`-action: `|N_O(g•a)| = |N_O(a)|`.

For a transitive `G`-action, this means the subdegree depends only on
the orbital `O` (not on `a`).  Higman 1964 Lem 3 uses this in the
constancy of `k = |Δ(a)|` and `l = |Γ(a)|`.

Wraps `Moore57.orbitalNeighborhood_card_smul`. -/
theorem lem3_subdegree_G_invariant
    (G Ω : Type*) [Group G] [MulAction G Ω]
    (O : Moore57.orbital G Ω) (g : G) (a : Ω) :
    Nat.card (Moore57.orbitalNeighborhood G Ω O (g • a)) =
    Nat.card (Moore57.orbitalNeighborhood G Ω O a) :=
  Moore57.orbitalNeighborhood_card_smul G Ω O g a

/-- **Lemma 3 main form (conditional)**: under paired orbitals + in-deg
= out-deg hypothesis (which holds under transitive + finite Ω by
double counting), the two paired-orbital subdegrees coincide
(`k = l` in the paper's notation).

This is the conditional "k = l" form of Higman 1964 Lem 3:
* Paired hypothesis (`swap O₁ = O₂`) comes from Lem 1 main form under
  odd order: in a rank-3 odd-order group, the two non-diagonal
  orbitals are paired by swap.
* In-deg = out-deg comes from double-counting (`∑_a |N_O(a)| =
  |orbital_set O| = ∑_a |N⁻_O(a)|`) under transitivity + Fintype Ω.

Both inputs are then independently formalisable.  Wraps
`Moore57.lem3_subdegree_eq_of_paired_and_eq_in_out_deg`. -/
theorem lem3_subdegree_eq_of_paired_and_eq_in_out_deg
    (G Ω : Type*) [Group G] [MulAction G Ω]
    {O₁ O₂ : Moore57.orbital G Ω}
    (h_paired : Moore57.swapOrbital G Ω O₁ = O₂) (a : Ω)
    (h_in_out : Nat.card (Moore57.orbitalNeighborhood G Ω O₁ a) =
                Nat.card (Moore57.orbitalReverseNeighborhood G Ω O₁ a)) :
    Nat.card (Moore57.orbitalNeighborhood G Ω O₁ a) =
    Nat.card (Moore57.orbitalNeighborhood G Ω O₂ a) :=
  Moore57.lem3_subdegree_eq_of_paired_and_eq_in_out_deg
    (G := G) (Ω := Ω) h_paired a h_in_out

/-- **Lemma 3 odd-order arithmetic: `n = 2k + 1`**. [done]

The paper's odd-`|G|` rank-3 conclusion: `k = l` and `n = 1 + k + l = 1 + 2k`.
Packaged as a conditional identity. -/
theorem lem3_odd_order_arithmetic
    (n k l : ℕ)
    (h_n : n = 1 + k + l)
    (h_eq : k = l) :
    n = 2 * k + 1 := by
  rw [h_n, h_eq]; ring

/-- **Lemma 3 Moore57 contrapositive: `n = 3250` is even, so no odd-order
rank-3 action**. [done]

For Moore57 with `n = 3250` (even), the necessary condition `n = 2k + 1`
(odd) of the odd-`|G|` case *fails* — there is no `k : ℕ` with
`3250 = 2k + 1`.  Hence any rank-3 group acting on Moore57 has *even*
order, consistent with Lem 5 Cor 1 (`λ ≠ μ` for Moore57). -/
theorem lem3_moore57_no_odd_aut_via_n_parity :
    ¬ ∃ k : ℕ, (3250 : ℕ) = 2 * k + 1 := by
  intro ⟨k, hk⟩
  omega

/-- **Lemma 3 (self-paired structure under parity).** [deferred-heavy] -/
theorem lem3_self_paired_iff_even : True := by trivial

/-- **Corollary to Lemma 3** (symmetry of `Δ` under even order). [deferred-heavy] -/
theorem cor_lem3_symmetric_delta_of_even : True := by trivial

end Moore57.Papers.Higman1964
