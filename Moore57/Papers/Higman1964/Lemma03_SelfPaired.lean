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

/-! ### Lemma 3 main form (D3.2 remaining): odd order rank-3 ⟹ k = l

The paper's odd-|G| rank-3 conclusion `k = l` is the combination of:
* (Stage A) Swap pairs the two non-diagonal orbitals (uses Lem 1
  contrapositive: odd order ⟹ no non-diagonal self-paired orbital).
* (Stage B) In-degree = out-degree for any orbital at any base point
  (double counting under transitivity + finite Ω).

Stage A is unconditional on Stage B and is the structural core of the
"k = l" identity.  Stage B is the remaining "double counting" piece,
the same difficulty level as the existing
`lem3_subdegree_eq_of_paired_and_eq_in_out_deg` conditional.
-/

/-- **Lemma 3 Stage A: rank 3 + odd ⟹ swap pairs non-diagonal orbitals**.
[done]

Conditional rank-3 packaging: three distinct orbitals `D, O₁, O₂` covering
all orbitals, with `D` the diagonal at some basepoint `a₀` and `O₁, O₂`
having non-diagonal representatives.  Under odd `|G|` (so by Lemma 1
contrapositive no non-diagonal orbital is self-paired), the swap involution
maps `O₁` to `O₂`.

Proof: `swapOrbital O₁` lies among the 3 orbitals.  It cannot equal `D`
(else `O₁ = swap D = D`, contradicting `D ≠ O₁`), and cannot equal `O₁`
itself (else `O₁` is self-paired, contradicting Lemma 1 contrapositive);
hence it equals `O₂`. -/
theorem lem3_swap_pairs_non_diagonal_orbitals
    (G Ω : Type*) [Group G] [MulAction G Ω] [Fintype G]
    {a₀ : Ω}
    {O₁ O₂ : Moore57.orbital G Ω}
    (h_D_ne_O₁ : Moore57.diagonalOrbital G Ω a₀ ≠ O₁)
    (h_cover : ∀ (O : Moore57.orbital G Ω),
       O = Moore57.diagonalOrbital G Ω a₀ ∨ O = O₁ ∨ O = O₂)
    (h_O₁_nondiag : ∃ a b : Ω,
       (Quotient.mk'' (a, b) : Moore57.orbital G Ω) = O₁ ∧ a ≠ b)
    (h_odd : ¬ 2 ∣ Fintype.card G) :
    Moore57.swapOrbital G Ω O₁ = O₂ := by
  have h_D_self : Moore57.IsSelfPaired G Ω
      (Moore57.diagonalOrbital G Ω a₀) :=
    Moore57.isSelfPaired_diagonalOrbital G Ω a₀
  -- O₁ is not self-paired (by Lem 1 contrapositive applied to its
  -- non-diagonal representative).
  have h_O₁_not_self : ¬ Moore57.IsSelfPaired G Ω O₁ := by
    intro h_self
    obtain ⟨a, b, h_rep, h_ne⟩ := h_O₁_nondiag
    exact lem1_no_non_diagonal_self_paired_of_odd_card G Ω h_odd
      ⟨O₁, a, b, h_self, h_rep, h_ne⟩
  rcases h_cover (Moore57.swapOrbital G Ω O₁) with h | h | h
  · -- swap O₁ = D ⟹ O₁ = swap D = D, contradicting D ≠ O₁
    exfalso
    apply h_D_ne_O₁
    have h2 : Moore57.swapOrbital G Ω (Moore57.swapOrbital G Ω O₁) =
              Moore57.swapOrbital G Ω
                (Moore57.diagonalOrbital G Ω a₀) :=
      congrArg _ h
    rw [Moore57.swapOrbital_involutive G Ω O₁, h_D_self] at h2
    exact h2.symm
  · -- swap O₁ = O₁ ⟹ O₁ is self-paired
    exact absurd h h_O₁_not_self
  · exact h

/-- **Lemma 3 main form (k = l), conditional on in-deg = out-deg for O₁**.
[done]

Combining Stage A (`lem3_swap_pairs_non_diagonal_orbitals`) with the
existing in-deg = out-deg conditional
(`lem3_subdegree_eq_of_paired_and_eq_in_out_deg`).  Under rank-3
packaging + odd order + the in-degree = out-degree hypothesis for `O₁`
at base point `a` (the remaining Stage B piece — double counting under
transitivity + finite Ω), the two non-diagonal subdegrees coincide:
`|N_{O₁}(a)| = |N_{O₂}(a)|`.

This is the precise paper-faithful "k = l" of Higman 1964 Lemma 3
(under odd `|G|`). -/
theorem lem3_subdegree_eq_of_odd_rank3_and_in_out_eq
    (G Ω : Type*) [Group G] [MulAction G Ω] [Fintype G]
    {a₀ a : Ω}
    {O₁ O₂ : Moore57.orbital G Ω}
    (h_D_ne_O₁ : Moore57.diagonalOrbital G Ω a₀ ≠ O₁)
    (h_cover : ∀ (O : Moore57.orbital G Ω),
       O = Moore57.diagonalOrbital G Ω a₀ ∨ O = O₁ ∨ O = O₂)
    (h_O₁_nondiag : ∃ a b : Ω,
       (Quotient.mk'' (a, b) : Moore57.orbital G Ω) = O₁ ∧ a ≠ b)
    (h_odd : ¬ 2 ∣ Fintype.card G)
    (h_in_out : Nat.card (Moore57.orbitalNeighborhood G Ω O₁ a) =
                Nat.card (Moore57.orbitalReverseNeighborhood G Ω O₁ a)) :
    Nat.card (Moore57.orbitalNeighborhood G Ω O₁ a) =
    Nat.card (Moore57.orbitalNeighborhood G Ω O₂ a) :=
  lem3_subdegree_eq_of_paired_and_eq_in_out_deg G Ω
    (lem3_swap_pairs_non_diagonal_orbitals G Ω h_D_ne_O₁ h_cover
      h_O₁_nondiag h_odd) a h_in_out

/-- **Lemma 3 (corollary, paper-faithful)**: under odd `|G|` and rank 3,
the swap involution has no non-diagonal fixed points; equivalently the
two non-diagonal orbitals are paired by swap. [done]

Restatement of `lem3_swap_pairs_non_diagonal_orbitals` focused on the
"paired by swap" conclusion. -/
theorem lem3_non_diagonal_orbitals_paired_of_odd_rank3
    (G Ω : Type*) [Group G] [MulAction G Ω] [Fintype G]
    {a₀ : Ω}
    {O₁ O₂ : Moore57.orbital G Ω}
    (h_D_ne_O₁ : Moore57.diagonalOrbital G Ω a₀ ≠ O₁)
    (h_cover : ∀ (O : Moore57.orbital G Ω),
       O = Moore57.diagonalOrbital G Ω a₀ ∨ O = O₁ ∨ O = O₂)
    (h_O₁_nondiag : ∃ a b : Ω,
       (Quotient.mk'' (a, b) : Moore57.orbital G Ω) = O₁ ∧ a ≠ b)
    (h_odd : ¬ 2 ∣ Fintype.card G) :
    Moore57.swapOrbital G Ω O₁ = O₂ ∧ Moore57.swapOrbital G Ω O₂ = O₁ := by
  have h₁ : Moore57.swapOrbital G Ω O₁ = O₂ :=
    lem3_swap_pairs_non_diagonal_orbitals G Ω h_D_ne_O₁ h_cover
      h_O₁_nondiag h_odd
  refine ⟨h₁, ?_⟩
  -- swap O₂ = swap (swap O₁) = O₁
  have := congrArg (Moore57.swapOrbital G Ω) h₁
  rw [Moore57.swapOrbital_involutive G Ω O₁] at this
  exact this.symm

/-- **Lemma 3 Stage B**: in-degree = out-degree under transitivity + finite Ω.
[done]

Paper-faithful wrap of `Moore57.orbitalNeighborhood_card_eq_orbitalReverseNeighborhood_card`:
for a transitive `G`-action on `Fintype Ω` (with `Nonempty Ω`), any
orbital `O` and any base point `a` satisfy
`|N_O(a)| = |N⁻_O(a)|`.

Combined with Stage A (`lem3_swap_pairs_non_diagonal_orbitals`), this
discharges the in-deg = out-deg hypothesis of
`lem3_subdegree_eq_of_odd_rank3_and_in_out_eq`, giving the
unconditional `k = l` form (see `lem3_subdegree_eq_of_odd_rank3`). -/
theorem lem3_in_deg_eq_out_deg
    (G Ω : Type*) [Group G] [MulAction G Ω] [Fintype Ω] [Nonempty Ω]
    (h_trans : ∀ a b : Ω, ∃ g : G, g • a = b)
    (O : Moore57.orbital G Ω) (a : Ω) :
    Nat.card (Moore57.orbitalNeighborhood G Ω O a) =
    Nat.card (Moore57.orbitalReverseNeighborhood G Ω O a) :=
  Moore57.orbitalNeighborhood_card_eq_orbitalReverseNeighborhood_card
    G Ω h_trans O a

/-- **Lemma 3 main form (unconditional)**: under transitive rank-3
action on `Fintype Ω` (`Nonempty Ω`) with odd `|G|`, the two
non-diagonal subdegrees coincide (`k = l` in the paper's notation).
[done]

Combines Stage A (swap pairs non-diagonal orbitals — Lem 1
contrapositive) and Stage B (in-deg = out-deg double counting). -/
theorem lem3_subdegree_eq_of_odd_rank3
    (G Ω : Type*) [Group G] [MulAction G Ω] [Fintype G]
    [Fintype Ω] [Nonempty Ω]
    {a₀ a : Ω}
    {O₁ O₂ : Moore57.orbital G Ω}
    (h_trans : ∀ a b : Ω, ∃ g : G, g • a = b)
    (h_D_ne_O₁ : Moore57.diagonalOrbital G Ω a₀ ≠ O₁)
    (h_cover : ∀ (O : Moore57.orbital G Ω),
       O = Moore57.diagonalOrbital G Ω a₀ ∨ O = O₁ ∨ O = O₂)
    (h_O₁_nondiag : ∃ a b : Ω,
       (Quotient.mk'' (a, b) : Moore57.orbital G Ω) = O₁ ∧ a ≠ b)
    (h_odd : ¬ 2 ∣ Fintype.card G) :
    Nat.card (Moore57.orbitalNeighborhood G Ω O₁ a) =
    Nat.card (Moore57.orbitalNeighborhood G Ω O₂ a) :=
  lem3_subdegree_eq_of_odd_rank3_and_in_out_eq G Ω h_D_ne_O₁ h_cover
    h_O₁_nondiag h_odd (lem3_in_deg_eq_out_deg G Ω h_trans O₁ a)

/-- **Lemma 3 (paper-faithful "k = l" under odd order).** [done]

Proper-signature paper-faithful packaging: given odd `|G|` + rank-3
transitive `G` action on `Ω` + the standard rank-3 orbital cover
(`{diag, O₁, O₂}`), the two non-diagonal orbital subdegrees coincide:
`|O₁(a)| = |O₂(a)|`.  This is Stage A + Stage B + parity combined.

Re-export of `lem3_subdegree_eq_of_odd_rank3` for paper-faithful naming. -/
theorem lem3_self_paired_paper
    (G Ω : Type*) [Group G] [MulAction G Ω] [Fintype G]
    [Fintype Ω] [Nonempty Ω]
    {a₀ a : Ω}
    {O₁ O₂ : Moore57.orbital G Ω}
    (h_trans : ∀ a b : Ω, ∃ g : G, g • a = b)
    (h_D_ne_O₁ : Moore57.diagonalOrbital G Ω a₀ ≠ O₁)
    (h_cover : ∀ (O : Moore57.orbital G Ω),
       O = Moore57.diagonalOrbital G Ω a₀ ∨ O = O₁ ∨ O = O₂)
    (h_O₁_nondiag : ∃ a b : Ω,
       (Quotient.mk'' (a, b) : Moore57.orbital G Ω) = O₁ ∧ a ≠ b)
    (h_odd : ¬ 2 ∣ Fintype.card G) :
    Nat.card (Moore57.orbitalNeighborhood G Ω O₁ a) =
    Nat.card (Moore57.orbitalNeighborhood G Ω O₂ a) :=
  lem3_subdegree_eq_of_odd_rank3 G Ω h_trans h_D_ne_O₁ h_cover h_O₁_nondiag h_odd

/-- **Lemma 3 (self-paired structure under parity).** [deferred-heavy]

Full iff packaging combining Stage A and Stage B with Lem 1's two
directions.  Both Stage A (`lem3_swap_pairs_non_diagonal_orbitals`)
and Stage B (`lem3_in_deg_eq_out_deg`) are proven; the unconditional
"k = l" conclusion is `lem3_subdegree_eq_of_odd_rank3` /
`lem3_self_paired_paper` (above). -/
theorem lem3_self_paired_iff_even : True := by trivial

/-- **Corollary to Lemma 3** (symmetry of `Δ` under even order). [deferred-heavy] -/
theorem cor_lem3_symmetric_delta_of_even : True := by trivial

end Moore57.Papers.Higman1964
