import Moore57.Moore57Graph.Aut.SingletonAndEmptyFixedData
import Moore57.Moore57Graph.Aut.FixedCount

/-!
# Construction of `EmptyFixedData` for an order-13 Moore57 automorphism

Paper-reference: Mačaj–Širáň 2010, §6, Lemma 19 case (1).

> Let `p > 5` be a prime and let `X` be a group of automorphisms of Γ of
> order `p^k`.  Case (1) of Lemma 19 asserts `Fix(X) = ∅` and `X ≅ Z₁₃`.

For an automorphism `σ : Equiv.Perm V` of a Moore57 graph with `σ^13 = 1`
and `σ ≠ 1`, the *paper-asserted* shape of Fix is empty: `Fix(σ) = ∅`.
This file provides the **constructor** `aut_order_thirteen_EmptyFixedData`
that, given the geometric fix-emptiness fact `fixedVertexCount σ = 0`,
packages it as a `EmptyFixedData σ` structure (the input expected by the
§6 Lem 19 case (1) chain).

## Status: partial unconditional

The full unconditional derivation of `fixedVertexCount σ = 0` from
`σ^13 = 1 ∧ σ ≠ 1` requires the structural Fix-shape classification chain
(rule out singleton / pentagon / Petersen / HS / star / edge cases via
mod-13 constraints on `|N(a) ∩ Fix|` ≡ 5).  The mod-13 modular constraint
machinery is already available
(`aut_fixedVertexCount_modEq_zero_of_pow_thirteen_pow` and friends in
`FixedCount.lean` / `NeighborMod.lean`), but the shape-exclusion ladder
(`|Fix(σ)| < 13` ⟹ `|Fix(σ)| = 0`) is **not yet** in Foundations.

This file therefore exposes the **conditional constructor** taking
`fixedVertexCount σ = 0` as input.  Mirrors the role of
`aut_order_eleven_C5FixedData` (in `OrderElevenIsC5.lean`) which derives
the order-11 pentagon-fix `C5FixedData` structure unconditionally.

## Design parallel

| File                          | Output            | Status         |
|-------------------------------|-------------------|----------------|
| `OrderElevenIsC5.lean`        | `C5FixedData`     | unconditional  |
| `OrderThirteenEmptyFix.lean`  | `EmptyFixedData`  | conditional    |

When the §2 / §6 shape-classification chain matures (paper Lem 4 / 16
case (1) ⟹ `fixedVertexCount σ = 0` for the 13-prime case
unconditionally), this constructor immediately upgrades to unconditional
without any signature change at the consumer side.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Constructor for `EmptyFixedData` from `fixedVertexCount σ = 0` -/

/-- **EmptyFixedData from fix-emptiness count.** [done]

Given any permutation `σ : Equiv.Perm V` whose σ-fixed-vertex count is
`0`, construct the canonical `EmptyFixedData σ` structure.  The
`no_fixed` proof is read off from the standard Finset-cardinality
characterization (`fixedVertexCount σ = 0` ↔ no `x` satisfies `σ x = x`).

This is the underlying constructor used by
`aut_order_thirteen_EmptyFixedData` (specialised to `σ^13 = 1` plus the
13-prime fix-emptiness fact). -/
def emptyFixedData_of_fixedVertexCount_eq_zero
    (σ : Equiv.Perm V) (h_count : fixedVertexCount σ = 0) :
    EmptyFixedData σ where
  no_fixed := by
    intro x hfix
    -- From fixedVertexCount σ = 0, every `x` is moved.
    have hsub : x ∈ ((Finset.univ : Finset V).filter (fun w => σ w = w)) := by
      simp [hfix]
    rw [fixedVertexCount, Finset.card_eq_zero] at h_count
    rw [h_count] at hsub
    exact (Finset.notMem_empty _) hsub

/-! ### Lemma 19 case (1) input: `EmptyFixedData` from `σ^13 = 1`

The constructor `aut_order_thirteen_EmptyFixedData` is the §6 Lem 19
case (1) data-packaging step: given the paper-asserted fix-emptiness
(`fixedVertexCount σ = 0` for a `σ^13 = 1, σ ≠ 1` Moore57 graph
automorphism), produce the `EmptyFixedData σ` structure that feeds into
the C3.4 semi-regular bridge (giving `orderOf σ ∣ 3250`) and onward to
the arithmetic core (giving `orderOf σ ∣ 13`).

The current signature includes `fixedVertexCount σ = 0` as an explicit
hypothesis because the shape-classification chain that derives it
unconditionally from `σ^13 = 1 ∧ σ ≠ 1` is not yet formalised.  The
parallel `aut_order_eleven_C5FixedData` derives `|Fix(σ)| = 5`
unconditionally because the order-11 SRG chain
(`aut_fixedInducedGraph_regular_of_pow_eleven` etc.) is already in
place; the analogous order-13 chain is the deferred piece. -/

/-- **Lem 19 case (1) `EmptyFixedData` constructor (partial unconditional).** [done]

Given:
* `hΓ : IsMoore57 Γ` (the host graph is a Moore57 graph),
* `σ : Equiv.Perm V` with `σ^13 = 1` and `σ ≠ 1`,
* `smul_adj` (σ is a graph automorphism),
* `h_fix_empty : fixedVertexCount σ = 0` (the geometric fix-emptiness
  fact, paper-asserted),

produce `EmptyFixedData σ`.  Mirrors `aut_order_eleven_C5FixedData`
modulo the (currently deferred) shape-classification chain. -/
noncomputable def aut_order_thirteen_EmptyFixedData
    (_hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (_smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (_pow_thirteen : σ ^ 13 = 1) (_hne : σ ≠ 1)
    (h_fix_empty : fixedVertexCount σ = 0) :
    EmptyFixedData σ :=
  emptyFixedData_of_fixedVertexCount_eq_zero σ h_fix_empty

/-- **Lem 19 case (1) input bound: `fixedVertexCount σ ≡ 0 [MOD 13]`.** [done]

Re-export of `aut_fixedVertexCount_modEq_zero_of_pow_thirteen_pow` for
the prime case (`k = 1`).  Used as the modular ingredient in the
unconditional Path B chain for case (1). -/
theorem aut_order_thirteen_fixedVertexCount_modEq_zero
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_thirteen : σ ^ 13 = 1) :
    fixedVertexCount σ ≡ 0 [MOD 13] := by
  have h_pow_pow : σ ^ (13 : ℕ) ^ 1 = 1 := by simpa using pow_thirteen
  exact aut_fixedVertexCount_modEq_zero_of_pow_thirteen_pow hΓ σ 1 h_pow_pow

/-- **Lem 19 case (1) `EmptyFixedData` via small fix-count.** [done]

If `fixedVertexCount σ ≤ 12`, the mod-13 constraint
`fixedVertexCount σ ≡ 0 [MOD 13]` forces `fixedVertexCount σ = 0`, and
the `EmptyFixedData` constructor applies.  Mirrors the §6 Lem 16
case (1) `lem16_case1_13group_fix_empty_if_small` shape-narrowing. -/
noncomputable def aut_order_thirteen_EmptyFixedData_of_small_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_thirteen : σ ^ 13 = 1) (hne : σ ≠ 1)
    (h_small : fixedVertexCount σ ≤ 12) :
    EmptyFixedData σ := by
  have h_count_zero : fixedVertexCount σ = 0 := by
    have hmod := aut_order_thirteen_fixedVertexCount_modEq_zero hΓ σ pow_thirteen
    rw [Nat.ModEq] at hmod
    omega
  exact aut_order_thirteen_EmptyFixedData hΓ σ smul_adj pow_thirteen hne h_count_zero

end Moore57
