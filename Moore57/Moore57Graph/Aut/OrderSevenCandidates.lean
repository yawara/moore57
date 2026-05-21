import Moore57.Moore57Graph.Aut.InducedSubgraph
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Aut.FixedCount
import Moore57.Moore57Graph.Aut.SRGKSquarePlusOne
import Moore57.D19OnMoore57.Fixed.InducedStarEdgeFormula
import Moore57.Foundations.GraphTheory.StrongZeroOne
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Fixed-vertex structure for an order-7 Moore57 automorphism (Tier 2)

For an automorphism `σ : Equiv.Perm V` of a Moore57 graph with
`σ ^ 7 = 1` and `σ ≠ 1`, we derive the structure of `Fix(σ)`.

Mačaj–Širáň 2010 Lemma 16 case (3) says: when the local fix-induced
graph is shape `K_{1,1} = K_2` (edge), the fix size is exactly `2`.
This module sets up the 7-prime analog of the 11-prime SRG ladder
(`OrderElevenCandidates.lean`) and the 13-prime ladder
(`OrderThirteenCandidates.lean`), and provides the regular-case
classification plus narrowing lemmas.

## Key arithmetic differences vs the 11-prime case

* `3250 = 7·464 + 2` ⟹ `|Fix(σ)| ≡ 2 (mod 7)`.
* `57 = 7·8 + 1` ⟹ `|N(v) ∩ Fix(σ)| ≡ 1 (mod 7)` at any σ-fixed `v`.
* Star case is **NOT** excluded: the leaf degree `1` is congruent to
  `1 (mod 7)`, matching the fix-neighbour count constraint.
  Stars of shape `K_{1, 1+7l}` with `l ≥ 0` are all locally consistent.
* Regular case: the degree `k ≡ 1 (mod 7)`, intersected with the
  Hoffman-Singleton degree list `{0,1,2,3,7,57}` gives `k ∈ {1, 7, 57}`.
* `k = 57` is excluded by `σ ≠ 1` (would force `|Fix| = 3250 = |V|`).
* Regular candidates: `k ∈ {1, 7}` with `|Fix| ∈ {2, 50}` respectively.

The remaining shape ambiguity (star `K_{1, 1+7l}` with `l ≥ 0`, vs
regular with `k ∈ {1, 7}`) cannot be resolved from purely local data
on `Fix(σ)`; the §6 Lemma 16 case 3 pin to `l = 0` (size 2) requires
extra external input.  This module therefore provides:

* The candidate ladder (star / regular dichotomy, SRG classification);
* A narrowing lemma `aut_order_seven_fixedVertexCount_eq_two_of_small`
  that pins `|Fix| = 2` when `|Fix| ≤ 8` (the `K_{1,1}` edge case).

The latter is consumed by `OrderSevenEdgeFix.lean` to produce the
`EdgeFixedData σ` constructor for the §6 Lemma 16 case 3 chain.
-/

namespace Moore57

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Regular-case ladder: `H` is SRG(|Fix|, k, 0, 1)

For `σ ^ 7 = 1`, the σ-fixed induced graph `H` is `IsStrongZeroOne`
(inherits the Moore57 `λ = 0, μ = 1` parameters).  The dichotomy
"regular vs. star" follows from `StrongZeroOne.exists_isStarWithCenter_of_not_regular`.

Unlike the 11-prime case (where the star branch is contradicted by
mod-11 fix-neighbour constraint at a leaf), for the 7-prime case
**both** branches survive at the local level; we therefore expose
the regular branch separately and handle the star branch via the
narrowing lemma at the bottom of this file. -/

/-- **Regular-case `|Fix(σ)| = k² + 1`.** [done]

If the σ-fixed induced graph is regular of some degree `k`, then
`|Fix(σ)| = k² + 1`.  Uses Mathlib's `IsSRGWith.param_eq` with the
`(λ, μ) = (0, 1)` parameters inherited from the Moore57 graph. -/
theorem aut_fixedVertexCount_eq_sq_add_one_of_regular_of_pow_seven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_seven : σ ^ 7 = 1)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k) :
    fixedVertexCount σ = k * k + 1 := by
  classical
  -- |Fix| ≥ 2 by mod-7.
  have h_pp : σ ^ (7 : ℕ) ^ 1 = 1 := by simpa using pow_seven
  have hge2 : 2 ≤ fixedVertexCount σ :=
    aut_fixedVertexCount_ge_two_of_pow_seven_pow hΓ σ 1 h_pp
  have hpos : 0 < fixedVertexCount σ := by omega
  have hsrg : (autFixedInducedGraph Γ σ).IsSRGWith (fixedVertexCount σ) k 0 1 :=
    autFixedInducedGraph_isSRGWith_of_regular hΓ σ smul_adj k hreg
  have hparam :=
    SimpleGraph.IsSRGWith.param_eq (autFixedInducedGraph Γ σ) hsrg hpos
  simp only [Nat.sub_zero, mul_one] at hparam
  -- hparam : k * (k - 1) = fixedVertexCount σ - k - 1
  have hge : k + 1 ≤ fixedVertexCount σ := by
    rcases (Fintype.card_pos_iff.mp (by
      rw [fixedVertexCount_eq_card_fixedVertexSet] at hpos; exact hpos)) with ⟨v⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
    · subst hk0
      simp only [zero_add]
      exact hpos
    have hneighbors_card :
        ((autFixedInducedGraph Γ σ).neighborFinset v).card = k := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hreg v
    have hv_not :
        v ∉ ((autFixedInducedGraph Γ σ).neighborFinset v) := by
      intro hmem
      exact (autFixedInducedGraph Γ σ).irrefl
        ((SimpleGraph.mem_neighborFinset _ _ _).mp hmem)
    have hcard_ins :
        (insert v ((autFixedInducedGraph Γ σ).neighborFinset v)).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hv_not, hneighbors_card]
    have hge_card :
        k + 1 ≤ (Finset.univ : Finset (fixedVertexSet σ)).card := by
      rw [← hcard_ins]
      exact Finset.card_le_card (Finset.subset_univ _)
    rwa [fixedVertexCount_eq_card_fixedVertexSet, ← Finset.card_univ]
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · subst hk0
    simp only [Nat.zero_sub, Nat.mul_zero] at hparam
    omega
  · have hsub : fixedVertexCount σ - k - 1 = k * (k - 1) := hparam.symm
    have : fixedVertexCount σ = k * (k - 1) + k + 1 := by omega
    have hkk : k * (k - 1) + k = k * k := by
      rcases k with _ | k
      · omega
      · simp; ring
    omega

/-- **Regular degree is `≡ 1 (mod 7)`.** [done]

Each fix-induced-graph vertex's H-degree equals its σ-fixed-neighbour
count in Γ, which is `≡ 57 ≡ 1 (mod 7)`. -/
theorem aut_fixedInducedGraph_regular_degree_modEq_one_of_pow_seven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_seven : σ ^ 7 = 1)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k) :
    k ≡ 1 [MOD 7] := by
  classical
  -- |Fix| ≥ 2 ensures at least one fixed vertex.
  have h_pp : σ ^ (7 : ℕ) ^ 1 = 1 := by simpa using pow_seven
  have hge2 : 2 ≤ fixedVertexCount σ :=
    aut_fixedVertexCount_ge_two_of_pow_seven_pow hΓ σ 1 h_pp
  have hpos : 0 < Fintype.card (fixedVertexSet σ) := by
    rw [← fixedVertexCount_eq_card_fixedVertexSet]; omega
  rcases Fintype.card_pos_iff.mp hpos with ⟨x⟩
  have hdeg : (autFixedInducedGraph Γ σ).degree x = k := hreg x
  have hdeg_eq :
      (autFixedInducedGraph Γ σ).degree x =
        (autFixedNeighborFinset Γ σ (x : V)).card := by
    rw [autFixedInducedGraph_degree_eq_fixedNeighborFinset_card σ x]
    rfl
  have hk_eq : (autFixedNeighborFinset Γ σ (x : V)).card = k := by
    rw [← hdeg_eq, hdeg]
  have hxFix : σ (x : V) = (x : V) := x.property
  have hmod :
      (autFixedNeighborFinset Γ σ (x : V)).card ≡ 1 [MOD 7] :=
    aut_card_fixedNeighborFinset_modEq_one_of_pow_seven_pow hΓ σ smul_adj 1 h_pp hxFix
  rw [hk_eq] at hmod
  exact hmod

/-- **`k = 57` exclusion via `σ ≠ 1`.** [done]

If the regular degree `k = 57`, then `|Fix(σ)| = 57² + 1 = 3250 = |V|`,
forcing `σ = 1`. -/
theorem aut_fixedInducedGraph_regular_degree_ne_57_of_pow_seven_of_ne_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_seven : σ ^ 7 = 1)
    (hne : σ ≠ 1)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k) :
    k ≠ 57 := by
  intro hk57
  subst hk57
  have hcard : fixedVertexCount σ = 57 * 57 + 1 :=
    aut_fixedVertexCount_eq_sq_add_one_of_regular_of_pow_seven
      hΓ σ smul_adj pow_seven 57 hreg
  have hcardV : Fintype.card V = 3250 := hΓ.card
  have hlt : fixedVertexCount σ < Fintype.card V :=
    aut_fixedVertexCount_lt_card σ hne
  omega

/-- **Regular-case fix size dichotomy.** [done]

For `σ ^ 7 = 1, σ ≠ 1` and the σ-fixed induced graph regular of degree
`k`, we have `|Fix(σ)| ∈ {2, 50}` (corresponding to `k = 1` or `k = 7`).

Combined with the mod-7 constraint `k ≡ 1 (mod 7)` and the
Hoffman-Singleton classification `k ∈ {0,1,2,3,7,57}`, with `k = 57`
excluded by `σ ≠ 1`. -/
theorem aut_order_seven_regular_fixedVertexCount_eq_two_or_fifty
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_seven : σ ^ 7 = 1) (hne : σ ≠ 1)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k) :
    fixedVertexCount σ = 2 ∨ fixedVertexCount σ = 50 := by
  classical
  have hcard : fixedVertexCount σ = k * k + 1 :=
    aut_fixedVertexCount_eq_sq_add_one_of_regular_of_pow_seven
      hΓ σ smul_adj pow_seven k hreg
  have hsrg :
      (autFixedInducedGraph Γ σ).IsSRGWith (k * k + 1) k 0 1 := by
    rw [← hcard]
    exact autFixedInducedGraph_isSRGWith_of_regular hΓ σ smul_adj k hreg
  have hk_class :=
    srg_k_sq_plus_one_degree_classification (autFixedInducedGraph Γ σ) k hsrg
  have hk_mod : k ≡ 1 [MOD 7] :=
    aut_fixedInducedGraph_regular_degree_modEq_one_of_pow_seven
      hΓ σ smul_adj pow_seven k hreg
  have hk57_ne :=
    aut_fixedInducedGraph_regular_degree_ne_57_of_pow_seven_of_ne_one
      hΓ σ smul_adj pow_seven hne k hreg
  have hge2 : 2 ≤ fixedVertexCount σ := by
    have h_pp : σ ^ (7 : ℕ) ^ 1 = 1 := by simpa using pow_seven
    exact aut_fixedVertexCount_ge_two_of_pow_seven_pow hΓ σ 1 h_pp
  rcases hk_class with hk0 | hk1 | hk2 | hk3 | hk7 | hk57
  · -- k = 0: |Fix| = 1, but |Fix| ≥ 2. Contradiction.
    subst hk0; rw [hcard] at hge2; omega
  · -- k = 1: |Fix| = 2. ✓
    subst hk1; left; rw [hcard]
  · -- k = 2: k ≡ 1 mod 7? No (2 ≢ 1).
    subst hk2
    exact absurd hk_mod (by decide)
  · -- k = 3: k ≡ 1 mod 7? No.
    subst hk3
    exact absurd hk_mod (by decide)
  · -- k = 7: |Fix| = 50. ✓
    subst hk7; right; rw [hcard]
  · -- k = 57: excluded by σ ≠ 1.
    exact absurd hk57 hk57_ne

/-! ### Star case + dichotomy

The star case `K_{1, 1+7l}` is locally consistent with both the
mod-7 fix-size and mod-7 fix-neighbour-count constraints, so it
**cannot be excluded** by purely local arguments (unlike the 11-prime
and 13-prime cases).  We still expose the dichotomy result for
downstream consumers (Lemma 16 case 3 needs to distinguish star from
regular). -/

/-- **Star ⟹ `|Fix| ≡ 2 (mod 7)` via center degree formula.** [done]

If the σ-fixed induced graph is a star with centre `c`, then the
H-degree of `c` is `|Fix| − 1`, which must be `≡ 1 (mod 7)` by the
fix-neighbour-count constraint, hence `|Fix| ≡ 2 (mod 7)`.  This is
consistent with the global mod-7 constraint and does not yield a
contradiction. -/
theorem aut_fixedInducedGraph_star_size_modEq_two_of_pow_seven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (_smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_seven : σ ^ 7 = 1) :
    fixedVertexCount σ ≡ 2 [MOD 7] := by
  -- Global mod-7 already gives this.
  have h_pp : σ ^ (7 : ℕ) ^ 1 = 1 := by simpa using pow_seven
  exact aut_fixedVertexCount_modEq_two_of_pow_seven_pow hΓ σ 1 h_pp

/-! ### `|Fix| = 2` narrowing via small upper bound

The narrowing path used downstream: if extra information bounds
`|Fix(σ)| ≤ 8` (e.g. via the §6 Lemma 16 case 3 external constraint
that fix is an "edge" of size 2), then the mod-7 congruence
`|Fix(σ)| ≡ 2 (mod 7)` forces `|Fix(σ)| = 2`.

This is the input expected by `OrderSevenEdgeFix.lean` for the
`EdgeFixedData σ` constructor. -/

/-- **7-group fix size = 2 from small bound.** [done]

If `|Fix(σ)| ≤ 8`, the mod-7 congruence pins `|Fix(σ)| = 2`. -/
theorem aut_order_seven_fixedVertexCount_eq_two_of_small
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (pow_seven : σ ^ 7 = 1)
    (h_small : fixedVertexCount σ ≤ 8) :
    fixedVertexCount σ = 2 := by
  have h_pp : σ ^ (7 : ℕ) ^ 1 = 1 := by simpa using pow_seven
  have hmod := aut_fixedVertexCount_modEq_two_of_pow_seven_pow hΓ σ 1 h_pp
  rw [Nat.ModEq] at hmod
  omega

/-- **7-group fix-size dichotomy (full).** [done]

Under `σ ^ 7 = 1`, `|Fix(σ)| ≡ 2 (mod 7)` and `|Fix(σ)| ≥ 2`.
The possible values up to `|V| = 3250` are `2, 9, 16, 23, 30, 37,
44, 51, ...`.  Combined with the `σ ≠ 1` exclusion of the full-fix
case (`|Fix| < |V|`), and the regular-vs-star dichotomy, the surviving
candidates for `|Fix|` come from:

* Regular case (degree `k ∈ {1, 7}`): `|Fix| ∈ {2, 50}`.
* Star case `K_{1, 1+7l}`: `|Fix| = 2 + 7l` for any `l ≥ 0` with
  `2 + 7l < 3250`.

Both `|Fix| = 2` instances (regular `k=1` = star `l=0` = `K_2`)
collapse to the same edge shape.  This is the §6 Lemma 16 case 3
candidate set. -/
theorem aut_order_seven_fixedVertexCount_modEq_two
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (pow_seven : σ ^ 7 = 1) :
    fixedVertexCount σ ≡ 2 [MOD 7] := by
  have h_pp : σ ^ (7 : ℕ) ^ 1 = 1 := by simpa using pow_seven
  exact aut_fixedVertexCount_modEq_two_of_pow_seven_pow hΓ σ 1 h_pp

end Moore57
