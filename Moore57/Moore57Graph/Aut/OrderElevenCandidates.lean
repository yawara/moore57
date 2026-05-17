import Moore57.Moore57Graph.Aut.InducedSubgraph
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Aut.FixedCount
import Moore57.D19OnMoore57.Fixed.InducedStarEdgeFormula
import Moore57.Foundations.GraphTheory.StrongZeroOne
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Fixed-vertex structure for an order-11 Moore57 automorphism (Tier 2)

For an automorphism `σ : Equiv.Perm V` of a Moore57 graph with
`σ ^ 11 = 1` and `σ ≠ 1`, we derive the structure of Fix(σ).

Mačaj-Širáň 2010 Lemma 4 (4) says: for prime order 11, only the pentagon
case occurs in Aschbacher's classification (`|X| | 11·5`). This module
provides the formalization, step-by-step:

* `aut_fixedInducedGraph_not_star_of_pow_eleven` — the σ-fixed induced
  graph is not a star (`degree(leaf) = 1` but `fix-nbr count ≡ 2 (mod 11)`).
* Subsequent files build the regular `SRG(k²+1, k, 0, 1)` chain to derive
  k = 2, hence Fix(σ) ≅ C_5.
-/

namespace Moore57

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Star case exclusion -/

/-- If the σ-fixed induced graph of a `σ^11 = 1` automorphism is a star,
the star has a non-center vertex (i.e., leaf), since `|Fix(σ)| ≥ 5 > 1`. -/
theorem aut_exists_noncenter_of_star_of_pow_eleven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (pow_eleven : σ ^ 11 = 1)
    {c : fixedVertexSet σ}
    (_hstar : IsStarWithCenter (autFixedInducedGraph Γ σ) c) :
    ∃ u : fixedVertexSet σ, u ≠ c := by
  classical
  have hge5 : 5 ≤ fixedVertexCount σ :=
    aut_fixedVertexCount_ge_five_of_pow_eleven hΓ σ pow_eleven
  have hcard5 : 5 ≤ Fintype.card (fixedVertexSet σ) := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using hge5
  have hcard1 : 1 < Fintype.card (fixedVertexSet σ) := by omega
  rcases Fintype.one_lt_card_iff.mp hcard1 with ⟨x, y, hxy⟩
  by_cases hxc : x = c
  · exact ⟨y, fun hyc => hxy (hxc.trans hyc.symm)⟩
  · exact ⟨x, hxc⟩

/-- **Star case exclusion**: For an automorphism σ of Moore57 with `σ^11 = 1`
and `σ ≠ 1`, the σ-fixed induced subgraph is not a star.

Proof: a leaf would have H-degree 1, but by the p=11 mod constraint, every
fix-neighbour count is ≡ 2 (mod 11) (since `57 = 11·5 + 2`). 1 ≢ 2 (mod 11). -/
theorem aut_fixedInducedGraph_not_star_of_pow_eleven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1) :
    ¬ ∃ c : fixedVertexSet σ, IsStarWithCenter (autFixedInducedGraph Γ σ) c := by
  classical
  rintro ⟨c, hstar⟩
  rcases aut_exists_noncenter_of_star_of_pow_eleven hΓ σ pow_eleven hstar with ⟨u, hu_ne⟩
  -- u is a leaf, so its H-degree is 1.
  have hdeg_one : (autFixedInducedGraph Γ σ).degree u = 1 :=
    hstar.degree_noncenter_eq_one hu_ne
  -- The H-degree of u equals the σ-fixed-neighbour count of (u : V).
  have hdeg_eq : (autFixedInducedGraph Γ σ).degree u =
      (autFixedNeighborFinset Γ σ (u : V)).card := by
    rw [autFixedInducedGraph_degree_eq_fixedNeighborFinset_card σ u]
    rfl
  have hcount_one : (autFixedNeighborFinset Γ σ (u : V)).card = 1 := by
    rw [← hdeg_eq, hdeg_one]
  -- But fix-neighbor count ≡ 2 (mod 11) for σ-fixed u.
  have huFix : σ (u : V) = (u : V) := u.property
  have hcount_mod :
      (autFixedNeighborFinset Γ σ (u : V)).card ≡ 2 [MOD 11] :=
    aut_card_fixedNeighborFinset_modEq_two_of_pow_eleven hΓ σ smul_adj pow_eleven huFix
  rw [hcount_one] at hcount_mod
  exact absurd hcount_mod (by decide)

/-! ### Regular case: H is SRG(|Fix|, k, 0, 1) -/

/-- The σ-fixed induced graph is regular (every vertex has the same degree),
when `σ ^ 11 = 1` on a Moore57 graph. -/
theorem aut_fixedInducedGraph_regular_of_pow_eleven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1) :
    ∃ k : ℕ, ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k := by
  classical
  by_contra hnot
  -- Not regular ⟹ exists star center (via IsStrongZeroOne dichotomy).
  have hstrong : IsStrongZeroOne (autFixedInducedGraph Γ σ) :=
    autFixedInducedGraph_isStrongZeroOne hΓ σ smul_adj
  rcases hstrong.exists_isStarWithCenter_of_not_regular hnot with ⟨c, hstar⟩
  -- This contradicts Stage 2 (star case excluded for σ^11=1).
  exact aut_fixedInducedGraph_not_star_of_pow_eleven hΓ σ smul_adj pow_eleven ⟨c, hstar⟩

/-- Regular case: the fixed-vertex count equals `k² + 1`. -/
theorem aut_fixedVertexCount_eq_sq_add_one_of_regular_of_pow_eleven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k) :
    fixedVertexCount σ = k * k + 1 := by
  classical
  have hpos : 0 < fixedVertexCount σ :=
    aut_fixedVertexCount_pos_of_pow_eleven hΓ σ pow_eleven
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
      simp
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
  · -- k ≥ 1: k*(k-1) = n - k - 1, with n ≥ k + 1
    -- ⟹ n = k(k-1) + k + 1 = k² - k + k + 1 = k² + 1
    have hsub : fixedVertexCount σ - k - 1 = k * (k - 1) := hparam.symm
    have : fixedVertexCount σ = k * (k - 1) + k + 1 := by omega
    have hkk : k * (k - 1) + k = k * k := by
      rcases k with _ | k
      · omega
      · simp; ring
    omega

/-- For `σ ^ 11 = 1` automorphism of Moore57, the fixed-vertex count equals
`k² + 1` for some regular degree `k`. -/
theorem aut_fixedVertexCount_eq_sq_add_one_of_pow_eleven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1) :
    ∃ k : ℕ, fixedVertexCount σ = k * k + 1 ∧
      ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k := by
  rcases aut_fixedInducedGraph_regular_of_pow_eleven hΓ σ smul_adj pow_eleven with ⟨k, hreg⟩
  refine ⟨k, ?_, hreg⟩
  exact aut_fixedVertexCount_eq_sq_add_one_of_regular_of_pow_eleven
    hΓ σ smul_adj pow_eleven k hreg

/-- The regular degree `k` satisfies `k ≡ 2 (mod 11)`.

Reason: each fixed vertex's H-degree = its σ-fixed-neighbour count in Γ,
which is `≡ 57 ≡ 2 (mod 11)`. -/
theorem aut_fixedInducedGraph_regular_degree_modEq_two_of_pow_eleven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k) :
    k ≡ 2 [MOD 11] := by
  classical
  -- We need at least one fixed vertex. |Fix(σ)| ≥ 5 from Cauchy.
  have hge5 : 5 ≤ fixedVertexCount σ :=
    aut_fixedVertexCount_ge_five_of_pow_eleven hΓ σ pow_eleven
  have hpos : 0 < Fintype.card (fixedVertexSet σ) := by
    rw [← fixedVertexCount_eq_card_fixedVertexSet]; omega
  rcases Fintype.card_pos_iff.mp hpos with ⟨x⟩
  -- Pick any fixed vertex x. Its H-degree is k, equal to fix-neighbor count.
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
      (autFixedNeighborFinset Γ σ (x : V)).card ≡ 2 [MOD 11] :=
    aut_card_fixedNeighborFinset_modEq_two_of_pow_eleven hΓ σ smul_adj pow_eleven hxFix
  rw [hk_eq] at hmod
  exact hmod

end Moore57
