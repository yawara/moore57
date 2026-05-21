import Moore57.Moore57Graph.Aut.InducedSubgraph
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Aut.FixedCount
import Moore57.Moore57Graph.Aut.SRGKSquarePlusOne
import Moore57.D19OnMoore57.Fixed.InducedStarEdgeFormula
import Moore57.Foundations.GraphTheory.StrongZeroOne
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Fixed-vertex structure for an order-13 Moore57 automorphism (Tier 2)

For an automorphism `σ : Equiv.Perm V` of a Moore57 graph with
`σ ^ 13 = 1` and `σ ≠ 1`, we derive the structure of Fix(σ).

Mačaj-Širáň 2010 Lemma 19 case (1) says: for prime order 13, the only
possibility is `Fix(σ) = ∅`.  This module provides the formalization,
mirroring `OrderElevenCandidates.lean`, with the key difference that
the 13-group regular case is **always contradictory** (no SRG-regular
degree `k` is mod-compatible with both `k ≡ 5 (mod 13)` and
`|Fix| = k² + 1 ≡ 0 (mod 13)` while also satisfying `σ ≠ 1` exclusion
of `k = 57`).

Logical chain (for `σ^13 = 1, σ ≠ 1`):

* `0 < |Fix(σ)|` is assumed.
* The fixed induced graph `H = Γ.induce (Fix σ)` is `IsStrongZeroOne`.
* If not regular ⟹ star (`StrongZeroOne.exists_isStarWithCenter`).
  - Star case: leaf has H-degree `1`, but mod-13 constraint says
    every fix-neighbour count is `≡ 5 (mod 13)`.  `1 ≢ 5 (mod 13)`.
* If regular ⟹ `IsSRGWith (|Fix|, k, 0, 1)`.
  - Hoffman-Singleton ⟹ `k ∈ {0, 1, 2, 3, 7, 57}`.
  - `k = 0`: |Fix| = 1, but |Fix| ≡ 0 (mod 13) forces |Fix| ∈ {0, 13, ...}.
    1 ≢ 0 (mod 13).  Excluded.
  - `k = 1`: |Fix| = 2; 2 ≢ 0 (mod 13).  Excluded.
  - `k = 2`: |Fix| = 5; 5 ≢ 0.  Excluded.
  - `k = 3`: |Fix| = 10; 10 ≢ 0.  Excluded.
  - `k = 7`: |Fix| = 50; 50 mod 13 = 11 ≢ 0.  Excluded.
  - `k = 57`: |Fix| = 3250 = |V|, forcing `σ = 1`.  Excluded by `σ ≠ 1`.

Hence `0 < |Fix(σ)|` is impossible, so `|Fix(σ)| = 0`.

-/

namespace Moore57

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Star case exclusion -/

/-- If the σ-fixed induced graph of a `σ^13 = 1` automorphism is a star,
the star has a non-center vertex (leaf), provided the fix has at least
two vertices.  For our actual use we will combine this with the
mod-13 constraint `|Fix| ≡ 0 (mod 13)` and `|Fix| > 0`, giving
`|Fix| ≥ 13 > 1`. -/
theorem aut_exists_noncenter_of_star_of_pow_thirteen
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (pow_thirteen : σ ^ 13 = 1)
    (h_pos : 0 < fixedVertexCount σ)
    {c : fixedVertexSet σ}
    (_hstar : IsStarWithCenter (autFixedInducedGraph Γ σ) c) :
    ∃ u : fixedVertexSet σ, u ≠ c := by
  classical
  -- Mod-13 constraint: |Fix| ≡ 0 (mod 13) and |Fix| > 0 ⟹ |Fix| ≥ 13.
  have hmod : fixedVertexCount σ ≡ 0 [MOD 13] := by
    have h_pp : σ ^ (13 : ℕ) ^ 1 = 1 := by simpa using pow_thirteen
    exact aut_fixedVertexCount_modEq_zero_of_pow_thirteen_pow hΓ σ 1 h_pp
  have hge13 : 13 ≤ fixedVertexCount σ := by
    rw [Nat.ModEq] at hmod
    omega
  have hcard13 : 13 ≤ Fintype.card (fixedVertexSet σ) := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using hge13
  have hcard1 : 1 < Fintype.card (fixedVertexSet σ) := by omega
  rcases Fintype.one_lt_card_iff.mp hcard1 with ⟨x, y, hxy⟩
  by_cases hxc : x = c
  · exact ⟨y, fun hyc => hxy (hxc.trans hyc.symm)⟩
  · exact ⟨x, hxc⟩

/-- **Star case exclusion**: For an automorphism σ of Moore57 with `σ^13 = 1`
and `0 < |Fix(σ)|`, the σ-fixed induced subgraph is not a star.

Proof: a leaf would have H-degree 1, but by the p=13 mod constraint, every
fix-neighbour count is ≡ 5 (mod 13) (since `57 = 13·4 + 5`).  1 ≢ 5 (mod 13). -/
theorem aut_fixedInducedGraph_not_star_of_pow_thirteen
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_thirteen : σ ^ 13 = 1)
    (h_pos : 0 < fixedVertexCount σ) :
    ¬ ∃ c : fixedVertexSet σ, IsStarWithCenter (autFixedInducedGraph Γ σ) c := by
  classical
  rintro ⟨c, hstar⟩
  rcases aut_exists_noncenter_of_star_of_pow_thirteen hΓ σ pow_thirteen h_pos hstar
    with ⟨u, hu_ne⟩
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
  -- But fix-neighbor count ≡ 5 (mod 13) for σ-fixed u.
  have huFix : σ (u : V) = (u : V) := u.property
  have h_pp : σ ^ (13 : ℕ) ^ 1 = 1 := by simpa using pow_thirteen
  have hcount_mod :
      (autFixedNeighborFinset Γ σ (u : V)).card ≡ 5 [MOD 13] :=
    aut_card_fixedNeighborFinset_modEq_five_of_pow_thirteen_pow hΓ σ smul_adj 1 h_pp huFix
  rw [hcount_one] at hcount_mod
  exact absurd hcount_mod (by decide)

/-! ### Regular case: H is SRG(|Fix|, k, 0, 1) -/

/-- The σ-fixed induced graph is regular (every vertex has the same degree),
when `σ ^ 13 = 1` on a Moore57 graph with `0 < |Fix(σ)|`. -/
theorem aut_fixedInducedGraph_regular_of_pow_thirteen
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_thirteen : σ ^ 13 = 1)
    (h_pos : 0 < fixedVertexCount σ) :
    ∃ k : ℕ, ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k := by
  classical
  by_contra hnot
  -- Not regular ⟹ exists star center (via IsStrongZeroOne dichotomy).
  have hstrong : IsStrongZeroOne (autFixedInducedGraph Γ σ) :=
    autFixedInducedGraph_isStrongZeroOne hΓ σ smul_adj
  rcases hstrong.exists_isStarWithCenter_of_not_regular hnot with ⟨c, hstar⟩
  -- This contradicts the star case (excluded for σ^13=1).
  exact aut_fixedInducedGraph_not_star_of_pow_thirteen hΓ σ smul_adj
    pow_thirteen h_pos ⟨c, hstar⟩

/-- Regular case: the fixed-vertex count equals `k² + 1`. -/
theorem aut_fixedVertexCount_eq_sq_add_one_of_regular_of_pow_thirteen
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (_pow_thirteen : σ ^ 13 = 1)
    (h_pos : 0 < fixedVertexCount σ)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k) :
    fixedVertexCount σ = k * k + 1 := by
  classical
  have hsrg : (autFixedInducedGraph Γ σ).IsSRGWith (fixedVertexCount σ) k 0 1 :=
    autFixedInducedGraph_isSRGWith_of_regular hΓ σ smul_adj k hreg
  have hparam :=
    SimpleGraph.IsSRGWith.param_eq (autFixedInducedGraph Γ σ) hsrg h_pos
  simp only [Nat.sub_zero, mul_one] at hparam
  -- hparam : k * (k - 1) = fixedVertexCount σ - k - 1
  have hge : k + 1 ≤ fixedVertexCount σ := by
    rcases (Fintype.card_pos_iff.mp (by
      rw [fixedVertexCount_eq_card_fixedVertexSet] at h_pos; exact h_pos)) with ⟨v⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
    · subst hk0
      simp only [zero_add]
      exact h_pos
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

/-- For `σ ^ 13 = 1` automorphism of Moore57 with `0 < |Fix(σ)|`,
the fixed-vertex count equals `k² + 1` for some regular degree `k`. -/
theorem aut_fixedVertexCount_eq_sq_add_one_of_pow_thirteen
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_thirteen : σ ^ 13 = 1)
    (h_pos : 0 < fixedVertexCount σ) :
    ∃ k : ℕ, fixedVertexCount σ = k * k + 1 ∧
      ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k := by
  rcases aut_fixedInducedGraph_regular_of_pow_thirteen hΓ σ smul_adj pow_thirteen h_pos
    with ⟨k, hreg⟩
  refine ⟨k, ?_, hreg⟩
  exact aut_fixedVertexCount_eq_sq_add_one_of_regular_of_pow_thirteen
    hΓ σ smul_adj pow_thirteen h_pos k hreg

/-- The regular degree `k` satisfies `k ≡ 5 (mod 13)`.

Reason: each fixed vertex's H-degree = its σ-fixed-neighbour count in Γ,
which is `≡ 57 ≡ 5 (mod 13)`. -/
theorem aut_fixedInducedGraph_regular_degree_modEq_five_of_pow_thirteen
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_thirteen : σ ^ 13 = 1)
    (h_pos : 0 < fixedVertexCount σ)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k) :
    k ≡ 5 [MOD 13] := by
  classical
  -- Pick any fixed vertex x.  Its H-degree is k, equal to fix-neighbor count.
  have hcardpos : 0 < Fintype.card (fixedVertexSet σ) := by
    rw [← fixedVertexCount_eq_card_fixedVertexSet]; exact h_pos
  rcases Fintype.card_pos_iff.mp hcardpos with ⟨x⟩
  have hdeg : (autFixedInducedGraph Γ σ).degree x = k := hreg x
  have hdeg_eq :
      (autFixedInducedGraph Γ σ).degree x =
        (autFixedNeighborFinset Γ σ (x : V)).card := by
    rw [autFixedInducedGraph_degree_eq_fixedNeighborFinset_card σ x]
    rfl
  have hk_eq : (autFixedNeighborFinset Γ σ (x : V)).card = k := by
    rw [← hdeg_eq, hdeg]
  have hxFix : σ (x : V) = (x : V) := x.property
  have h_pp : σ ^ (13 : ℕ) ^ 1 = 1 := by simpa using pow_thirteen
  have hmod :
      (autFixedNeighborFinset Γ σ (x : V)).card ≡ 5 [MOD 13] :=
    aut_card_fixedNeighborFinset_modEq_five_of_pow_thirteen_pow
      hΓ σ smul_adj 1 h_pp hxFix
  rw [hk_eq] at hmod
  exact hmod

/-! ### Stage 5: k = 57 exclusion via σ ≠ 1 -/

/-- If the regular degree `k` equals 57, then `|Fix(σ)| = 3250 = |V|`,
forcing `σ = 1`.  So for `σ ≠ 1` the degree is `≠ 57`. -/
theorem aut_fixedInducedGraph_regular_degree_ne_57_of_pow_thirteen_of_ne_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_thirteen : σ ^ 13 = 1)
    (hne : σ ≠ 1)
    (h_pos : 0 < fixedVertexCount σ)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k) :
    k ≠ 57 := by
  intro hk57
  subst hk57
  have hcard : fixedVertexCount σ = 57 * 57 + 1 :=
    aut_fixedVertexCount_eq_sq_add_one_of_regular_of_pow_thirteen
      hΓ σ smul_adj pow_thirteen h_pos 57 hreg
  have hcardV : Fintype.card V = 3250 := hΓ.card
  have hlt : fixedVertexCount σ < Fintype.card V :=
    aut_fixedVertexCount_lt_card σ hne
  omega

/-! ### Stage 6: `|Fix(σ)| = 0` -/

/-- **The 13-group regular case is always contradictory.**

For `σ^13 = 1, σ ≠ 1` on Moore57 with `0 < |Fix(σ)|`, no Hoffman-Singleton
degree `k` is mod-compatible with both `k ≡ 5 (mod 13)` (regular degree
constraint) and `|Fix| = k² + 1 ≡ 0 (mod 13)` (global mod-13 constraint),
while also avoiding `k = 57` (excluded by `σ ≠ 1`).  Hence `0 < |Fix(σ)|`
is impossible. -/
theorem aut_order_thirteen_fixedVertexCount_eq_zero
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_thirteen : σ ^ 13 = 1) (hne : σ ≠ 1) :
    fixedVertexCount σ = 0 := by
  classical
  by_contra h_ne_zero
  have h_pos : 0 < fixedVertexCount σ := Nat.pos_of_ne_zero h_ne_zero
  -- Get the regular SRG: |Fix| = k² + 1.
  rcases aut_fixedVertexCount_eq_sq_add_one_of_pow_thirteen
    hΓ σ smul_adj pow_thirteen h_pos with ⟨k, hcard, hreg⟩
  -- SRG classification: k ∈ {0, 1, 2, 3, 7, 57}.
  have hsrg :
      (autFixedInducedGraph Γ σ).IsSRGWith (k * k + 1) k 0 1 := by
    rw [← hcard]
    exact autFixedInducedGraph_isSRGWith_of_regular hΓ σ smul_adj k hreg
  have hk_class :=
    srg_k_sq_plus_one_degree_classification (autFixedInducedGraph Γ σ) k hsrg
  -- Global mod-13: |Fix| ≡ 0 (mod 13).
  have h_pp : σ ^ (13 : ℕ) ^ 1 = 1 := by simpa using pow_thirteen
  have hcardmod : fixedVertexCount σ ≡ 0 [MOD 13] :=
    aut_fixedVertexCount_modEq_zero_of_pow_thirteen_pow hΓ σ 1 h_pp
  -- k=57 excluded by σ ≠ 1.
  have hk57_ne :=
    aut_fixedInducedGraph_regular_degree_ne_57_of_pow_thirteen_of_ne_one
      hΓ σ smul_adj pow_thirteen hne h_pos k hreg
  -- Case on k ∈ {0, 1, 2, 3, 7, 57}: in each case, |Fix| = k²+1 is not
  -- ≡ 0 (mod 13) (except k=57 which is excluded by σ ≠ 1).
  rcases hk_class with hk0 | hk1 | hk2 | hk3 | hk7 | hk57
  · -- k = 0: |Fix| = 1.  1 ≡ 0 (mod 13)? No.
    subst hk0
    rw [hcard] at hcardmod
    exact absurd hcardmod (by decide)
  · -- k = 1: |Fix| = 2.  2 ≡ 0 (mod 13)? No.
    subst hk1
    rw [hcard] at hcardmod
    exact absurd hcardmod (by decide)
  · -- k = 2: |Fix| = 5.  5 ≡ 0 (mod 13)? No.
    subst hk2
    rw [hcard] at hcardmod
    exact absurd hcardmod (by decide)
  · -- k = 3: |Fix| = 10.  10 ≡ 0 (mod 13)? No.
    subst hk3
    rw [hcard] at hcardmod
    exact absurd hcardmod (by decide)
  · -- k = 7: |Fix| = 50.  50 ≡ 0 (mod 13)? 50 = 13·3 + 11, so 50 ≡ 11 ≠ 0.
    subst hk7
    rw [hcard] at hcardmod
    exact absurd hcardmod (by decide)
  · -- k = 57: excluded by σ ≠ 1.
    exact absurd hk57 hk57_ne

end Moore57
