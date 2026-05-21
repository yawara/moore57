import Moore57.Moore57Graph.Aut.InducedSubgraph
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Aut.FixedCount
import Moore57.Moore57Graph.Aut.SRGKSquarePlusOne
import Moore57.D19OnMoore57.Fixed.InducedStarEdgeFormula
import Moore57.Foundations.GraphTheory.StrongZeroOne
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Fixed-vertex structure for an order-3 Moore57 automorphism (Tier 2)

For an automorphism `σ : Equiv.Perm V` of a Moore57 graph with `σ ^ 3 = 1`
and `σ ≠ 1`, we derive the structure of Fix(σ).

Mačaj-Širáň 2010 Lemma 17 says: for a 3-group `X`, `Fix(X)` is either a
singleton (case (2)) or the Petersen graph (case (1)).  In the prime case
`σ^3 = 1`, the same dichotomy holds and this module formalises it,
mirroring `OrderElevenCandidates.lean` / `OrderThirteenCandidates.lean`.

Unlike the 11-group and 13-group cases (where the regular SRG branch
narrows to a *unique* `k` via mod-`p` constraints), the 3-group case is a
genuine **two-way classification**: both `k = 0` (giving `|Fix| = 1`, the
singleton case) and `k = 3` (giving `|Fix| = 10`, the Petersen case) are
compatible with `k ≡ 0 (mod 3)` and HS list `{0, 1, 2, 3, 7, 57}`.

Logical chain (for `σ^3 = 1, σ ≠ 1`):

* `0 < |Fix(σ)|` is unconditional (`aut_fixedVertexCount_pos_of_pow_three_pow`).
* The fixed induced graph `H = Γ.induce (Fix σ)` is `IsStrongZeroOne`.
* If not regular ⟹ star (`StrongZeroOne.exists_isStarWithCenter`).
  - Star case: leaf has H-degree `1`, but mod-3 constraint says
    every fix-neighbour count is `≡ 0 (mod 3)`.  `1 ≢ 0 (mod 3)`.
* If regular ⟹ `IsSRGWith (|Fix|, k, 0, 1)`.
  - Hoffman-Singleton ⟹ `k ∈ {0, 1, 2, 3, 7, 57}`.
  - Intersect with `k ≡ 0 (mod 3)`: `k ∈ {0, 3, 57}`.
  - `k = 0`: |Fix| = 1, singleton case.
  - `k = 3`: |Fix| = 10, Petersen case.
  - `k = 57`: |Fix| = 3250 = |V|, forcing `σ = 1`.  Excluded by `σ ≠ 1`.

Hence `|Fix(σ)| ∈ {1, 10}`.
-/

namespace Moore57

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Star case exclusion -/

/-- If the σ-fixed induced graph is a star and has at least two fixed
vertices, then a non-center vertex (leaf) exists. -/
theorem aut_exists_noncenter_of_star_of_pow_three
    (_hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (_pow_three : σ ^ 3 = 1)
    (h_ge2 : 2 ≤ fixedVertexCount σ)
    {c : fixedVertexSet σ}
    (_hstar : IsStarWithCenter (autFixedInducedGraph Γ σ) c) :
    ∃ u : fixedVertexSet σ, u ≠ c := by
  classical
  have hcard2 : 2 ≤ Fintype.card (fixedVertexSet σ) := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using h_ge2
  have hcard1 : 1 < Fintype.card (fixedVertexSet σ) := by omega
  rcases Fintype.one_lt_card_iff.mp hcard1 with ⟨x, y, hxy⟩
  by_cases hxc : x = c
  · exact ⟨y, fun hyc => hxy (hxc.trans hyc.symm)⟩
  · exact ⟨x, hxc⟩

/-- **Star case exclusion**: For an automorphism σ of Moore57 with `σ^3 = 1`
and `2 ≤ |Fix(σ)|`, the σ-fixed induced subgraph is not a star.

Proof: a leaf would have H-degree 1, but by the p=3 mod constraint, every
fix-neighbour count is ≡ 0 (mod 3) (since `57 = 3·19`).  `1 ≢ 0 (mod 3)`. -/
theorem aut_fixedInducedGraph_not_star_of_pow_three
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_three : σ ^ 3 = 1)
    (h_ge2 : 2 ≤ fixedVertexCount σ) :
    ¬ ∃ c : fixedVertexSet σ, IsStarWithCenter (autFixedInducedGraph Γ σ) c := by
  classical
  rintro ⟨c, hstar⟩
  rcases aut_exists_noncenter_of_star_of_pow_three hΓ σ pow_three h_ge2 hstar
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
  -- But fix-neighbor count ≡ 0 (mod 3) for σ-fixed u.
  have huFix : σ (u : V) = (u : V) := u.property
  have h_pp : σ ^ (3 : ℕ) ^ 1 = 1 := by simpa using pow_three
  have hcount_mod :
      (autFixedNeighborFinset Γ σ (u : V)).card ≡ 0 [MOD 3] :=
    aut_card_fixedNeighborFinset_modEq_zero_of_pow_three_pow hΓ σ smul_adj 1 h_pp huFix
  rw [hcount_one] at hcount_mod
  exact absurd hcount_mod (by decide)

/-! ### Regular case: H is SRG(|Fix|, k, 0, 1) -/

/-- The σ-fixed induced graph is regular (every vertex has the same degree),
when `σ ^ 3 = 1` on a Moore57 graph.

This holds **unconditionally** for the 3-prime case: if `|Fix(σ)| = 1` the
graph is trivially regular (degree 0), and if `|Fix(σ)| ≥ 2` (in fact ≥ 4
by `|Fix| ≡ 1 (mod 3)`) the star case is excluded by mod-3. -/
theorem aut_fixedInducedGraph_regular_of_pow_three
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_three : σ ^ 3 = 1) :
    ∃ k : ℕ, ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k := by
  classical
  by_contra hnot
  -- Not regular ⟹ exists star center (via IsStrongZeroOne dichotomy).
  have hstrong : IsStrongZeroOne (autFixedInducedGraph Γ σ) :=
    autFixedInducedGraph_isStrongZeroOne hΓ σ smul_adj
  rcases hstrong.exists_isStarWithCenter_of_not_regular hnot with ⟨c, hstar⟩
  -- Not regular ⟹ ≥ 2 fixed vertices.  Indeed `exists_degree_ne_of_not_regular`
  -- supplies (v, w) with degrees differing, so they are distinct.
  have h_ge2 : 2 ≤ fixedVertexCount σ := by
    rcases IsStrongZeroOne.exists_degree_ne_of_not_regular
      (autFixedInducedGraph Γ σ) hnot with ⟨v, w, hdeg⟩
    have hvw : v ≠ w := by
      intro hvw_eq; subst hvw_eq; exact hdeg rfl
    have hcard_ge : 2 ≤ Fintype.card (fixedVertexSet σ) := by
      have h2 : 1 < Fintype.card (fixedVertexSet σ) :=
        Fintype.one_lt_card_iff.mpr ⟨v, w, hvw⟩
      omega
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using hcard_ge
  -- Contradicts star case exclusion (Stage 2).
  exact aut_fixedInducedGraph_not_star_of_pow_three hΓ σ smul_adj pow_three h_ge2
    ⟨c, hstar⟩

/-- Regular case: the fixed-vertex count equals `k² + 1`. -/
theorem aut_fixedVertexCount_eq_sq_add_one_of_regular_of_pow_three
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_three : σ ^ 3 = 1)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k) :
    fixedVertexCount σ = k * k + 1 := by
  classical
  have h_pos : 0 < fixedVertexCount σ := by
    have h_pp : σ ^ (3 : ℕ) ^ 1 = 1 := by simpa using pow_three
    exact aut_fixedVertexCount_pos_of_pow_three_pow hΓ σ 1 h_pp
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

/-- For `σ ^ 3 = 1` automorphism of Moore57, the fixed-vertex count equals
`k² + 1` for some regular degree `k`. -/
theorem aut_fixedVertexCount_eq_sq_add_one_of_pow_three
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_three : σ ^ 3 = 1) :
    ∃ k : ℕ, fixedVertexCount σ = k * k + 1 ∧
      ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k := by
  rcases aut_fixedInducedGraph_regular_of_pow_three hΓ σ smul_adj pow_three
    with ⟨k, hreg⟩
  refine ⟨k, ?_, hreg⟩
  exact aut_fixedVertexCount_eq_sq_add_one_of_regular_of_pow_three
    hΓ σ smul_adj pow_three k hreg

/-- The regular degree `k` satisfies `k ≡ 0 (mod 3)`.

Reason: each fixed vertex's H-degree = its σ-fixed-neighbour count in Γ,
which is `≡ 57 ≡ 0 (mod 3)`. -/
theorem aut_fixedInducedGraph_regular_degree_modEq_zero_of_pow_three
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_three : σ ^ 3 = 1)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k) :
    k ≡ 0 [MOD 3] := by
  classical
  have h_pos : 0 < fixedVertexCount σ := by
    have h_pp : σ ^ (3 : ℕ) ^ 1 = 1 := by simpa using pow_three
    exact aut_fixedVertexCount_pos_of_pow_three_pow hΓ σ 1 h_pp
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
  have h_pp : σ ^ (3 : ℕ) ^ 1 = 1 := by simpa using pow_three
  have hmod :
      (autFixedNeighborFinset Γ σ (x : V)).card ≡ 0 [MOD 3] :=
    aut_card_fixedNeighborFinset_modEq_zero_of_pow_three_pow
      hΓ σ smul_adj 1 h_pp hxFix
  rw [hk_eq] at hmod
  exact hmod

/-! ### Stage 5: k = 57 exclusion via σ ≠ 1 -/

/-- If the regular degree `k` equals 57, then `|Fix(σ)| = 3250 = |V|`,
forcing `σ = 1`.  So for `σ ≠ 1` the degree is `≠ 57`. -/
theorem aut_fixedInducedGraph_regular_degree_ne_57_of_pow_three_of_ne_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_three : σ ^ 3 = 1)
    (hne : σ ≠ 1)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k) :
    k ≠ 57 := by
  intro hk57
  subst hk57
  have hcard : fixedVertexCount σ = 57 * 57 + 1 :=
    aut_fixedVertexCount_eq_sq_add_one_of_regular_of_pow_three
      hΓ σ smul_adj pow_three 57 hreg
  have hcardV : Fintype.card V = 3250 := hΓ.card
  have hlt : fixedVertexCount σ < Fintype.card V :=
    aut_fixedVertexCount_lt_card σ hne
  omega

/-! ### Stage 6: `|Fix(σ)| ∈ {1, 10}` (singleton or Petersen-count) -/

/-- **Main theorem for Stage 6**: For an automorphism `σ` of Moore57 with
`σ^3 = 1` and `σ ≠ 1`, the fixed-vertex count is exactly `1` or `10`.

Reasoning:
1. (Stage 3) Regular case ⟹ `|Fix(σ)| = k² + 1` for some `k`, with
   `k ≡ 0 (mod 3)`.
2. (Stage 4 / HS) `SRG(k²+1, k, 0, 1)` exists ⟹ `k ∈ {0, 1, 2, 3, 7, 57}`.
3. Intersecting with `k ≡ 0 (mod 3)`: `k ∈ {0, 3, 57}`.
4. (Stage 5) `k = 57` excluded by `σ ≠ 1`.
5. `k = 0`: `|Fix| = 1` (singleton case).
6. `k = 3`: `|Fix| = 10` (Petersen case).

The two-way split is the Mačaj-Širáň §6 Lem 17 dichotomy at the prime
level. -/
theorem aut_order_three_fixedVertexCount_eq_one_or_ten
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_three : σ ^ 3 = 1) (hne : σ ≠ 1) :
    fixedVertexCount σ = 1 ∨ fixedVertexCount σ = 10 := by
  classical
  rcases aut_fixedVertexCount_eq_sq_add_one_of_pow_three hΓ σ smul_adj pow_three
    with ⟨k, hcard, hreg⟩
  -- SRG classification
  have hsrg :
      (autFixedInducedGraph Γ σ).IsSRGWith (k * k + 1) k 0 1 := by
    rw [← hcard]
    exact autFixedInducedGraph_isSRGWith_of_regular hΓ σ smul_adj k hreg
  have hk_class :=
    srg_k_sq_plus_one_degree_classification (autFixedInducedGraph Γ σ) k hsrg
  have hk_mod : k ≡ 0 [MOD 3] :=
    aut_fixedInducedGraph_regular_degree_modEq_zero_of_pow_three
      hΓ σ smul_adj pow_three k hreg
  have hk57_ne :=
    aut_fixedInducedGraph_regular_degree_ne_57_of_pow_three_of_ne_one
      hΓ σ smul_adj pow_three hne k hreg
  -- Case on k ∈ {0, 1, 2, 3, 7, 57}.
  rcases hk_class with hk0 | hk1 | hk2 | hk3 | hk7 | hk57
  · -- k = 0: |Fix| = 1.
    subst hk0
    left
    rw [hcard]
  · -- k = 1: 1 ≢ 0 (mod 3).  Excluded.
    subst hk1
    exact absurd hk_mod (by decide)
  · -- k = 2: 2 ≢ 0 (mod 3).  Excluded.
    subst hk2
    exact absurd hk_mod (by decide)
  · -- k = 3: |Fix| = 10.
    subst hk3
    right
    rw [hcard]
  · -- k = 7: 7 ≢ 0 (mod 3).  Excluded.
    subst hk7
    exact absurd hk_mod (by decide)
  · -- k = 57: excluded by σ ≠ 1 (Stage 5).
    exact absurd hk57 hk57_ne

/-! ### Stage 6 (refined): include the SRG degree witness

For the Petersen branch, the consumer wants to know not just
`|Fix| = 10` but also that the σ-fixed induced graph is
`IsSRGWith 10 3 0 1` (since this is the SRG signature of the Petersen
graph).  We expose both pieces. -/

/-- **Stage 6 with SRG-witness**: For an automorphism `σ` of Moore57 with
`σ^3 = 1` and `σ ≠ 1`, *either*
* `fixedVertexCount σ = 1`, or
* `fixedVertexCount σ = 10` *and* the σ-fixed induced graph is
  `IsSRGWith 10 3 0 1` (which is the Petersen SRG signature). -/
theorem aut_order_three_fixedVertexCount_singleton_or_petersenSRG
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_three : σ ^ 3 = 1) (hne : σ ≠ 1) :
    fixedVertexCount σ = 1 ∨
      (fixedVertexCount σ = 10 ∧
        (autFixedInducedGraph Γ σ).IsSRGWith 10 3 0 1) := by
  classical
  rcases aut_fixedVertexCount_eq_sq_add_one_of_pow_three hΓ σ smul_adj pow_three
    with ⟨k, hcard, hreg⟩
  -- SRG classification
  have hsrg :
      (autFixedInducedGraph Γ σ).IsSRGWith (k * k + 1) k 0 1 := by
    rw [← hcard]
    exact autFixedInducedGraph_isSRGWith_of_regular hΓ σ smul_adj k hreg
  have hk_class :=
    srg_k_sq_plus_one_degree_classification (autFixedInducedGraph Γ σ) k hsrg
  have hk_mod : k ≡ 0 [MOD 3] :=
    aut_fixedInducedGraph_regular_degree_modEq_zero_of_pow_three
      hΓ σ smul_adj pow_three k hreg
  have hk57_ne :=
    aut_fixedInducedGraph_regular_degree_ne_57_of_pow_three_of_ne_one
      hΓ σ smul_adj pow_three hne k hreg
  rcases hk_class with hk0 | hk1 | hk2 | hk3 | hk7 | hk57
  · -- k = 0
    subst hk0
    left; rw [hcard]
  · -- k = 1: excluded by mod-3
    subst hk1
    exact absurd hk_mod (by decide)
  · -- k = 2: excluded by mod-3
    subst hk2
    exact absurd hk_mod (by decide)
  · -- k = 3: |Fix| = 10 and SRG(10, 3, 0, 1)
    subst hk3
    right
    refine ⟨?_, ?_⟩
    · rw [hcard]
    · -- We have hsrg : IsSRGWith (3*3 + 1) 3 0 1 = IsSRGWith 10 3 0 1
      have : (3 : ℕ) * 3 + 1 = 10 := by decide
      rw [this] at hsrg
      exact hsrg
  · -- k = 7: excluded by mod-3
    subst hk7
    exact absurd hk_mod (by decide)
  · -- k = 57: excluded by σ ≠ 1
    exact absurd hk57 hk57_ne

end Moore57
