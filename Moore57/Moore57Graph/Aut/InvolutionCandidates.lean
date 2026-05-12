import Moore57.Moore57Graph.Aut.InducedSubgraph
import Moore57.Moore57Graph.Aut.TraceIntegrality
import Moore57.Moore57Graph.Aut.FixedCount
import Moore57.Moore57Graph.InvolutionEdgeCountFormula
import Moore57.Foundations.GroupAction.InvolutionParity
import Moore57.D19OnMoore57.Reflection.FixedCountStarCandidates
import Moore57.D19OnMoore57.Involution.HigmanCountArithmetic
import Moore57.D19OnMoore57.Fixed.InducedStarEdgeFormula
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Fixed-vertex count candidates for an involutive Moore57 automorphism (Tier 2)

For an involutive automorphism `σ : Equiv.Perm V` of a Moore57 graph with
`σ ≠ 1`, the fixed-vertex count `fixedVertexCount σ` is forced to lie in

```
{0, 2, 6, 10, 16, 26, 36, 46, 50, 56}.
```

The proof case-splits on whether the σ-fixed induced subgraph is regular or
a star (using `IsStrongZeroOne` inherited from Moore57's `(λ, μ) = (0, 1)`):

* **Regular case** (`fixedVertexCount σ > 0`): the induced graph is
  `IsSRGWith (a₀, k, 0, 1)`, hence `a₀ = k² + 1` by
  `SimpleGraph.IsSRGWith.param_eq`. The involution edge-count formula plus
  parity forces `k ∈ {1, 3, 5, 7}` (larger odd `k` makes `a₁ < 0`).
* **Star case**: the Higman/star-edge mod-5 congruence together with parity
  and the ambient-degree bound forces `a₀ ∈ {6, 16, 26, 36, 46, 56}`.
* **`a₀ = 0` case** is the empty regular subgraph, captured separately.

The corollary `aut_involution_fixedVertexCount_not_modEq_one` says that the
count is never `≡ 1 (mod 19)`; this is what the `C₃₈` non-existence proof
needs (the `C₃₈` commutation forces the involution's fixed count to be
`≡ 1 (mod 19)`, contradicting the candidate list).
-/

namespace Moore57

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Upper bound for the star case -/

/-- If the σ-fixed induced subgraph is a star with center `c`, then
`fixedVertexCount σ ≤ 58` (the star center degree is bounded by the ambient
degree `57`). -/
theorem aut_fixedVertexCount_le_fiftyEight_of_star
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    {c : fixedVertexSet σ}
    (hstar : IsStarWithCenter (autFixedInducedGraph Γ σ) c) :
    fixedVertexCount σ ≤ 58 := by
  classical
  have hcenter_degree :
      (autFixedInducedGraph Γ σ).degree c =
        fixedVertexCount σ - 1 := by
    have hstar_degree :=
      IsStarWithCenter.degree_center_eq_card_sub_one
        (G := autFixedInducedGraph Γ σ) (c := c) hstar
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using hstar_degree
  have hdegree_filter :
      (autFixedInducedGraph Γ σ).degree c =
        ((Γ.neighborFinset (c : V)).filter fun w => σ w = w).card :=
    autFixedInducedGraph_degree_eq_fixedNeighborFinset_card σ c
  have hfilter_le :
      ((Γ.neighborFinset (c : V)).filter fun w => σ w = w).card ≤
        (Γ.neighborFinset (c : V)).card :=
    Finset.card_filter_le _ _
  have hdegree_le :
      (autFixedInducedGraph Γ σ).degree c ≤ 57 := by
    rw [hdegree_filter]
    rw [SimpleGraph.card_neighborFinset_eq_degree,
      hΓ.regular.degree_eq (c : V)] at hfilter_le
    exact hfilter_le
  have hpos : 0 < fixedVertexCount σ := by
    rw [fixedVertexCount_eq_card_fixedVertexSet]
    exact Fintype.card_pos_iff.mpr ⟨c⟩
  omega

/-! ### Star edge-count formula -/

/-- If the σ-fixed induced subgraph is a star, the involution edge-count formula
takes the explicit form `a₁ = 3248 - 56·a₀`. -/
theorem aut_involution_starEdgeCountFormula
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ)
    {c : fixedVertexSet σ}
    (hstar : IsStarWithCenter (autFixedInducedGraph Γ σ) c) :
    (adjacentMovedCount Γ σ : ℤ) =
      3250 - 58 * (fixedVertexCount σ : ℤ) +
        2 * ((fixedVertexCount σ : ℤ) - 1) := by
  classical
  have hedge :
      (adjacentMovedCount Γ σ : ℤ) =
        3250 - 58 * (fixedVertexCount σ : ℤ) +
          2 * (((Γ.induce (fixedVertexSet σ)).edgeFinset.card : ℤ)) :=
    adjacentMovedCount_eq_involution_fixed_edge_formula hΓ hinv haut
  have hpos : 0 < fixedVertexCount σ := by
    rw [fixedVertexCount_eq_card_fixedVertexSet]
    exact Fintype.card_pos_iff.mpr ⟨c⟩
  have hstar_edges :
      (autFixedInducedGraph Γ σ).edgeFinset.card =
        Fintype.card (fixedVertexSet σ) - 1 :=
    IsStarWithCenter.card_edgeFinset_eq_card_sub_one
      (G := autFixedInducedGraph Γ σ) (c := c) hstar
  have hstar_edges_count :
      (autFixedInducedGraph Γ σ).edgeFinset.card = fixedVertexCount σ - 1 := by
    rw [hstar_edges, fixedVertexCount_eq_card_fixedVertexSet]
  have hstar_edges_int :
      ((autFixedInducedGraph Γ σ).edgeFinset.card : ℤ) =
        (fixedVertexCount σ : ℤ) - 1 := by
    have hnat : (autFixedInducedGraph Γ σ).edgeFinset.card = fixedVertexCount σ - 1 :=
      hstar_edges_count
    calc
      ((autFixedInducedGraph Γ σ).edgeFinset.card : ℤ)
          = ((fixedVertexCount σ - 1 : ℕ) : ℤ) := by exact_mod_cast hnat
      _ = (fixedVertexCount σ : ℤ) - 1 := by
            rw [Nat.cast_sub (Nat.succ_le_of_lt hpos)]
            norm_num
  rw [hedge, hstar_edges_int]

/-! ### Star candidate list -/

/-- For an involutive automorphism `σ` whose σ-fixed induced subgraph is a
star, the fixed count lies in `{6, 16, 26, 36, 46, 56}`. -/
theorem aut_involution_fixedVertexCount_star_candidates
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ)
    {c : fixedVertexSet σ}
    (hstar : IsStarWithCenter (autFixedInducedGraph Γ σ) c) :
    fixedVertexCount σ = 6 ∨
    fixedVertexCount σ = 16 ∨
    fixedVertexCount σ = 26 ∨
    fixedVertexCount σ = 36 ∨
    fixedVertexCount σ = 46 ∨
    fixedVertexCount σ = 56 := by
  classical
  have hpos : 0 < fixedVertexCount σ := by
    rw [fixedVertexCount_eq_card_fixedVertexSet]
    exact Fintype.card_pos_iff.mpr ⟨c⟩
  have hle := aut_fixedVertexCount_le_fiftyEight_of_star hΓ σ hstar
  have heven : 2 ∣ fixedVertexCount σ := by
    have hcard : Fintype.card V = 3250 := hΓ.card
    have hsupport_even : 2 ∣ Fintype.card V - fixedVertexCount σ :=
      two_dvd_card_sub_fixedVertexCount_of_involutive σ hinv
    obtain ⟨q, hq⟩ := hsupport_even
    refine ⟨1625 - q, ?_⟩
    rw [hcard] at hq
    omega
  have hformula : (adjacentMovedCount Γ σ : ℤ) =
      3250 - 58 * (fixedVertexCount σ : ℤ) +
        2 * ((fixedVertexCount σ : ℤ) - 1) :=
    aut_involution_starEdgeCountFormula hΓ σ haut hinv hstar
  obtain ⟨z, htrace⟩ := aut_involution_E7_trace_int hΓ σ haut hinv
  have hmod : (fixedVertexCount σ : ℤ) ≡ 1 [ZMOD 5] :=
    hΓ.starEdgeCountFormula_fixedVertexCount_intModEq_five σ htrace hformula
  exact fixed_count_candidates_of_pos_le_even_intModEq_five
    (fixedVertexCount σ) hpos hle heven hmod

/-! ### Regular case arithmetic -/

/-- For an involutive automorphism `σ` whose σ-fixed induced subgraph is
regular of degree `k`, the fixed count is `k² + 1` (when positive). -/
theorem aut_involution_fixedVertexCount_regular_eq_sq_add_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k)
    (hpos : 0 < fixedVertexCount σ) :
    fixedVertexCount σ = k * k + 1 := by
  have hsrg :
      (autFixedInducedGraph Γ σ).IsSRGWith (fixedVertexCount σ) k 0 1 :=
    autFixedInducedGraph_isSRGWith_of_regular hΓ σ haut k hreg
  have hparam :=
    SimpleGraph.IsSRGWith.param_eq (autFixedInducedGraph Γ σ) hsrg hpos
  -- hparam : k * (k - 0 - 1) = (fixedVertexCount σ - k - 1) * 1
  simp only [Nat.sub_zero, mul_one] at hparam
  -- hparam : k * (k - 1) = fixedVertexCount σ - k - 1
  -- A regular graph of positive size of degree k has at least k+1 vertices.
  have hge : k + 1 ≤ fixedVertexCount σ := by
    classical
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
      have : (autFixedInducedGraph Γ σ).Adj v v :=
        (SimpleGraph.mem_neighborFinset _ _ _).mp hmem
      exact (autFixedInducedGraph Γ σ).irrefl this
    have hcard_ins :
        (insert v ((autFixedInducedGraph Γ σ).neighborFinset v)).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hv_not, hneighbors_card]
    have hge_card :
        k + 1 ≤ (Finset.univ : Finset (fixedVertexSet σ)).card := by
      rw [← hcard_ins]
      exact Finset.card_le_card (Finset.subset_univ _)
    rwa [fixedVertexCount_eq_card_fixedVertexSet, ← Finset.card_univ]
  -- Cast everything to ℤ so we can use ring/linear arithmetic.
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · subst hk0
    simp only [Nat.zero_sub, Nat.mul_zero, Nat.zero_mul, Nat.zero_add] at hparam
    omega
  have h_k_sub_pos : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  have hparam_int :
      (k : ℤ) * ((k : ℤ) - 1) = (fixedVertexCount σ : ℤ) - (k : ℤ) - 1 := by
    have h1 : ((k * (k - 1) : ℕ) : ℤ) = (k : ℤ) * ((k : ℤ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hk_pos]
      push_cast
      ring
    have h2 : ((fixedVertexCount σ - k - 1 : ℕ) : ℤ) =
        (fixedVertexCount σ : ℤ) - (k : ℤ) - 1 := by
      have hge2 : 1 ≤ fixedVertexCount σ - k := by omega
      rw [Nat.cast_sub (by omega : 1 ≤ fixedVertexCount σ - k),
          Nat.cast_sub (by omega : k ≤ fixedVertexCount σ)]
      push_cast
      ring
    have : ((k * (k - 1) : ℕ) : ℤ) = ((fixedVertexCount σ - k - 1 : ℕ) : ℤ) := by
      exact_mod_cast hparam
    rw [h1, h2] at this
    exact this
  have hgoal_int : (fixedVertexCount σ : ℤ) = (k : ℤ) * (k : ℤ) + 1 := by
    linarith
  have : fixedVertexCount σ = k * k + 1 := by
    have : ((fixedVertexCount σ : ℤ)) = ((k * k + 1 : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  exact this

/-- For an involutive automorphism `σ` whose σ-fixed induced subgraph is
regular of degree `k`, the involution edge-count formula reads
`a₁ = 3250 + (k² + 1)(k − 58)`. -/
theorem aut_involution_a1_regular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ)
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k)
    (hpos : 0 < fixedVertexCount σ) :
    (adjacentMovedCount Γ σ : ℤ) =
      3250 + ((k : ℤ) * (k : ℤ) + 1) * ((k : ℤ) - 58) := by
  have hcard : fixedVertexCount σ = k * k + 1 :=
    aut_involution_fixedVertexCount_regular_eq_sq_add_one hΓ σ haut k hreg hpos
  have hedge :
      (adjacentMovedCount Γ σ : ℤ) =
        3250 - 58 * (fixedVertexCount σ : ℤ) +
          2 * (((Γ.induce (fixedVertexSet σ)).edgeFinset.card : ℤ)) :=
    adjacentMovedCount_eq_involution_fixed_edge_formula hΓ hinv haut
  have hreg_edges :
      2 * (autFixedInducedGraph Γ σ).edgeFinset.card =
        Fintype.card (fixedVertexSet σ) * k := by
    classical
    have hsum := (autFixedInducedGraph Γ σ).sum_degrees_eq_twice_card_edges
    have hsum_eq :
        (∑ v : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree v) =
          Fintype.card (fixedVertexSet σ) * k := by
      calc
        (∑ v : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree v)
            = ∑ _v : fixedVertexSet σ, k :=
              Finset.sum_congr rfl (fun v _ => hreg v)
        _ = Fintype.card (fixedVertexSet σ) * k := by
              simp [Finset.sum_const, Finset.card_univ, mul_comm]
    omega
  have hreg_edges_int :
      2 * (((Γ.induce (fixedVertexSet σ)).edgeFinset.card : ℤ)) =
        (fixedVertexCount σ : ℤ) * (k : ℤ) := by
    have : ((2 * (autFixedInducedGraph Γ σ).edgeFinset.card : ℕ) : ℤ) =
        ((Fintype.card (fixedVertexSet σ) * k : ℕ) : ℤ) := by
      exact_mod_cast hreg_edges
    have := this
    push_cast at this
    rw [fixedVertexCount_eq_card_fixedVertexSet]
    linarith
  rw [hedge, hreg_edges_int, hcard]
  push_cast
  ring

/-! ### Main candidate-list theorem -/

/-- For an involutive automorphism `σ` of a Moore57 graph with `σ ≠ 1`, the
fixed-vertex count lies in `{0, 2, 6, 10, 16, 26, 36, 46, 50, 56}`. -/
theorem aut_involution_fixedVertexCount_candidates
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ)
    (hne : σ ≠ 1) :
    fixedVertexCount σ = 0 ∨
    fixedVertexCount σ = 2 ∨
    fixedVertexCount σ = 6 ∨
    fixedVertexCount σ = 10 ∨
    fixedVertexCount σ = 16 ∨
    fixedVertexCount σ = 26 ∨
    fixedVertexCount σ = 36 ∨
    fixedVertexCount σ = 46 ∨
    fixedVertexCount σ = 50 ∨
    fixedVertexCount σ = 56 := by
  classical
  by_cases ha0_zero : fixedVertexCount σ = 0
  · left; exact ha0_zero
  have hpos : 0 < fixedVertexCount σ := Nat.pos_of_ne_zero ha0_zero
  have hstrong : IsStrongZeroOne (autFixedInducedGraph Γ σ) :=
    autFixedInducedGraph_isStrongZeroOne hΓ σ haut
  by_cases hregular :
      ∃ k : ℕ, ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k
  · -- Regular branch
    obtain ⟨k, hreg⟩ := hregular
    have hcard : fixedVertexCount σ = k * k + 1 :=
      aut_involution_fixedVertexCount_regular_eq_sq_add_one hΓ σ haut k hreg hpos
    have hVle : fixedVertexCount σ ≤ Fintype.card V := by
      simp [fixedVertexCount]
      exact Finset.card_filter_le _ _
    have heven : 2 ∣ fixedVertexCount σ := by
      have hVcard : Fintype.card V = 3250 := hΓ.card
      have hVle' : fixedVertexCount σ ≤ 3250 := hVcard ▸ hVle
      have hsupport_even : 2 ∣ Fintype.card V - fixedVertexCount σ :=
        two_dvd_card_sub_fixedVertexCount_of_involutive σ hinv
      obtain ⟨q, hq⟩ := hsupport_even
      refine ⟨1625 - q, ?_⟩
      rw [hVcard] at hq
      omega
    have hkodd : ¬ 2 ∣ k := by
      intro hk
      have h_kk_even : 2 ∣ k * k := hk.mul_right k
      have h_kkp1_even : 2 ∣ k * k + 1 := hcard ▸ heven
      omega
    have ha1 : (adjacentMovedCount Γ σ : ℤ) =
        3250 + ((k : ℤ) * (k : ℤ) + 1) * ((k : ℤ) - 58) :=
      aut_involution_a1_regular hΓ σ haut hinv k hreg hpos
    have ha1_nonneg : 0 ≤ (adjacentMovedCount Γ σ : ℤ) := by
      exact_mod_cast Nat.zero_le _
    rw [ha1] at ha1_nonneg
    have ha0_lt : fixedVertexCount σ < 3250 := by
      rw [← hΓ.card]; exact aut_fixedVertexCount_lt_card σ hne
    rw [hcard] at ha0_lt
    have hk_le_56 : k ≤ 56 := by nlinarith
    -- Enumerate k ∈ [0, 56]: even ones contradict hkodd; odd k ≥ 9 contradict ha1_nonneg.
    -- The remaining odd k ∈ {1, 3, 5, 7} give a_0 ∈ {2, 10, 26, 50}, matching the
    -- disjunction.
    interval_cases k
    all_goals first
      | (exact absurd (by decide) hkodd)
      | (norm_num at hcard; omega)
      | (exfalso; norm_num at ha1_nonneg)
  · -- Star branch
    rcases hstrong.exists_isStarWithCenter_of_not_regular hregular with ⟨c, hstar⟩
    rcases aut_involution_fixedVertexCount_star_candidates hΓ σ haut hinv hstar with
      h6 | h16 | h26 | h36 | h46 | h56
    · right; right; left; exact h6
    · right; right; right; right; left; exact h16
    · right; right; right; right; right; left; exact h26
    · right; right; right; right; right; right; left; exact h36
    · right; right; right; right; right; right; right; left; exact h46
    · right; right; right; right; right; right; right; right; right; exact h56

/-- For an involutive automorphism `σ` of a Moore57 graph with `σ ≠ 1`, the
fixed-vertex count is never congruent to `1` mod `19`. This is the form used
by the `C₃₈` non-existence proof. -/
theorem aut_involution_fixedVertexCount_not_modEq_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ)
    (hne : σ ≠ 1) :
    ¬ (fixedVertexCount σ ≡ 1 [MOD 19]) := by
  intro hmod
  rcases aut_involution_fixedVertexCount_candidates hΓ σ haut hinv hne with
    h | h | h | h | h | h | h | h | h | h <;>
    · rw [h] at hmod
      simp [Nat.ModEq] at hmod

end Moore57
