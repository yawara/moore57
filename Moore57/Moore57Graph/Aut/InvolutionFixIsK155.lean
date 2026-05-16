import Moore57.Moore57Graph.Aut.InvolutionCandidates
import Moore57.Moore57Graph.Aut.InducedSubgraph
import Moore57.Moore57Graph.InvolutionEdgeCountFormula
import Moore57.Foundations.GraphTheory.StrongZeroOne
import Moore57.Moore57Graph.Aut.FixedSubgraphData

/-!
# Fix(σ) ≅ K_{1,55} for an involution σ of a Moore57 graph (Tier 2)

This file establishes Cameron's Theorem 3.13 (Higman's argument, see
`tmp/pdfs/cameron_ch3_coherent_configurations.txt` Steps 1-4 and
Makhnev-Paduchikh's Lemmas 1, 2, 4 in `tmp/pdfs/involution-fixed-star.txt`).
Inputs are minimal:

* `σ : Equiv.Perm V` with `Function.Involutive σ` (i.e. `σ^2 = 1`),
* `σ ≠ 1`,
* `σ` preserves adjacency in a Moore57 graph `Γ`.

The conclusion is that the σ-fixed induced subgraph is the star `K_{1,55}` —
a center adjacent to all 55 leaves, with no other edges.

## Outline (Cameron Steps 1-4)

* **Phase 1** (`aut_involution_exists_adjacent_moved`): Case B impossible.
  If `∀ v, ¬ Γ.Adj v (σ v)` (no adjacent moved pair), then the
  `adjacentMovedCount` equation forces `2 · #E(Fix) = 58 · |Fix| - 3250`.
  Combined with `#E ≥ 0`, this gives `|Fix| ≥ 57`, contradicting the
  candidates list (max 56). Hence some adjacent moved pair exists.

* **Phase 2** (Cameron Step 2 labeling): for `a`, `b = σ a` with `a ~ b`, the
  map `V \ ({a,b} ∪ N(a)\{b} ∪ N(b)\{a}) → A × B`, `v ↦ (φ_a v, φ_b v)`
  (common neighbors with `a`, `b`) is a bijection, and σ-fixed `v` correspond
  to pairs `(α, σ α)` with `α ∈ A`. Hence `|Fix(σ)| = 56`.

* **Phase 3**: `|Fix(σ)| = 56` rules out the regular branch
  (`k² = 55` has no integer solution), so the fixed induced graph is a star.

* **Phase 4**: Build `K155FixedData Γ σ` from the star + 56-vertex data.
-/

namespace Moore57

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Phase 1: Some adjacent moved pair exists -/

/-- If `σ` has no adjacent moved pair, then `adjacentMovedCount Γ σ = 0`. -/
private theorem adjacentMovedCount_eq_zero_of_no_adjacent_moved
    (σ : Equiv.Perm V)
    (hno : ∀ v : V, ¬ Γ.Adj v (σ v)) :
    adjacentMovedCount Γ σ = 0 := by
  classical
  unfold adjacentMovedCount
  rw [Finset.card_eq_zero]
  ext v
  simp [hno v]

/-- **Cameron Step 1 (refuted Case B)**: an involutive automorphism `σ ≠ 1` of
a Moore57 graph must interchange some adjacent pair. -/
theorem aut_involution_exists_adjacent_moved
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ)
    (hne : σ ≠ 1) :
    ∃ a : V, Γ.Adj a (σ a) := by
  classical
  by_contra hno_exists
  push_neg at hno_exists
  have ha1_zero : adjacentMovedCount Γ σ = 0 :=
    adjacentMovedCount_eq_zero_of_no_adjacent_moved σ hno_exists
  have hformula :
      (adjacentMovedCount Γ σ : ℤ) =
        3250 - 58 * (fixedVertexCount σ : ℤ) +
          2 * (((Γ.induce (fixedVertexSet σ)).edgeFinset.card : ℤ)) :=
    adjacentMovedCount_eq_involution_fixed_edge_formula hΓ hinv haut
  rw [ha1_zero] at hformula
  have hedges_nn :
      0 ≤ ((Γ.induce (fixedVertexSet σ)).edgeFinset.card : ℤ) := by
    exact_mod_cast Nat.zero_le _
  -- 0 = 3250 - 58 |Fix| + 2 #E, with #E ≥ 0, gives 58 |Fix| ≥ 3250, so |Fix| ≥ 57
  have hge_int : (57 : ℤ) ≤ (fixedVertexCount σ : ℤ) := by omega
  have hge : 57 ≤ fixedVertexCount σ := by exact_mod_cast hge_int
  rcases aut_involution_fixedVertexCount_candidates hΓ σ haut hinv hne with
    h | h | h | h | h | h | h | h | h | h <;> omega

/-! ### Phase 2: Cameron Step 2 labeling

Given `a ∈ V` with `Γ.Adj a (σ a)`, let `b := σ a`. The proof strategy is to
inject `Aset := (Γ.neighborFinset a).erase b` (= 56 elements) into
`fixedFinset σ`, by sending `v ∈ Aset` to the unique common neighbour of `v`
and `σ v`. That common neighbour is σ-fixed by
`aut_fixed_commonNeighbor_of_swap_not_adj`, and the assignment is injective
by a μ=1 argument. Combined with `|Fix(σ)| ≤ 56` from the candidates list,
this forces `|Fix(σ)| = 56`. -/

/-- The σ-fixed common neighbour of `v` and `σ v`, when `σ` is an involutive
graph automorphism, `v` and `σ v` are non-adjacent and distinct.

This is a constructive choice via `Classical.choose` on the μ=1 singleton. -/
private noncomputable def commonFixOfSwapPair
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {v : V} (hne : v ≠ σ v) (hnadj : ¬ Γ.Adj v (σ v)) : V := by
  classical
  have hcard : Fintype.card (Γ.commonNeighbors v (σ v)) = 1 :=
    hΓ.of_not_adj hne hnadj
  exact (Fintype.card_eq_one_iff.mp hcard).choose.val

private theorem commonFixOfSwapPair_spec
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ)
    {v : V} (hne : v ≠ σ v) (hnadj : ¬ Γ.Adj v (σ v)) :
    let z := commonFixOfSwapPair hΓ σ haut hne hnadj
    σ z = z ∧ Γ.Adj v z ∧ Γ.Adj (σ v) z := by
  classical
  have hcard : Fintype.card (Γ.commonNeighbors v (σ v)) = 1 :=
    hΓ.of_not_adj hne hnadj
  set hExists := Fintype.card_eq_one_iff.mp hcard
  set zRec := hExists.choose
  have hz_mem : (zRec.val : V) ∈ Γ.commonNeighbors v (σ v) := zRec.property
  rw [SimpleGraph.mem_commonNeighbors] at hz_mem
  have hσz : σ zRec.val = zRec.val := by
    refine aut_fixed_commonNeighbor_of_swap_not_adj hΓ σ haut ?_ ?_ hne hnadj ?_
    · rfl
    · exact hinv v
    · exact hz_mem
  exact ⟨hσz, hz_mem⟩

private theorem commonFixOfSwapPair_unique
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {v : V} (hne : v ≠ σ v) (hnadj : ¬ Γ.Adj v (σ v))
    {w : V} (hw : Γ.Adj v w ∧ Γ.Adj (σ v) w) :
    w = commonFixOfSwapPair hΓ σ haut hne hnadj := by
  classical
  have hcard : Fintype.card (Γ.commonNeighbors v (σ v)) = 1 :=
    hΓ.of_not_adj hne hnadj
  set hExists := Fintype.card_eq_one_iff.mp hcard
  have hw_mem : w ∈ Γ.commonNeighbors v (σ v) := by
    rw [SimpleGraph.mem_commonNeighbors]; exact hw
  have hzRec_unique : ∀ y, y = hExists.choose := hExists.choose_spec
  have h1 : (⟨w, hw_mem⟩ : Γ.commonNeighbors v (σ v)) = hExists.choose :=
    hzRec_unique _
  exact congrArg Subtype.val h1

/-- **Cameron's Theorem 3.13 Step 2** (labeling): for an involutive
automorphism `σ` with `σ ≠ 1` of a Moore57 graph, if `σ` swaps an adjacent
pair `a ~ σ a`, then `|Fix(σ)| = 56`. -/
theorem aut_involution_fixedVertexCount_eq_56_of_adjacent_moved
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ)
    (hne : σ ≠ 1)
    {a : V} (hAdj : Γ.Adj a (σ a)) :
    fixedVertexCount σ = 56 := by
  classical
  -- Setup: b := σ a, b ≠ a, σ b = a.
  set b : V := σ a with hb_def
  have hab : Γ.Adj a b := hAdj
  have hab_ne : a ≠ b := by
    intro h
    have hloop : ¬ Γ.Adj a a := Γ.loopless.1 a
    exact hloop (h ▸ hab)
  have hσb : σ b = a := hinv a
  -- Aset := (Γ.neighborFinset a).erase b — has cardinality 56.
  set Aset : Finset V := (Γ.neighborFinset a).erase b with hAset_def
  have mem_Aset : ∀ {v : V}, v ∈ Aset ↔ v ≠ b ∧ Γ.Adj a v := by
    intro v
    simp [Aset, SimpleGraph.mem_neighborFinset]
  have hb_mem_N : b ∈ Γ.neighborFinset a :=
    (SimpleGraph.mem_neighborFinset _ _ _).mpr hab
  have Aset_card : Aset.card = 56 := by
    rw [hAset_def, Finset.card_erase_of_mem hb_mem_N,
        SimpleGraph.card_neighborFinset_eq_degree, hΓ.regular.degree_eq]
  -- For each v ∈ Aset, σ v ≠ v and ¬ Γ.Adj v (σ v), so the common neighbour
  -- of v and σ v is well-defined and σ-fixed.
  have hSwapData : ∀ v ∈ Aset, v ≠ σ v ∧ ¬ Γ.Adj v (σ v) := by
    intro v hv
    rw [mem_Aset] at hv
    obtain ⟨hvb, hav⟩ := hv
    -- σ v ∈ N(b) since Γ.Adj a v ↔ Γ.Adj (σ a) (σ v) = Γ.Adj b (σ v).
    have hbσv : Γ.Adj b (σ v) := by
      have h := (haut a v).mp hav
      simpa [b] using h
    -- σ v ≠ a because σ v = a would give v = σ a = b, contradicting v ≠ b.
    have hσv_ne_a : σ v ≠ a := by
      intro heq
      have : v = b := by
        have := congrArg σ heq
        rwa [hinv v, ← hb_def] at this
      exact hvb this
    -- σ v ∈ N(b) and σ v ≠ a, so σ v ∈ Bset. Aset ∩ Bset = ∅ ⇒ σ v ∉ Aset.
    -- σ v ≠ v: if σ v = v, then v ∈ Aset ∩ Bset = ∅. But concretely we need
    -- to show v ≠ σ v. Suppose v = σ v: then Γ.Adj b v (= Γ.Adj b (σ v)). So
    -- v ∈ N(a) ∩ N(b). But a~b and λ=0 implies N(a) ∩ N(b) = ∅.
    have hne : v ≠ σ v := by
      intro heq
      have hbv : Γ.Adj b v := heq ▸ hbσv
      exact hΓ.no_triangle hab hbv hav.symm
    refine ⟨hne, ?_⟩
    -- ¬ Γ.Adj v (σ v): a 4-cycle a-v-σv-b would contradict no_four_cycle.
    intro hvσv
    -- 4-cycle a, v, σ v, b: a ~ v, v ~ σ v, σ v ~ b, b ~ a.
    have h_a_neq_σv : a ≠ σ v := fun h => hσv_ne_a h.symm
    have h_v_neq_b : v ≠ b := hvb
    have h_a_neq_v : a ≠ v := hav.ne
    have h_v_neq_σv : v ≠ σ v := hne
    have h_σv_neq_b : σ v ≠ b := by
      intro heq
      have hvσa : v = σ b := by
        have := congrArg σ heq
        rw [hinv v] at this
        exact this
      rw [hσb] at hvσa
      exact h_a_neq_v hvσa.symm
    -- Apply no_four_cycle: vertices a, v, σ v, b in order.
    exact hΓ.no_four_cycle h_a_neq_v h_a_neq_σv hab_ne h_v_neq_σv h_v_neq_b
      h_σv_neq_b hav hvσv hbσv.symm hab.symm
  -- Define the injection as a subtype-to-subtype function.
  let f : {v // v ∈ Aset} → {v // v ∈ fixedFinset σ} := fun ⟨v, hv⟩ =>
    ⟨commonFixOfSwapPair hΓ σ haut (hSwapData v hv).1 (hSwapData v hv).2, by
      rw [mem_fixedFinset]
      exact (commonFixOfSwapPair_spec hΓ σ haut hinv (hSwapData v hv).1
              (hSwapData v hv).2).1⟩
  -- Injectivity of f.
  have hf_inj : Function.Injective f := by
    rintro ⟨v₁, h₁⟩ ⟨v₂, h₂⟩ heq
    apply Subtype.ext
    -- f ⟨v₁, h₁⟩.val = f ⟨v₂, h₂⟩.val
    have hval_eq :
        commonFixOfSwapPair hΓ σ haut (hSwapData v₁ h₁).1 (hSwapData v₁ h₁).2 =
        commonFixOfSwapPair hΓ σ haut (hSwapData v₂ h₂).1 (hSwapData v₂ h₂).2 :=
      congrArg Subtype.val heq
    by_contra hne'
    -- Both v₁, v₂ ∈ N(a). If v₁ ~ v₂, triangle a-v₁-v₂ — but λ=0. So v₁ ≁ v₂.
    have hv₁a : Γ.Adj a v₁ := (mem_Aset.mp h₁).2
    have hv₂a : Γ.Adj a v₂ := (mem_Aset.mp h₂).2
    have h_v₁v₂_not_adj : ¬ Γ.Adj v₁ v₂ := fun hv₁v₂ =>
      hΓ.no_triangle hv₁a hv₁v₂ hv₂a.symm
    -- μ=1: unique common neighbor of v₁ and v₂. We have a, and we have f.val.
    have hcard : Fintype.card (Γ.commonNeighbors v₁ v₂) = 1 :=
      hΓ.of_not_adj hne' h_v₁v₂_not_adj
    rcases Fintype.card_eq_one_iff.mp hcard with ⟨u, hu_unique⟩
    have ha_mem : a ∈ Γ.commonNeighbors v₁ v₂ := by
      rw [SimpleGraph.mem_commonNeighbors]; exact ⟨hv₁a.symm, hv₂a.symm⟩
    set fval := commonFixOfSwapPair hΓ σ haut (hSwapData v₁ h₁).1 (hSwapData v₁ h₁).2
    have hfval_adj_v₁ : Γ.Adj v₁ fval :=
      (commonFixOfSwapPair_spec hΓ σ haut hinv (hSwapData v₁ h₁).1
        (hSwapData v₁ h₁).2).2.1
    have hfval_adj_v₂ : Γ.Adj v₂ fval := by
      have hf₂ := (commonFixOfSwapPair_spec hΓ σ haut hinv (hSwapData v₂ h₂).1
        (hSwapData v₂ h₂).2).2.1
      have : fval = commonFixOfSwapPair hΓ σ haut (hSwapData v₂ h₂).1
          (hSwapData v₂ h₂).2 := hval_eq
      rw [this]; exact hf₂
    have hfval_mem : fval ∈ Γ.commonNeighbors v₁ v₂ := by
      rw [SimpleGraph.mem_commonNeighbors]; exact ⟨hfval_adj_v₁, hfval_adj_v₂⟩
    have h_a_eq_u : (⟨a, ha_mem⟩ : Γ.commonNeighbors v₁ v₂) = u := hu_unique _
    have h_fv_eq_u : (⟨fval, hfval_mem⟩ : Γ.commonNeighbors v₁ v₂) = u := hu_unique _
    have h_a_eq_fv : a = fval :=
      congrArg Subtype.val (h_a_eq_u.trans h_fv_eq_u.symm)
    -- But a is not σ-fixed while fval is.
    have hf_fixed' : σ fval = fval :=
      (commonFixOfSwapPair_spec hΓ σ haut hinv (hSwapData v₁ h₁).1
        (hSwapData v₁ h₁).2).1
    have ha_fixed : σ a = a := h_a_eq_fv ▸ hf_fixed'
    exact hab_ne (ha_fixed.symm.trans hb_def)
  -- |Aset| ≤ |fixedFinset σ| from the injection f.
  have hcard_le_subtype :
      Fintype.card {v // v ∈ Aset} ≤ Fintype.card {v // v ∈ fixedFinset σ} :=
    Fintype.card_le_of_injective f hf_inj
  have hAset_card_eq : Fintype.card {v // v ∈ Aset} = Aset.card :=
    Fintype.card_coe Aset
  have hFix_card_eq : Fintype.card {v // v ∈ fixedFinset σ} = (fixedFinset σ).card :=
    Fintype.card_coe _
  have h56_le : 56 ≤ fixedVertexCount σ := by
    have := hcard_le_subtype
    rw [hAset_card_eq, hFix_card_eq, Aset_card, fixedFinset_card] at this
    exact this
  -- Combine with candidates list (max 56).
  rcases aut_involution_fixedVertexCount_candidates hΓ σ haut hinv hne with
    h | h | h | h | h | h | h | h | h | h <;> omega

/-! ### Phase 1+2 combined: unconditional `|Fix(σ)| = 56` -/

/-- **Cameron Theorem 3.13** (Higman): an involutive automorphism `σ ≠ 1` of a
Moore57 graph fixes exactly 56 vertices. Combines Phase 1 (`∃ a, Γ.Adj a (σ a)`)
with Phase 2 (the labeling argument). -/
theorem aut_involution_fixedVertexCount_eq_56
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ)
    (hne : σ ≠ 1) :
    fixedVertexCount σ = 56 := by
  obtain ⟨a, hAdj⟩ := aut_involution_exists_adjacent_moved hΓ σ haut hinv hne
  exact aut_involution_fixedVertexCount_eq_56_of_adjacent_moved
    hΓ σ haut hinv hne hAdj

/-! ### Phase 3: Fix(σ) is a star

With `|Fix(σ)| = 56` and the strong-`(0,1)` structure inherited from Moore57,
the σ-fixed induced graph is non-regular (the regular case would force
`|Fix| = k² + 1`, but `55` is not a perfect square) and hence a star with
some center `c`. -/

/-- For an involutive automorphism `σ ≠ 1` of a Moore57 graph, the σ-fixed
induced subgraph is a star, i.e., has a center vertex adjacent to all 55
other fixed vertices, with no other edges. -/
theorem aut_involution_fixedInducedGraph_isStarWithCenter
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ)
    (hne : σ ≠ 1) :
    ∃ c : fixedVertexSet σ, IsStarWithCenter (autFixedInducedGraph Γ σ) c := by
  classical
  have hcard : fixedVertexCount σ = 56 :=
    aut_involution_fixedVertexCount_eq_56 hΓ σ haut hinv hne
  have hstrong : IsStrongZeroOne (autFixedInducedGraph Γ σ) :=
    autFixedInducedGraph_isStrongZeroOne hΓ σ haut
  -- Regular case is impossible: 56 = k² + 1 has no integer solution.
  have hnot_regular :
      ¬ ∃ k : ℕ, ∀ x : fixedVertexSet σ,
        (autFixedInducedGraph Γ σ).degree x = k := by
    rintro ⟨k, hreg⟩
    have hpos : 0 < fixedVertexCount σ := by rw [hcard]; norm_num
    have hkk : fixedVertexCount σ = k * k + 1 :=
      aut_involution_fixedVertexCount_regular_eq_sq_add_one hΓ σ haut k hreg hpos
    rw [hcard] at hkk
    -- 56 = k * k + 1, so k * k = 55. But 7² = 49, 8² = 64, no integer k works.
    have h55 : k * k = 55 := by omega
    have hk_lt : k < 8 := by nlinarith
    have hk_gt : 7 < k := by nlinarith
    omega
  exact hstrong.exists_isStarWithCenter_of_not_regular hnot_regular

/-! ### Phase 4: Assembled `K155FixedData` -/

/-- **Main theorem**: For an involutive automorphism `σ ≠ 1` of a Moore57
graph, the σ-fixed subgraph is the star `K_{1,55}` — a center adjacent to
55 leaves, with no other edges.

This packages the data as a `K155FixedData Γ σ` with an explicit `Fin 55`
enumeration of the leaves. -/
theorem aut_involution_nonempty_K155FixedData
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ)
    (hne : σ ≠ 1) :
    Nonempty (K155FixedData Γ σ) := by
  classical
  -- Get star center c and fix(σ) cardinality.
  obtain ⟨c, hstar⟩ :=
    aut_involution_fixedInducedGraph_isStarWithCenter hΓ σ haut hinv hne
  have hcard : fixedVertexCount σ = 56 :=
    aut_involution_fixedVertexCount_eq_56 hΓ σ haut hinv hne
  -- Set up the 55-vertex leaf Finset and its Fin 55 enumeration.
  set Lfin : Finset V := (fixedFinset σ).erase c.val with hLfin_def
  have hc_mem_fix : c.val ∈ fixedFinset σ := by
    rw [mem_fixedFinset]; exact c.property
  have hLcard : Lfin.card = 55 := by
    rw [hLfin_def, Finset.card_erase_of_mem hc_mem_fix, fixedFinset_card, hcard]
  have hcardL : Fintype.card {x // x ∈ Lfin} = 55 := by
    rw [Fintype.card_coe]; exact hLcard
  let leafEnum : Fin 55 ≃ {x // x ∈ Lfin} :=
    (Fintype.equivFinOfCardEq hcardL).symm
  let leafFn : Fin 55 → V := fun i => (leafEnum i).val
  -- Membership characterization of leafFn.
  have hleafFn_mem : ∀ i : Fin 55, leafFn i ∈ Lfin := fun i => (leafEnum i).property
  have hleaf_in_fix : ∀ i : Fin 55, σ (leafFn i) = leafFn i := by
    intro i
    have := hleafFn_mem i
    rw [hLfin_def, Finset.mem_erase, mem_fixedFinset] at this
    exact this.2
  have hleaf_ne_center : ∀ i : Fin 55, leafFn i ≠ c.val := by
    intro i
    have := hleafFn_mem i
    rw [hLfin_def, Finset.mem_erase] at this
    exact this.1
  -- Build the K155FixedData.
  refine ⟨{
    center := c.val
    leaf := leafFn
    center_ne_leaf := ?_
    leaf_injective := ?_
    center_fixed := c.property
    leaf_fixed := hleaf_in_fix
    span := ?_
    adj_center := ?_
    no_leaf_leaf := ?_
  }⟩
  · -- center_ne_leaf
    intro i hi
    exact hleaf_ne_center i hi.symm
  · -- leaf_injective
    intro i j hij
    have h1 : leafEnum i = leafEnum j := Subtype.ext hij
    exact leafEnum.injective h1
  · -- span
    intro x hx
    by_cases hxc : x = c.val
    · left; exact hxc
    · right
      have hx_mem : x ∈ Lfin := by
        rw [hLfin_def, Finset.mem_erase, mem_fixedFinset]
        exact ⟨hxc, hx⟩
      refine ⟨leafEnum.symm ⟨x, hx_mem⟩, ?_⟩
      show x = (leafEnum (leafEnum.symm ⟨x, hx_mem⟩)).val
      rw [Equiv.apply_symm_apply]
  · -- adj_center
    intro i
    have hi_subtype : leafFn i ∈ fixedVertexSet σ := hleaf_in_fix i
    have hstar_iff := hstar c ⟨leafFn i, hi_subtype⟩
    have hAdj_sub : (autFixedInducedGraph Γ σ).Adj c ⟨leafFn i, hi_subtype⟩ := by
      apply hstar_iff.mpr
      left
      refine ⟨rfl, ?_⟩
      intro hcontra
      exact hleaf_ne_center i (congrArg Subtype.val hcontra)
    exact hAdj_sub
  · -- no_leaf_leaf
    intro i j hadj
    have hi_subtype : leafFn i ∈ fixedVertexSet σ := hleaf_in_fix i
    have hj_subtype : leafFn j ∈ fixedVertexSet σ := hleaf_in_fix j
    have hadj_sub : (autFixedInducedGraph Γ σ).Adj
        ⟨leafFn i, hi_subtype⟩ ⟨leafFn j, hj_subtype⟩ := hadj
    rcases (hstar ⟨leafFn i, hi_subtype⟩ ⟨leafFn j, hj_subtype⟩).mp hadj_sub with
      ⟨hi_c, _⟩ | ⟨hj_c, _⟩
    · exact hleaf_ne_center i (congrArg Subtype.val hi_c)
    · exact hleaf_ne_center j (congrArg Subtype.val hj_c)

end Moore57
