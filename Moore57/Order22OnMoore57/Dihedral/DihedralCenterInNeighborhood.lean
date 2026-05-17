import Moore57.Order22OnMoore57.Dihedral.DihedralC5Reflection

/-!
# Steps 2-4 (Dihedral): K_{1,55} center は B_0 内

dihedral case で:
* (Step 2) `K_{1,55}` の center は u_τ ではなく leaf である.
  `x_0 := τ_fix.center` と置くと `x_0 ≠ u_τ` かつ `x_0 ∈ N(u_τ)`.
* (Step 3) `x_0 ∉ Fix(σ)` (∵ Fix(σ) ∩ Fix(τ) = {u_τ}).
  したがって x_0 は length-11 σ-orbit (= B_0) に属する.
* (Step 4) N(u_τ) は σ-stable, B_0 ⊂ N(u_τ).

* bτ, cτ も `x_0` と非隣接 (Step 7 用).
-/

namespace Moore57

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable (h : Order22ActsOnMoore57 V Γ)

/-! ## Step 4 (前置き): σ-stability of N(u_τ) -/

theorem dihedral_σ_mem_neighborFinset_uτ_iff
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) (x : V) :
    h.σ x ∈ Γ.neighborFinset (h.dihedral_uτ hdihe) ↔
      x ∈ Γ.neighborFinset (h.dihedral_uτ hdihe) := by
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
  conv_lhs => rw [show h.dihedral_uτ hdihe = h.σ (h.dihedral_uτ hdihe)
    from (h.dihedral_σ_uτ hdihe).symm]
  exact (h.σ_aut (h.dihedral_uτ hdihe) x).symm

/-! ## 補助: σ²·x = x ⟹ σ x = x (∵ |σ| = 11 prime) -/

private theorem dihedral_σ_pow_two_implies_σ_fixed
    {y : V} (h : Order22ActsOnMoore57 V Γ)
    (hy : h.σ (h.σ y) = y) :
    h.σ y = y := by
  have h_σ10 : (h.σ^10) y = y := by
    show h.σ (h.σ (h.σ (h.σ (h.σ (h.σ (h.σ (h.σ (h.σ (h.σ y))))))))) = y
    rw [hy, hy, hy, hy, hy]
  have h_σ11 : (h.σ^11) y = y := by
    rw [h.σ_pow_eleven]; rfl
  have : h.σ ((h.σ^10) y) = y := by
    show (h.σ^11) y = y
    exact h_σ11
  rw [h_σ10] at this
  exact this

/-- Leaf y のもとで σ y ∈ Fix(τ) ⟹ y = uτ. -/
private theorem dihedral_σ_leaf_in_τFix_implies_leaf_eq_uτ
    (h : Order22ActsOnMoore57 V Γ)
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) (y : V)
    (hy_τfix : h.τ y = y)
    (hσy_τfix : h.τ (h.σ y) = h.σ y) :
    y = h.dihedral_uτ hdihe := by
  have h_τσ : h.τ (h.σ y) = h.σ⁻¹ y := by
    rw [h.dihedral_τσ_eq_σinv_τ_apply hdihe]
    rw [hy_τfix]
  rw [h_τσ] at hσy_τfix
  have h_σ2 : h.σ (h.σ y) = y := by
    have hcong := congr_arg h.σ hσy_τfix
    have h_cancel : h.σ (h.σ⁻¹ y) = y := by
      show (h.σ * h.σ⁻¹) y = y
      rw [mul_inv_cancel]; rfl
    rw [h_cancel] at hcong
    exact hcong.symm
  have h_σy : h.σ y = y := dihedral_σ_pow_two_implies_σ_fixed h h_σ2
  exact h.dihedral_σFix_τFix_eq_uτ hdihe y h_σy hy_τfix

/-! ## Step 2: center は u_τ ではない (leaf) -/

theorem dihedral_center_ne_uτ
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ_fix.center ≠ h.dihedral_uτ hdihe := by
  intro huτ_eq_center
  -- uτ = center を仮定. 55 leaves ⊂ N(uτ).
  -- 各 leaf y で σ y ∈ N(uτ) ∖ Fix(τ) (= 2 element set when uτ = center).
  -- σ-injectivity ⟹ 55 distinct images in 2-element set: 矛盾.
  have h_σ_mem_N : ∀ x ∈ Γ.neighborFinset (h.dihedral_uτ hdihe),
      h.σ x ∈ Γ.neighborFinset (h.dihedral_uτ hdihe) := fun x hx =>
    (h.dihedral_σ_mem_neighborFinset_uτ_iff hdihe x).mpr hx
  -- 各 leaf i は N(uτ) = N(center) の元.
  have h_leaf_mem_N : ∀ i : Fin 55,
      h.τ_fix.leaf i ∈ Γ.neighborFinset (h.dihedral_uτ hdihe) := by
    intro i
    rw [SimpleGraph.mem_neighborFinset]
    rw [← huτ_eq_center]
    exact h.τ_fix.adj_center i
  -- τ (σ (leaf i)) ≠ σ (leaf i): もし fixed なら σ (leaf i) ∈ Fix(τ) で
  -- leaf i = uτ = center, leaf i = center で center_ne_leaf 矛盾.
  have h_σ_leaf_not_τ_fix : ∀ i : Fin 55,
      h.τ (h.σ (h.τ_fix.leaf i)) ≠ h.σ (h.τ_fix.leaf i) := by
    intro i hcontra
    have h_eq : h.τ_fix.leaf i = h.dihedral_uτ hdihe :=
      dihedral_σ_leaf_in_τFix_implies_leaf_eq_uτ h hdihe (h.τ_fix.leaf i)
        (h.τ_fix.leaf_fixed i) hcontra
    rw [← huτ_eq_center] at h_eq
    exact h.τ_fix.center_ne_leaf i h_eq.symm
  -- σ (leaf i) ∉ Fix(τ): K155.span から center または leaf, どちらも τ-fixed なので除外.
  have h_σ_leaf_not_center : ∀ i : Fin 55, h.σ (h.τ_fix.leaf i) ≠ h.τ_fix.center := by
    intro i heq
    have h_τfix : h.τ (h.σ (h.τ_fix.leaf i)) = h.σ (h.τ_fix.leaf i) := by
      rw [heq]; exact h.τ_fix.center_fixed
    exact h_σ_leaf_not_τ_fix i h_τfix
  have h_σ_leaf_not_leaf : ∀ i j : Fin 55,
      h.σ (h.τ_fix.leaf i) ≠ h.τ_fix.leaf j := by
    intro i j heq
    have h_τfix : h.τ (h.σ (h.τ_fix.leaf i)) = h.σ (h.τ_fix.leaf i) := by
      rw [heq]; exact h.τ_fix.leaf_fixed j
    exact h_σ_leaf_not_τ_fix i h_τfix
  -- σ(leaves) ⊂ N(uτ) ∖ leaves. |σ(leaves)| = 55, |N(uτ) ∖ leaves| = 2. 矛盾.
  set L : Finset V := Finset.univ.image h.τ_fix.leaf with hL_def
  have h_L_card : L.card = 55 := by
    rw [hL_def, Finset.card_image_of_injective _ h.τ_fix.leaf_injective]
    exact Finset.card_univ
  set σL : Finset V := L.image h.σ with hσL_def
  have h_σL_card : σL.card = 55 := by
    rw [hσL_def, Finset.card_image_of_injective _ h.σ.injective]
    exact h_L_card
  -- L ⊂ N(uτ)
  have hL_sub : L ⊆ Γ.neighborFinset (h.dihedral_uτ hdihe) := by
    intro y hy
    rw [hL_def, Finset.mem_image] at hy
    obtain ⟨i, _, hi⟩ := hy
    rw [← hi]
    exact h_leaf_mem_N i
  -- |N(uτ)| = 57
  have h_N_card : (Γ.neighborFinset (h.dihedral_uτ hdihe)).card = 57 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, h.isMoore.regular.degree_eq]
  -- |N(uτ) ∖ L| = 2
  have h_N_minus_L_card :
      (Γ.neighborFinset (h.dihedral_uτ hdihe) \ L).card = 2 := by
    rw [Finset.card_sdiff_of_subset hL_sub, h_N_card, h_L_card]
  -- σL ⊂ N(uτ) ∖ L
  have h_σL_sub : σL ⊆ Γ.neighborFinset (h.dihedral_uτ hdihe) \ L := by
    intro w hw
    rw [hσL_def, Finset.mem_image] at hw
    obtain ⟨z, hz, hzw⟩ := hw
    rw [hL_def, Finset.mem_image] at hz
    obtain ⟨i, _, hi⟩ := hz
    rw [← hi] at hzw
    rw [← hzw, Finset.mem_sdiff]
    refine ⟨h_σ_mem_N _ (h_leaf_mem_N i), ?_⟩
    rw [hL_def, Finset.mem_image]
    rintro ⟨j, _, hj⟩
    exact h_σ_leaf_not_leaf i j hj.symm
  -- 55 ≤ 2 contradiction
  have h_le : 55 ≤ 2 := by
    calc 55 = σL.card := h_σL_card.symm
      _ ≤ (Γ.neighborFinset (h.dihedral_uτ hdihe) \ L).card :=
          Finset.card_le_card h_σL_sub
      _ = 2 := h_N_minus_L_card
  omega

/-! ## Step 2/3: x_0 ∈ N(u_τ) -/

theorem dihedral_adj_uτ_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Γ.Adj (h.dihedral_uτ hdihe) h.τ_fix.center := by
  -- uτ ∈ Fix(τ), uτ ≠ center, よって uτ は leaf.
  have h_uτ_τfix : h.τ (h.dihedral_uτ hdihe) = h.dihedral_uτ hdihe := h.dihedral_τ_uτ hdihe
  rcases h.τ_fix.span _ h_uτ_τfix with h_uτ_cen | ⟨i, h_uτ_leaf⟩
  · exact absurd h_uτ_cen.symm (h.dihedral_center_ne_uτ hdihe)
  · rw [h_uτ_leaf]
    exact (h.τ_fix.adj_center i).symm

/-! ## Step 3: x_0 ∉ Fix(σ) -/

theorem dihedral_center_not_σ_fixed
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.σ h.τ_fix.center ≠ h.τ_fix.center := by
  intro h_cen_σfix
  -- center ∈ Fix(σ) ∩ Fix(τ) = {uτ}. But center ≠ uτ.
  have h_eq : h.τ_fix.center = h.dihedral_uτ hdihe :=
    h.dihedral_σFix_τFix_eq_uτ hdihe _ h_cen_σfix h.τ_fix.center_fixed
  exact h.dihedral_center_ne_uτ hdihe h_eq

theorem dihedral_σ_pow_adj_uτ_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) (k : ℕ) :
    Γ.Adj (h.dihedral_uτ hdihe) ((h.σ ^ k) h.τ_fix.center) := by
  -- σ permutes N(uτ); by induction, σ^k center ∈ N(uτ).
  induction k with
  | zero =>
    simp only [pow_zero, Equiv.Perm.one_apply]
    exact h.dihedral_adj_uτ_center hdihe
  | succ n ih =>
    show Γ.Adj _ ((h.σ ^ (n + 1)) h.τ_fix.center)
    rw [pow_succ', Equiv.Perm.mul_apply]
    have h_mem : (h.σ ^ n) h.τ_fix.center ∈ Γ.neighborFinset (h.dihedral_uτ hdihe) := by
      rw [SimpleGraph.mem_neighborFinset]; exact ih
    have h_σ_mem : h.σ ((h.σ ^ n) h.τ_fix.center) ∈
        Γ.neighborFinset (h.dihedral_uτ hdihe) :=
      (h.dihedral_σ_mem_neighborFinset_uτ_iff hdihe _).mpr h_mem
    rw [SimpleGraph.mem_neighborFinset] at h_σ_mem
    exact h_σ_mem

/-! ## Step 7 用: b_τ, c_τ は x_0 と非隣接 -/

theorem dihedral_bτ_ne_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_bτ hdihe ≠ h.τ_fix.center := by
  intro heq
  have : h.σ (h.dihedral_bτ hdihe) = h.dihedral_bτ hdihe := h.dihedral_σ_bτ hdihe
  rw [heq] at this
  exact h.dihedral_center_not_σ_fixed hdihe this

theorem dihedral_cτ_ne_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_cτ hdihe ≠ h.τ_fix.center := by
  intro heq
  have : h.σ (h.dihedral_cτ hdihe) = h.dihedral_cτ hdihe := h.dihedral_σ_cτ hdihe
  rw [heq] at this
  exact h.dihedral_center_not_σ_fixed hdihe this

theorem dihedral_not_adj_bτ_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    ¬ Γ.Adj (h.dihedral_bτ hdihe) h.τ_fix.center := by
  intro h_adj
  -- center は uτ と隣接 (adj_uτ_center).
  have h_uτ_center : Γ.Adj (h.dihedral_uτ hdihe) h.τ_fix.center :=
    h.dihedral_adj_uτ_center hdihe
  -- uτ ≠ bτ, uτ ≁ bτ ⟹ μ = 1: 共通近傍は 1 個.
  -- aτ は uτ-bτ 共通近傍 (cycle 隣接). center も共通近傍と仮定.
  -- aτ ≠ center (∵ aτ ∈ Fix(σ), center ∉).
  -- ⟹ ≥ 2 共通近傍, μ = 1 矛盾.
  have h_uτ_ne_bτ : h.dihedral_uτ hdihe ≠ h.dihedral_bτ hdihe :=
    fun heq => (h.dihedral_uτ_ne_bτ hdihe) heq
  have h_uτ_not_adj_bτ : ¬ Γ.Adj (h.dihedral_uτ hdihe) (h.dihedral_bτ hdihe) :=
    h.dihedral_not_adj_uτ_bτ hdihe
  have h_card : Fintype.card (Γ.commonNeighbors (h.dihedral_uτ hdihe) (h.dihedral_bτ hdihe)) = 1 :=
    h.isMoore.of_not_adj h_uτ_ne_bτ h_uτ_not_adj_bτ
  -- aτ ∈ common.
  have h_aτ_common : h.dihedral_aτ hdihe ∈
      Γ.commonNeighbors (h.dihedral_uτ hdihe) (h.dihedral_bτ hdihe) := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨h.dihedral_adj_uτ_aτ hdihe, (h.dihedral_adj_aτ_bτ hdihe).symm⟩
  -- center ∈ common: uτ ~ center (Step 2/3), bτ ~ center (hypothesis).
  have h_center_common : h.τ_fix.center ∈
      Γ.commonNeighbors (h.dihedral_uτ hdihe) (h.dihedral_bτ hdihe) := by
    rw [SimpleGraph.mem_commonNeighbors]
    refine ⟨h_uτ_center, ?_⟩
    -- bτ ~ center. We have h_adj : Γ.Adj bτ center.
    -- Need Γ.Adj bτ center which IS h_adj.
    exact h_adj
  -- aτ ≠ center: aτ ∈ Fix(σ), center ∉ Fix(σ).
  have h_aτ_ne_center : h.dihedral_aτ hdihe ≠ h.τ_fix.center := by
    intro heq
    have : h.σ (h.dihedral_aτ hdihe) = h.dihedral_aτ hdihe := h.dihedral_σ_aτ hdihe
    rw [heq] at this
    exact h.dihedral_center_not_σ_fixed hdihe this
  -- 2 distinct common neighbors but |common| = 1: contradiction.
  have h_pair_card :
      ({h.dihedral_aτ hdihe, h.τ_fix.center} :
        Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [h_aτ_ne_center]),
        Finset.card_singleton]
  have h_two_le : 2 ≤ Fintype.card (Γ.commonNeighbors (h.dihedral_uτ hdihe) (h.dihedral_bτ hdihe)) := by
    rw [← Set.toFinset_card, ← h_pair_card]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [Set.mem_toFinset]; exact h_aτ_common
    · rw [Set.mem_toFinset]; exact h_center_common
  omega

theorem dihedral_not_adj_cτ_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    ¬ Γ.Adj (h.dihedral_cτ hdihe) h.τ_fix.center := by
  intro h_adj
  have h_uτ_center : Γ.Adj (h.dihedral_uτ hdihe) h.τ_fix.center :=
    h.dihedral_adj_uτ_center hdihe
  have h_uτ_ne_cτ : h.dihedral_uτ hdihe ≠ h.dihedral_cτ hdihe :=
    fun heq => (h.dihedral_uτ_ne_cτ hdihe) heq
  have h_uτ_not_adj_cτ : ¬ Γ.Adj (h.dihedral_uτ hdihe) (h.dihedral_cτ hdihe) :=
    h.dihedral_not_adj_uτ_cτ hdihe
  have h_card : Fintype.card (Γ.commonNeighbors (h.dihedral_uτ hdihe) (h.dihedral_cτ hdihe)) = 1 :=
    h.isMoore.of_not_adj h_uτ_ne_cτ h_uτ_not_adj_cτ
  -- dτ ∈ common (cycle dτ ∼ uτ and dτ ∼ cτ from cycle adj cτ-dτ).
  have h_dτ_common : h.dihedral_dτ hdihe ∈
      Γ.commonNeighbors (h.dihedral_uτ hdihe) (h.dihedral_cτ hdihe) := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨(h.dihedral_adj_dτ_uτ hdihe).symm, (h.dihedral_adj_cτ_dτ hdihe)⟩
  have h_center_common : h.τ_fix.center ∈
      Γ.commonNeighbors (h.dihedral_uτ hdihe) (h.dihedral_cτ hdihe) := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨h_uτ_center, h_adj⟩
  have h_dτ_ne_center : h.dihedral_dτ hdihe ≠ h.τ_fix.center := by
    intro heq
    have : h.σ (h.dihedral_dτ hdihe) = h.dihedral_dτ hdihe := h.dihedral_σ_dτ hdihe
    rw [heq] at this
    exact h.dihedral_center_not_σ_fixed hdihe this
  have h_pair_card :
      ({h.dihedral_dτ hdihe, h.τ_fix.center} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [h_dτ_ne_center]),
        Finset.card_singleton]
  have h_two_le : 2 ≤ Fintype.card (Γ.commonNeighbors (h.dihedral_uτ hdihe) (h.dihedral_cτ hdihe)) := by
    rw [← Set.toFinset_card, ← h_pair_card]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [Set.mem_toFinset]; exact h_dτ_common
    · rw [Set.mem_toFinset]; exact h_center_common
  omega

end Order22ActsOnMoore57

end Moore57
