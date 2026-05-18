import Moore57.Order22OnMoore57.Dihedral.DihedralPiOneInvolution

/-!
# Step 15 (Dihedral): 結論合成

* p, q ∉ Fix(ρ_1) (4-cycle 排除).
* Fix(ρ_1) ⊂ L.
* |Fix(ρ_1)| ≡ |F_0| = 56 ≡ 0 (mod 2) (involution parity).
* Fix(ρ_1) ∩ L = Fix(π_1) ∩ L = L ∩ S.
* |Fix(τ) ∩ S| = |L ∩ S| (∵ x_0, u_τ ∉ S).
* ⟹ |Fix(τ) ∩ S| ≡ 0 (mod 2).

最終結果 `dihedral_fix_τ_adj_σ_card_even` を提供.
-/

namespace Moore57

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable (h : Order22ActsOnMoore57 V Γ)

/-! ## Step 15: p, q ∉ Fix(ρ_1) -/

theorem dihedral_p_not_fix_ρ1
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (p_sub : {y // y ∈ h.dihedral_F0 hdihe})
    (hp : p_sub.val = h.dihedral_p hdihe) :
    h.dihedral_ρ1 hdihe p_sub ≠ p_sub := by
  intro h_fix
  -- ρ_1 p_sub = p_sub ⟹ τ (π_1 p_sub).val = p_sub.val ⟹ (π_1 p_sub).val = τ p_sub.val.
  have h_τπ1p : h.τ (h.dihedral_π1 hdihe p_sub).val = p_sub.val :=
    congr_arg Subtype.val h_fix
  have h_π1p_τp : (h.dihedral_π1 hdihe p_sub).val = h.τ p_sub.val := by
    have hcong := congr_arg h.τ h_τπ1p
    rw [h.τ_involutive] at hcong
    exact hcong
  rw [hp, h.dihedral_τ_p hdihe] at h_π1p_τp
  -- h_π1p_τp : (π_1 p_sub).val = q
  rw [h.dihedral_π1_val_eq hdihe p_sub] at h_π1p_τp
  -- h_π1p_τp : σ⁻¹ (m_1 p_sub).val = q
  have h_m1p_σq : (h.dihedral_m1 hdihe p_sub).val = h.σ (h.dihedral_q hdihe) := by
    have hcong := congr_arg h.σ h_π1p_τp
    rw [show h.σ (h.σ⁻¹ (h.dihedral_m1 hdihe p_sub).val) =
         (h.dihedral_m1 hdihe p_sub).val from by
      change (h.σ * h.σ⁻¹) (h.dihedral_m1 hdihe p_sub).val =
           (h.dihedral_m1 hdihe p_sub).val
      rw [mul_inv_cancel]; rfl] at hcong
    exact hcong
  -- p ~ m_1 p = σ q
  have h_p_σq : Γ.Adj (h.dihedral_p hdihe) (h.σ (h.dihedral_q hdihe)) := by
    have h_adj := h.dihedral_m1_val_adj hdihe p_sub
    rw [hp, h_m1p_σq] at h_adj
    exact h_adj
  -- Build 4-cycle: b_τ - p - σ q - c_τ - b_τ.
  have h_bτ_p : Γ.Adj (h.dihedral_bτ hdihe) (h.dihedral_p hdihe) := h.dihedral_p_adj_bτ hdihe
  have h_σq_cτ : Γ.Adj (h.σ (h.dihedral_q hdihe)) (h.dihedral_cτ hdihe) := by
    have h_cτ_q : Γ.Adj (h.dihedral_cτ hdihe) (h.dihedral_q hdihe) := h.dihedral_q_adj_cτ hdihe
    have h_σ : Γ.Adj (h.σ (h.dihedral_cτ hdihe)) (h.σ (h.dihedral_q hdihe)) :=
      (h.σ_aut _ _).mp h_cτ_q
    rw [h.dihedral_σ_cτ hdihe] at h_σ
    exact h_σ.symm
  have h_cτ_bτ : Γ.Adj (h.dihedral_cτ hdihe) (h.dihedral_bτ hdihe) :=
    (h.dihedral_adj_bτ_cτ hdihe).symm
  -- Distinctness
  have h_bτ_ne_p : h.dihedral_bτ hdihe ≠ h.dihedral_p hdihe := h_bτ_p.ne
  have h_p_ne_σq : h.dihedral_p hdihe ≠ h.σ (h.dihedral_q hdihe) := h_p_σq.ne
  have h_σq_ne_cτ : h.σ (h.dihedral_q hdihe) ≠ h.dihedral_cτ hdihe := h_σq_cτ.ne
  have h_bτ_ne_cτ : h.dihedral_bτ hdihe ≠ h.dihedral_cτ hdihe := h.dihedral_bτ_ne_cτ hdihe
  -- b_τ ≠ σ q: σ q ∈ N(σ x_0). If b_τ = σ q then b_τ ∈ N(σ x_0).
  -- σ-aut: b_τ ~ σ x_0 ↔ b_τ ~ x_0 (σ fixes b_τ). But b_τ ≁ x_0.
  have h_bτ_ne_σq : h.dihedral_bτ hdihe ≠ h.σ (h.dihedral_q hdihe) := by
    intro heq
    have h_σq_x1 : Γ.Adj (h.σ (h.dihedral_q hdihe)) (h.σ h.τ_fix.center) := by
      have h_q_x0 : Γ.Adj (h.dihedral_q hdihe) h.τ_fix.center :=
        (h.dihedral_q_adj_center hdihe).symm
      exact (h.σ_aut _ _).mp h_q_x0
    rw [← heq] at h_σq_x1
    -- h_σq_x1 : Γ.Adj b_τ (σ x_0)
    have h_aut := h.σ_aut (h.dihedral_bτ hdihe) h.τ_fix.center
    rw [h.dihedral_σ_bτ hdihe] at h_aut
    have h_bτ_x0 : Γ.Adj (h.dihedral_bτ hdihe) h.τ_fix.center := h_aut.mpr h_σq_x1
    exact h.dihedral_not_adj_bτ_center hdihe h_bτ_x0
  -- p ≠ c_τ: c_τ ≁ x_0, p ~ x_0.
  have h_p_ne_cτ : h.dihedral_p hdihe ≠ h.dihedral_cτ hdihe := by
    intro heq
    have h_p_x0 : Γ.Adj (h.dihedral_p hdihe) h.τ_fix.center :=
      (h.dihedral_p_adj_center hdihe).symm
    rw [heq] at h_p_x0
    exact h.dihedral_not_adj_cτ_center hdihe h_p_x0
  exact h.isMoore.no_four_cycle h_bτ_ne_p h_bτ_ne_σq h_bτ_ne_cτ h_p_ne_σq h_p_ne_cτ
    h_σq_ne_cτ h_bτ_p h_p_σq h_σq_cτ h_cτ_bτ

theorem dihedral_q_not_fix_ρ1
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (q_sub : {y // y ∈ h.dihedral_F0 hdihe})
    (hq : q_sub.val = h.dihedral_q hdihe) :
    h.dihedral_ρ1 hdihe q_sub ≠ q_sub := by
  intro h_fix
  -- ρ_1 q_sub = q_sub ⟹ (π_1 q_sub).val = τ q_sub.val = p.
  have h_τπ1q : h.τ (h.dihedral_π1 hdihe q_sub).val = q_sub.val :=
    congr_arg Subtype.val h_fix
  have h_π1q_τq : (h.dihedral_π1 hdihe q_sub).val = h.τ q_sub.val := by
    have hcong := congr_arg h.τ h_τπ1q
    rw [h.τ_involutive] at hcong
    exact hcong
  rw [hq, h.dihedral_τ_q hdihe] at h_π1q_τq
  rw [h.dihedral_π1_val_eq hdihe q_sub] at h_π1q_τq
  have h_m1q_σp : (h.dihedral_m1 hdihe q_sub).val = h.σ (h.dihedral_p hdihe) := by
    have hcong := congr_arg h.σ h_π1q_τq
    rw [show h.σ (h.σ⁻¹ (h.dihedral_m1 hdihe q_sub).val) =
         (h.dihedral_m1 hdihe q_sub).val from by
      change (h.σ * h.σ⁻¹) (h.dihedral_m1 hdihe q_sub).val =
           (h.dihedral_m1 hdihe q_sub).val
      rw [mul_inv_cancel]; rfl] at hcong
    exact hcong
  have h_q_σp : Γ.Adj (h.dihedral_q hdihe) (h.σ (h.dihedral_p hdihe)) := by
    have h_adj := h.dihedral_m1_val_adj hdihe q_sub
    rw [hq, h_m1q_σp] at h_adj
    exact h_adj
  -- 4-cycle: c_τ - q - σ p - b_τ - c_τ.
  have h_cτ_q : Γ.Adj (h.dihedral_cτ hdihe) (h.dihedral_q hdihe) := h.dihedral_q_adj_cτ hdihe
  have h_σp_bτ : Γ.Adj (h.σ (h.dihedral_p hdihe)) (h.dihedral_bτ hdihe) := by
    have h_bτ_p : Γ.Adj (h.dihedral_bτ hdihe) (h.dihedral_p hdihe) := h.dihedral_p_adj_bτ hdihe
    have h_σ : Γ.Adj (h.σ (h.dihedral_bτ hdihe)) (h.σ (h.dihedral_p hdihe)) :=
      (h.σ_aut _ _).mp h_bτ_p
    rw [h.dihedral_σ_bτ hdihe] at h_σ
    exact h_σ.symm
  have h_bτ_cτ : Γ.Adj (h.dihedral_bτ hdihe) (h.dihedral_cτ hdihe) :=
    h.dihedral_adj_bτ_cτ hdihe
  have h_cτ_ne_q : h.dihedral_cτ hdihe ≠ h.dihedral_q hdihe := h_cτ_q.ne
  have h_q_ne_σp : h.dihedral_q hdihe ≠ h.σ (h.dihedral_p hdihe) := h_q_σp.ne
  have h_σp_ne_bτ : h.σ (h.dihedral_p hdihe) ≠ h.dihedral_bτ hdihe := h_σp_bτ.ne
  have h_cτ_ne_bτ : h.dihedral_cτ hdihe ≠ h.dihedral_bτ hdihe :=
    (h.dihedral_bτ_ne_cτ hdihe).symm
  -- c_τ ≠ σ p: σ p ∈ N(σ x_0). If c_τ = σ p, then c_τ ~ σ x_0 ↔ c_τ ~ x_0. But c_τ ≁ x_0.
  have h_cτ_ne_σp : h.dihedral_cτ hdihe ≠ h.σ (h.dihedral_p hdihe) := by
    intro heq
    have h_σp_x1 : Γ.Adj (h.σ (h.dihedral_p hdihe)) (h.σ h.τ_fix.center) := by
      have h_p_x0 : Γ.Adj (h.dihedral_p hdihe) h.τ_fix.center :=
        (h.dihedral_p_adj_center hdihe).symm
      exact (h.σ_aut _ _).mp h_p_x0
    rw [← heq] at h_σp_x1
    have h_aut := h.σ_aut (h.dihedral_cτ hdihe) h.τ_fix.center
    rw [h.dihedral_σ_cτ hdihe] at h_aut
    have h_cτ_x0 : Γ.Adj (h.dihedral_cτ hdihe) h.τ_fix.center := h_aut.mpr h_σp_x1
    exact h.dihedral_not_adj_cτ_center hdihe h_cτ_x0
  -- q ≠ b_τ: b_τ ≁ x_0, q ~ x_0.
  have h_q_ne_bτ : h.dihedral_q hdihe ≠ h.dihedral_bτ hdihe := by
    intro heq
    have h_q_x0 : Γ.Adj (h.dihedral_q hdihe) h.τ_fix.center :=
      (h.dihedral_q_adj_center hdihe).symm
    rw [heq] at h_q_x0
    exact h.dihedral_not_adj_bτ_center hdihe h_q_x0
  exact h.isMoore.no_four_cycle h_cτ_ne_q h_cτ_ne_σp h_cτ_ne_bτ h_q_ne_σp h_q_ne_bτ
    h_σp_ne_bτ h_cτ_q h_q_σp h_σp_bτ h_bτ_cτ

/-- Fix(ρ_1) ⊂ L (lift to subtype). -/
theorem dihedral_fix_ρ1_subset_L
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (y : {y // y ∈ h.dihedral_F0 hdihe})
    (hy : h.dihedral_ρ1 hdihe y = y) :
    y.val ∈ h.dihedral_L hdihe := by
  unfold dihedral_L
  rw [Finset.mem_sdiff]
  refine ⟨y.property, ?_⟩
  rw [Finset.mem_insert, Finset.mem_singleton]
  rintro (h_eq | h_eq)
  · exact h.dihedral_p_not_fix_ρ1 hdihe y h_eq hy
  · exact h.dihedral_q_not_fix_ρ1 hdihe y h_eq hy

/-! ## サブ補題: Fix(τ) ∩ S ⊆ F_0 -/

/-- τ-fixed かつ σ-隣接 (∈ S) なら F_0 に属する.
center / u_τ は S に属さないので, τ-fixed leaves で u_τ 以外 = F_0 の leaves. -/
theorem dihedral_fix_τ_adj_σ_mem_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) {x : V}
    (hτ : h.τ x = x) (hadj : Γ.Adj x (h.σ x)) :
    x ∈ h.dihedral_F0 hdihe := by
  unfold dihedral_F0
  rw [mem_branchFiber]
  rcases h.τ_fix.span x hτ with h_x_cen | ⟨j, h_x_leaf⟩
  · -- x = center. center ~ σ center: triangle u_τ-center-σ center.
    exfalso
    rw [h_x_cen] at hadj
    have h_uτ_cen : Γ.Adj (h.dihedral_uτ hdihe) h.τ_fix.center :=
      h.dihedral_adj_uτ_center hdihe
    have h_uτ_σcen : Γ.Adj (h.dihedral_uτ hdihe) (h.σ h.τ_fix.center) :=
      h.dihedral_σ_pow_adj_uτ_center hdihe 1
    exact h.isMoore.no_triangle h_uτ_cen hadj h_uτ_σcen.symm
  · -- x = leaf j.
    refine ⟨?_, ?_⟩
    · -- x ≠ u_τ
      intro h_eq
      rw [h_eq] at hadj
      rw [h.dihedral_σ_uτ hdihe] at hadj
      exact SimpleGraph.irrefl Γ hadj
    · -- center ~ x
      rw [h_x_leaf]
      exact h.τ_fix.adj_center j

/-! ## Fix(ρ_1Perm) と Fix(τ) ∩ S の bijection -/

/-- subtype 側の固定点集合. -/
noncomputable def dihedral_fixOnSubtype (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Finset {y // y ∈ h.dihedral_F0 hdihe} :=
  Finset.univ.filter (fun y => h.dihedral_ρ1 hdihe y = y)

/-- V 側の固定点集合 (Fix(τ) ∩ S). -/
noncomputable def dihedral_fixτS (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : Finset V :=
  Finset.univ.filter (fun x : V => h.τ x = x ∧ Γ.Adj x (h.σ x))

theorem dihedral_fixOnSubtype_image_val_eq_fixτS
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (h.dihedral_fixOnSubtype hdihe).image Subtype.val = h.dihedral_fixτS hdihe := by
  ext x
  rw [Finset.mem_image]
  unfold dihedral_fixτS dihedral_fixOnSubtype
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Finset.mem_filter] at hy
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · -- τ y.val = y.val (∵ y.val ∈ L).
      have h_y_L : y.val ∈ h.dihedral_L hdihe :=
        h.dihedral_fix_ρ1_subset_L hdihe y hy.2
      exact h.dihedral_τ_eq_self_of_mem_L hdihe h_y_L
    · -- y.val ~ σ y.val (from π_1 y = y).
      have h_y_L : y.val ∈ h.dihedral_L hdihe :=
        h.dihedral_fix_ρ1_subset_L hdihe y hy.2
      have h_τy : h.τ y.val = y.val := h.dihedral_τ_eq_self_of_mem_L hdihe h_y_L
      have h_ρ1y : (h.dihedral_ρ1 hdihe y).val = y.val := congr_arg Subtype.val hy.2
      -- (ρ_1 y).val = τ (π_1 y).val by def.
      have h_π1y : (h.dihedral_π1 hdihe y).val = y.val := by
        have h_ρ1y' : h.τ (h.dihedral_π1 hdihe y).val = y.val := h_ρ1y
        have hcong := congr_arg h.τ h_ρ1y'
        rw [h.τ_involutive, h_τy] at hcong
        exact hcong
      have h_π1y_sub : h.dihedral_π1 hdihe y = y := Subtype.ext h_π1y
      exact (h.dihedral_π1_fix_iff_adj hdihe y).mp h_π1y_sub
  · rintro ⟨_, hτ, hadj⟩
    have h_x_F0 : x ∈ h.dihedral_F0 hdihe :=
      h.dihedral_fix_τ_adj_σ_mem_F0 hdihe hτ hadj
    refine ⟨⟨x, h_x_F0⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    -- ρ_1 ⟨x, _⟩ = ⟨x, _⟩: τ (π_1 ⟨x, _⟩).val = x.
    apply Subtype.ext
    change h.τ (h.dihedral_π1 hdihe ⟨x, h_x_F0⟩).val = x
    have h_π1_fix : h.dihedral_π1 hdihe ⟨x, h_x_F0⟩ = ⟨x, h_x_F0⟩ :=
      (h.dihedral_π1_fix_iff_adj hdihe ⟨x, h_x_F0⟩).mpr hadj
    rw [h_π1_fix]
    exact hτ

theorem dihedral_fixOnSubtype_card_eq
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (h.dihedral_fixOnSubtype hdihe).card = (h.dihedral_fixτS hdihe).card := by
  rw [← h.dihedral_fixOnSubtype_image_val_eq_fixτS hdihe]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

/-! ## 最終: |Fix(τ) ∩ S| 偶数 -/

theorem dihedral_fix_τ_adj_σ_card_even
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    2 ∣ (Finset.univ.filter
      (fun x : V => h.τ x = x ∧ Γ.Adj x (h.σ x))).card := by
  classical
  -- ρ_1Perm is involutive. By parity, 2 ∣ |F_0| - fixedCount.
  have h_parity : 2 ∣ Fintype.card {y // y ∈ h.dihedral_F0 hdihe} -
      fixedVertexCount (h.dihedral_ρ1Perm hdihe) :=
    two_dvd_card_sub_fixedVertexCount_of_involutive _ (h.dihedral_ρ1_involutive hdihe)
  have h_F0_card : Fintype.card {y // y ∈ h.dihedral_F0 hdihe} = 56 := by
    rw [Fintype.card_coe, h.dihedral_F0_card hdihe]
  -- fixedVertexCount (ρ_1Perm) = (fixOnSubtype).card.
  have h_fvc : fixedVertexCount (h.dihedral_ρ1Perm hdihe) =
      (h.dihedral_fixOnSubtype hdihe).card := rfl
  rw [h_F0_card, h_fvc] at h_parity
  -- h_parity : 2 ∣ 56 - fixOnSubtype.card
  -- fixOnSubtype.card ≤ 56.
  have h_card_le : (h.dihedral_fixOnSubtype hdihe).card ≤ 56 := by
    rw [← h_F0_card]
    exact Finset.card_le_card (Finset.subset_univ _)
  -- 2 ∣ 56 ⟹ 2 ∣ fixOnSubtype.card.
  have h_2_dvd : 2 ∣ (h.dihedral_fixOnSubtype hdihe).card := by
    obtain ⟨k, hk⟩ := h_parity
    refine ⟨28 - k, ?_⟩
    omega
  rw [h.dihedral_fixOnSubtype_card_eq hdihe] at h_2_dvd
  unfold dihedral_fixτS at h_2_dvd
  exact h_2_dvd

end Order22ActsOnMoore57

end Moore57
