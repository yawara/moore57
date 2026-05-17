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
  sorry

theorem dihedral_q_not_fix_ρ1
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (q_sub : {y // y ∈ h.dihedral_F0 hdihe})
    (hq : q_sub.val = h.dihedral_q hdihe) :
    h.dihedral_ρ1 hdihe q_sub ≠ q_sub := by
  sorry

/-- Fix(ρ_1) ⊂ L (lift to subtype). -/
theorem dihedral_fix_ρ1_subset_L
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (y : {y // y ∈ h.dihedral_F0 hdihe})
    (hy : h.dihedral_ρ1 hdihe y = y) :
    y.val ∈ h.dihedral_L hdihe := by
  sorry

/-! ## 最終: |Fix(τ) ∩ S| 偶数 -/

theorem dihedral_fix_τ_adj_σ_card_even
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    2 ∣ (Finset.univ.filter
      (fun x : V => h.τ x = x ∧ Γ.Adj x (h.σ x))).card := by
  sorry

end Order22ActsOnMoore57

end Moore57
