import Moore57.Order22OnMoore57.Dihedral.DihedralCenterInNeighborhood
import Moore57.Moore57Graph.BranchFiber.Matching

/-!
# Steps 5-8 (Dihedral): F_0 ファイバー構造

* (Step 5) `F_0 := branchFiber Γ u_τ x_0`, `F_1 := branchFiber Γ u_τ (σ x_0)`.
  |F_0| = |F_1| = 56, σ(F_0) = F_1.
* (Step 6) F_0 は τ-stable.
* (Step 7) `p ∈ N(b_τ) ∩ F_0`, `q ∈ N(c_τ) ∩ F_0` (一意).
* (Step 8) τ(p) = q, τ(q) = p.
-/

namespace Moore57

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable (h : Order22ActsOnMoore57 V Γ)

/-! ## Step 5: F_0, F_1 -/

/-- F_0 := branchFiber Γ u_τ x_0. -/
noncomputable def dihedral_F0 (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : Finset V :=
  branchFiber Γ (h.dihedral_uτ hdihe) h.τ_fix.center

/-- F_1 := branchFiber Γ u_τ (σ x_0). -/
noncomputable def dihedral_F1 (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : Finset V :=
  branchFiber Γ (h.dihedral_uτ hdihe) (h.σ h.τ_fix.center)

theorem dihedral_F0_card
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (h.dihedral_F0 hdihe).card = 56 :=
  h.isMoore.branchFiber_card (h.dihedral_adj_uτ_center hdihe)

theorem dihedral_F1_card
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (h.dihedral_F1 hdihe).card = 56 := by
  apply h.isMoore.branchFiber_card
  exact h.dihedral_σ_pow_adj_uτ_center hdihe 1

/-- σ x_0 ≠ x_0 (B_0 が length 11). -/
theorem dihedral_σ_center_ne_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.σ h.τ_fix.center ≠ h.τ_fix.center :=
  h.dihedral_center_not_σ_fixed hdihe

/-- σ は F_0 を F_1 に写す: σ(F_0) = F_1 (as Finset). -/
theorem dihedral_σ_image_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (h.dihedral_F0 hdihe).image h.σ = h.dihedral_F1 hdihe := by
  sorry

/-! ## Step 6: F_0 は τ-stable -/

theorem dihedral_τ_image_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (h.dihedral_F0 hdihe).image h.τ = h.dihedral_F0 hdihe := by
  sorry

theorem dihedral_τ_mem_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) {y : V} (hy : y ∈ h.dihedral_F0 hdihe) :
    h.τ y ∈ h.dihedral_F0 hdihe := by
  sorry

/-! ## Step 7: p, q の存在と F_0 への所属 -/

/-- p = b_τ と x_0 の唯一の共通近傍. -/
noncomputable def dihedral_p (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : V := by
  classical
  exact (h.isMoore.existsUnique_branch_of_not_adj_center
    (u := h.dihedral_bτ hdihe) (x := h.τ_fix.center)
    (h.dihedral_bτ_ne_center hdihe)
    (h.dihedral_not_adj_bτ_center hdihe)).choose

theorem dihedral_p_adj_bτ
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Γ.Adj (h.dihedral_bτ hdihe) (h.dihedral_p hdihe) := by
  classical
  exact (h.isMoore.existsUnique_branch_of_not_adj_center
    (u := h.dihedral_bτ hdihe) (x := h.τ_fix.center)
    (h.dihedral_bτ_ne_center hdihe)
    (h.dihedral_not_adj_bτ_center hdihe)).choose_spec.1.1

theorem dihedral_p_mem_branch
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ_fix.center ∈ branchFiber Γ (h.dihedral_bτ hdihe) (h.dihedral_p hdihe) := by
  classical
  exact (h.isMoore.existsUnique_branch_of_not_adj_center
    (u := h.dihedral_bτ hdihe) (x := h.τ_fix.center)
    (h.dihedral_bτ_ne_center hdihe)
    (h.dihedral_not_adj_bτ_center hdihe)).choose_spec.1.2

theorem dihedral_p_adj_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Γ.Adj h.τ_fix.center (h.dihedral_p hdihe) := by
  have := h.dihedral_p_mem_branch hdihe
  rw [mem_branchFiber] at this
  exact this.2.symm

theorem dihedral_p_ne_uτ
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_p hdihe ≠ h.dihedral_uτ hdihe := by
  sorry

theorem dihedral_p_mem_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_p hdihe ∈ h.dihedral_F0 hdihe := by
  sorry

/-- q = c_τ と x_0 の唯一の共通近傍. -/
noncomputable def dihedral_q (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : V := by
  classical
  exact (h.isMoore.existsUnique_branch_of_not_adj_center
    (u := h.dihedral_cτ hdihe) (x := h.τ_fix.center)
    (h.dihedral_cτ_ne_center hdihe)
    (h.dihedral_not_adj_cτ_center hdihe)).choose

theorem dihedral_q_adj_cτ
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Γ.Adj (h.dihedral_cτ hdihe) (h.dihedral_q hdihe) := by
  classical
  exact (h.isMoore.existsUnique_branch_of_not_adj_center
    (u := h.dihedral_cτ hdihe) (x := h.τ_fix.center)
    (h.dihedral_cτ_ne_center hdihe)
    (h.dihedral_not_adj_cτ_center hdihe)).choose_spec.1.1

theorem dihedral_q_adj_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Γ.Adj h.τ_fix.center (h.dihedral_q hdihe) := by
  classical
  have : h.τ_fix.center ∈ branchFiber Γ (h.dihedral_cτ hdihe) (h.dihedral_q hdihe) :=
    (h.isMoore.existsUnique_branch_of_not_adj_center
      (u := h.dihedral_cτ hdihe) (x := h.τ_fix.center)
      (h.dihedral_cτ_ne_center hdihe)
      (h.dihedral_not_adj_cτ_center hdihe)).choose_spec.1.2
  rw [mem_branchFiber] at this
  exact this.2.symm

theorem dihedral_q_ne_uτ
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_q hdihe ≠ h.dihedral_uτ hdihe := by
  sorry

theorem dihedral_q_mem_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_q hdihe ∈ h.dihedral_F0 hdihe := by
  sorry

theorem dihedral_p_ne_q
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_p hdihe ≠ h.dihedral_q hdihe := by
  sorry

/-! ## Step 8: τ swaps p, q -/

theorem dihedral_τ_p
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.dihedral_p hdihe) = h.dihedral_q hdihe := by
  sorry

theorem dihedral_τ_q
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.dihedral_q hdihe) = h.dihedral_p hdihe := by
  sorry

end Order22ActsOnMoore57

end Moore57
