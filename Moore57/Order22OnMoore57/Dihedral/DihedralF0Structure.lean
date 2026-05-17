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

/-- N(σ y) = σ-image of N(y) (for graph automorphism σ). -/
private theorem dihedral_neighborFinset_σ_image
    (h : Order22ActsOnMoore57 V Γ) (x : V) :
    (Γ.neighborFinset x).image h.σ = Γ.neighborFinset (h.σ x) := by
  ext y
  rw [Finset.mem_image, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [SimpleGraph.mem_neighborFinset] at hz
    exact (h.σ_aut x z).mp hz
  · intro hy
    refine ⟨h.σ⁻¹ y, ?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset]
      have : Γ.Adj (h.σ x) (h.σ (h.σ⁻¹ y)) := by
        rw [show h.σ (h.σ⁻¹ y) = y from by
          show (h.σ * h.σ⁻¹) y = y
          rw [mul_inv_cancel]; rfl]
        exact hy
      exact (h.σ_aut x (h.σ⁻¹ y)).mpr this
    · show (h.σ * h.σ⁻¹) y = y
      rw [mul_inv_cancel]; rfl

/-- σ は F_0 を F_1 に写す: σ(F_0) = F_1 (as Finset). -/
theorem dihedral_σ_image_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (h.dihedral_F0 hdihe).image h.σ = h.dihedral_F1 hdihe := by
  unfold dihedral_F0 dihedral_F1 branchFiber
  rw [Finset.image_erase h.σ.injective, dihedral_neighborFinset_σ_image,
      h.dihedral_σ_uτ hdihe]

/-! ## Step 6: F_0 は τ-stable -/

/-- N(τ y) = τ-image of N(y). -/
private theorem dihedral_neighborFinset_τ_image
    (h : Order22ActsOnMoore57 V Γ) (x : V) :
    (Γ.neighborFinset x).image h.τ = Γ.neighborFinset (h.τ x) := by
  ext y
  rw [Finset.mem_image, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [SimpleGraph.mem_neighborFinset] at hz
    exact (h.τ_aut x z).mp hz
  · intro hy
    refine ⟨h.τ y, ?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset]
      have : Γ.Adj (h.τ x) (h.τ (h.τ y)) := by
        rw [h.τ_involutive y]; exact hy
      exact (h.τ_aut x (h.τ y)).mpr this
    · exact h.τ_involutive y

theorem dihedral_τ_image_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (h.dihedral_F0 hdihe).image h.τ = h.dihedral_F0 hdihe := by
  unfold dihedral_F0 branchFiber
  rw [Finset.image_erase h.τ_involutive.injective, dihedral_neighborFinset_τ_image,
      h.τ_fix.center_fixed, h.dihedral_τ_uτ hdihe]

theorem dihedral_τ_mem_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) {y : V} (hy : y ∈ h.dihedral_F0 hdihe) :
    h.τ y ∈ h.dihedral_F0 hdihe := by
  rw [← h.dihedral_τ_image_F0 hdihe]
  exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

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

/-- p の uniqueness (任意の v ∈ N(bτ) で center ∈ branchFiber Γ bτ v なら v = p). -/
theorem dihedral_p_unique
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) (v : V)
    (hv_adj : Γ.Adj (h.dihedral_bτ hdihe) v)
    (hv_branch : h.τ_fix.center ∈ branchFiber Γ (h.dihedral_bτ hdihe) v) :
    v = h.dihedral_p hdihe := by
  classical
  rcases h.isMoore.existsUnique_branch_of_not_adj_center
    (u := h.dihedral_bτ hdihe) (x := h.τ_fix.center)
    (h.dihedral_bτ_ne_center hdihe)
    (h.dihedral_not_adj_bτ_center hdihe) with ⟨w, _, huniq⟩
  have h_v_eq_w : v = w := huniq v ⟨hv_adj, hv_branch⟩
  have h_p_eq_w : h.dihedral_p hdihe = w :=
    huniq _ ⟨h.dihedral_p_adj_bτ hdihe, h.dihedral_p_mem_branch hdihe⟩
  rw [h_v_eq_w, h_p_eq_w]

theorem dihedral_p_ne_uτ
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_p hdihe ≠ h.dihedral_uτ hdihe := by
  intro h_eq
  -- p ∼ bτ. If p = uτ, then uτ ∼ bτ, contradicting `not_adj_uτ_bτ`.
  have h_adj : Γ.Adj (h.dihedral_bτ hdihe) (h.dihedral_p hdihe) := h.dihedral_p_adj_bτ hdihe
  rw [h_eq] at h_adj
  exact h.dihedral_not_adj_uτ_bτ hdihe h_adj.symm

theorem dihedral_p_mem_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_p hdihe ∈ h.dihedral_F0 hdihe := by
  unfold dihedral_F0
  rw [mem_branchFiber]
  exact ⟨h.dihedral_p_ne_uτ hdihe, h.dihedral_p_adj_center hdihe⟩

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

theorem dihedral_q_mem_branch
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ_fix.center ∈ branchFiber Γ (h.dihedral_cτ hdihe) (h.dihedral_q hdihe) := by
  classical
  exact (h.isMoore.existsUnique_branch_of_not_adj_center
    (u := h.dihedral_cτ hdihe) (x := h.τ_fix.center)
    (h.dihedral_cτ_ne_center hdihe)
    (h.dihedral_not_adj_cτ_center hdihe)).choose_spec.1.2

theorem dihedral_q_adj_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Γ.Adj h.τ_fix.center (h.dihedral_q hdihe) := by
  have := h.dihedral_q_mem_branch hdihe
  rw [mem_branchFiber] at this
  exact this.2.symm

theorem dihedral_q_unique
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) (v : V)
    (hv_adj : Γ.Adj (h.dihedral_cτ hdihe) v)
    (hv_branch : h.τ_fix.center ∈ branchFiber Γ (h.dihedral_cτ hdihe) v) :
    v = h.dihedral_q hdihe := by
  classical
  rcases h.isMoore.existsUnique_branch_of_not_adj_center
    (u := h.dihedral_cτ hdihe) (x := h.τ_fix.center)
    (h.dihedral_cτ_ne_center hdihe)
    (h.dihedral_not_adj_cτ_center hdihe) with ⟨w, _, huniq⟩
  have h_v_eq_w : v = w := huniq v ⟨hv_adj, hv_branch⟩
  have h_q_eq_w : h.dihedral_q hdihe = w :=
    huniq _ ⟨h.dihedral_q_adj_cτ hdihe, h.dihedral_q_mem_branch hdihe⟩
  rw [h_v_eq_w, h_q_eq_w]

theorem dihedral_q_ne_uτ
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_q hdihe ≠ h.dihedral_uτ hdihe := by
  intro h_eq
  have h_adj : Γ.Adj (h.dihedral_cτ hdihe) (h.dihedral_q hdihe) := h.dihedral_q_adj_cτ hdihe
  rw [h_eq] at h_adj
  exact h.dihedral_not_adj_uτ_cτ hdihe h_adj.symm

theorem dihedral_q_mem_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_q hdihe ∈ h.dihedral_F0 hdihe := by
  unfold dihedral_F0
  rw [mem_branchFiber]
  exact ⟨h.dihedral_q_ne_uτ hdihe, h.dihedral_q_adj_center hdihe⟩

theorem dihedral_p_ne_q
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_p hdihe ≠ h.dihedral_q hdihe := by
  intro h_eq
  -- p ∼ bτ, q ∼ cτ, bτ ∼ cτ. If p = q, then triangle bτ-p-cτ.
  have h_p_bτ : Γ.Adj (h.dihedral_bτ hdihe) (h.dihedral_p hdihe) := h.dihedral_p_adj_bτ hdihe
  have h_q_cτ : Γ.Adj (h.dihedral_cτ hdihe) (h.dihedral_q hdihe) := h.dihedral_q_adj_cτ hdihe
  have h_bτ_cτ : Γ.Adj (h.dihedral_bτ hdihe) (h.dihedral_cτ hdihe) :=
    h.dihedral_adj_bτ_cτ hdihe
  rw [h_eq] at h_p_bτ
  -- bτ ~ q, cτ ~ q, bτ ~ cτ: triangle.
  exact h.isMoore.no_triangle h_bτ_cτ h_q_cτ h_p_bτ.symm

/-! ## Step 8: τ swaps p, q -/

theorem dihedral_τ_p
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.dihedral_p hdihe) = h.dihedral_q hdihe := by
  -- p ∼ bτ ⟹ τ p ∼ τ bτ = cτ.
  -- p ∼ center, center τ-fixed ⟹ τ p ∼ center.
  -- So τ p is a vertex adjacent to both cτ and center.
  -- By uniqueness (Moore57, μ=1, cτ ≁ center, cτ ≠ center), τ p = q.
  have h_τp_cτ : Γ.Adj (h.dihedral_cτ hdihe) (h.τ (h.dihedral_p hdihe)) := by
    have : Γ.Adj (h.τ (h.dihedral_bτ hdihe)) (h.τ (h.dihedral_p hdihe)) :=
      (h.τ_aut _ _).mp (h.dihedral_p_adj_bτ hdihe)
    rwa [h.dihedral_τ_bτ hdihe] at this
  have h_τp_center : Γ.Adj h.τ_fix.center (h.τ (h.dihedral_p hdihe)) := by
    have : Γ.Adj (h.τ h.τ_fix.center) (h.τ (h.dihedral_p hdihe)) :=
      (h.τ_aut _ _).mp (h.dihedral_p_adj_center hdihe)
    rwa [h.τ_fix.center_fixed] at this
  -- τ p ∈ branchFiber Γ cτ ?: τ p ~ cτ and ? has τ p; we want τ p ∈ N(?) for ?.
  -- Actually we want to show τ p is the unique vertex in N(cτ) ∩ N(center).
  -- By `dihedral_q_unique`, if v ∼ cτ and center ∈ branchFiber Γ cτ v, then v = q.
  -- center ∈ branchFiber Γ cτ (τ p) ↔ center ≠ cτ ∧ Γ.Adj (τ p) center.
  apply h.dihedral_q_unique hdihe (h.τ (h.dihedral_p hdihe)) h_τp_cτ
  rw [mem_branchFiber]
  exact ⟨(h.dihedral_cτ_ne_center hdihe).symm, h_τp_center.symm⟩

theorem dihedral_τ_q
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ (h.dihedral_q hdihe) = h.dihedral_p hdihe := by
  -- Symmetric: q ∼ cτ ⟹ τ q ∼ τ cτ = bτ. q ∼ center ⟹ τ q ∼ center.
  -- By uniqueness, τ q = p.
  have h_τq_bτ : Γ.Adj (h.dihedral_bτ hdihe) (h.τ (h.dihedral_q hdihe)) := by
    have : Γ.Adj (h.τ (h.dihedral_cτ hdihe)) (h.τ (h.dihedral_q hdihe)) :=
      (h.τ_aut _ _).mp (h.dihedral_q_adj_cτ hdihe)
    rwa [h.dihedral_τ_cτ hdihe] at this
  have h_τq_center : Γ.Adj h.τ_fix.center (h.τ (h.dihedral_q hdihe)) := by
    have : Γ.Adj (h.τ h.τ_fix.center) (h.τ (h.dihedral_q hdihe)) :=
      (h.τ_aut _ _).mp (h.dihedral_q_adj_center hdihe)
    rwa [h.τ_fix.center_fixed] at this
  apply h.dihedral_p_unique hdihe (h.τ (h.dihedral_q hdihe)) h_τq_bτ
  rw [mem_branchFiber]
  exact ⟨(h.dihedral_bτ_ne_center hdihe).symm, h_τq_center.symm⟩

end Order22ActsOnMoore57

end Moore57
