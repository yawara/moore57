import Moore57.Order22OnMoore57.Dihedral.DihedralF0Structure

/-!
# Step 9 (Dihedral): L := F_0 \ {p, q}, |L| = 54

* Fix(τ|F_0) = F_0 ∩ ({x_0, u_τ} ∪ leaves) と分解.
* x_0 ∉ F_0 (loopless), u_τ ∉ F_0 (loopless).
* leaves ⊂ N(x_0); 55 leaves のうち u_τ に対応する index `j_τ` は F_0 から外す.
* よって Fix(τ|F_0) = 54 leaves.
* p, q ∉ Fix(τ|F_0) (Step 8: τ swap).
* L := F_0 \ {p, q} = 54 leaves, |L| = 54.
-/

namespace Moore57

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable (h : Order22ActsOnMoore57 V Γ)

/-- L := F_0 \ {p, q}. -/
noncomputable def dihedral_L (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : Finset V :=
  h.dihedral_F0 hdihe \ {h.dihedral_p hdihe, h.dihedral_q hdihe}

theorem dihedral_L_card
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (h.dihedral_L hdihe).card = 54 := by
  unfold dihedral_L
  have h_pq_sub : ({h.dihedral_p hdihe, h.dihedral_q hdihe} : Finset V) ⊆
      h.dihedral_F0 hdihe := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h.dihedral_p_mem_F0 hdihe
    · exact h.dihedral_q_mem_F0 hdihe
  have h_pq_card : ({h.dihedral_p hdihe, h.dihedral_q hdihe} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [h.dihedral_p_ne_q hdihe]),
        Finset.card_singleton]
  rw [Finset.card_sdiff_of_subset h_pq_sub, h.dihedral_F0_card hdihe, h_pq_card]

theorem dihedral_L_subset_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_L hdihe ⊆ h.dihedral_F0 hdihe := by
  unfold dihedral_L
  exact Finset.sdiff_subset

/-! ## uτ を leaf として index -/

/-- uτ は K_{1,55} の leaf であるから一意の leaf index を持つ. -/
noncomputable def dihedral_uτ_leafIndex
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : Fin 55 := by
  classical
  have h_uτ_τfix : h.τ (h.dihedral_uτ hdihe) = h.dihedral_uτ hdihe := h.dihedral_τ_uτ hdihe
  exact (h.τ_fix.span _ h_uτ_τfix).resolve_left
    (fun h_cen => h.dihedral_center_ne_uτ hdihe h_cen.symm) |>.choose

theorem dihedral_uτ_eq_leaf
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_uτ hdihe = h.τ_fix.leaf (h.dihedral_uτ_leafIndex hdihe) := by
  classical
  have h_uτ_τfix : h.τ (h.dihedral_uτ hdihe) = h.dihedral_uτ hdihe := h.dihedral_τ_uτ hdihe
  exact (h.τ_fix.span _ h_uτ_τfix).resolve_left
    (fun h_cen => h.dihedral_center_ne_uτ hdihe h_cen.symm) |>.choose_spec

/-! ## Step 9: Fix(τ|F_0) = L -/

/-- F_0 内の τ-不動点はちょうど leaves で uτ 以外の集合. -/
theorem dihedral_fix_τ_on_F0_eq_leaves_minus_uτ
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (h.dihedral_F0 hdihe).filter (fun y => h.τ y = y) =
      (Finset.univ.image h.τ_fix.leaf).erase (h.dihedral_uτ hdihe) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hyF, hyτ⟩
    -- y ∈ F_0, τ y = y. y は center または leaf.
    rcases h.τ_fix.span y hyτ with h_cen | ⟨j, hyj⟩
    · -- y = center: でも center ∉ F_0 (loop). 矛盾.
      exfalso
      unfold dihedral_F0 at hyF
      rw [mem_branchFiber] at hyF
      rw [h_cen] at hyF
      exact SimpleGraph.irrefl Γ hyF.2
    · -- y = leaf j. y ≠ uτ (∵ uτ ∉ F_0).
      refine ⟨?_, j, hyj.symm⟩
      intro h_eq
      rw [h_eq] at hyF
      unfold dihedral_F0 at hyF
      rw [mem_branchFiber] at hyF
      exact hyF.1 rfl
  · rintro ⟨hy_ne_uτ, j, hyj⟩
    -- y = leaf j (= image), y ≠ uτ.
    refine ⟨?_, ?_⟩
    · -- y ∈ F_0
      unfold dihedral_F0
      rw [mem_branchFiber]
      refine ⟨hy_ne_uτ, ?_⟩
      rw [← hyj]
      exact h.τ_fix.adj_center j
    · -- τ y = y
      rw [← hyj]
      exact h.τ_fix.leaf_fixed j

/-- (image of leaf) \ {uτ} の cardinality = 54. -/
theorem dihedral_leaves_minus_uτ_card
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    ((Finset.univ.image h.τ_fix.leaf).erase (h.dihedral_uτ hdihe)).card = 54 := by
  rw [Finset.card_erase_of_mem]
  · rw [Finset.card_image_of_injective _ h.τ_fix.leaf_injective]
    simp
  · rw [Finset.mem_image]
    exact ⟨h.dihedral_uτ_leafIndex hdihe, Finset.mem_univ _, (h.dihedral_uτ_eq_leaf hdihe).symm⟩

/-- F_0 内の τ-不動点はちょうど 54 個. -/
theorem dihedral_fix_τ_on_F0_card
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    ((h.dihedral_F0 hdihe).filter (fun y => h.τ y = y)).card = 54 := by
  rw [h.dihedral_fix_τ_on_F0_eq_leaves_minus_uτ hdihe]
  exact h.dihedral_leaves_minus_uτ_card hdihe

/-- Fix(τ|F_0) ⊆ L (forward subset). -/
theorem dihedral_fix_τ_on_F0_sub_L
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (h.dihedral_F0 hdihe).filter (fun y => h.τ y = y) ⊆ h.dihedral_L hdihe := by
  intro y hy
  rw [Finset.mem_filter] at hy
  unfold dihedral_L
  rw [Finset.mem_sdiff]
  refine ⟨hy.1, ?_⟩
  rw [Finset.mem_insert, Finset.mem_singleton]
  rintro (h_eq | h_eq)
  · -- y = p ⟹ τ p = p. But τ p = q ≠ p.
    rw [h_eq] at hy
    have h_τp : h.τ (h.dihedral_p hdihe) = h.dihedral_p hdihe := hy.2
    rw [h.dihedral_τ_p hdihe] at h_τp
    exact h.dihedral_p_ne_q hdihe h_τp.symm
  · rw [h_eq] at hy
    have h_τq : h.τ (h.dihedral_q hdihe) = h.dihedral_q hdihe := hy.2
    rw [h.dihedral_τ_q hdihe] at h_τq
    exact h.dihedral_p_ne_q hdihe h_τq

/-- Step 9 主結論: Fix(τ|F_0) = L. -/
theorem dihedral_fix_τ_on_F0_eq_L
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (h.dihedral_F0 hdihe).filter (fun y => h.τ y = y) = h.dihedral_L hdihe := by
  -- Both have card 54. One subset of the other.
  apply Finset.eq_of_subset_of_card_le
  · exact h.dihedral_fix_τ_on_F0_sub_L hdihe
  · rw [h.dihedral_L_card hdihe, h.dihedral_fix_τ_on_F0_card hdihe]

/-- L 上 τ は恒等. -/
theorem dihedral_τ_eq_self_of_mem_L
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) {y : V}
    (hy : y ∈ h.dihedral_L hdihe) :
    h.τ y = y := by
  rw [← h.dihedral_fix_τ_on_F0_eq_L hdihe] at hy
  rw [Finset.mem_filter] at hy
  exact hy.2

end Order22ActsOnMoore57

end Moore57
