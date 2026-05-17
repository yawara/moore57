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
  sorry

/-- Fix(τ|F_0) = L: F_0 内の τ-不動点はちょうど L. -/
theorem dihedral_fix_τ_on_F0_eq_L
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    (h.dihedral_F0 hdihe).filter (fun y => h.τ y = y) = h.dihedral_L hdihe := by
  sorry

/-- L 上 τ は恒等. -/
theorem dihedral_τ_eq_self_of_mem_L
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) {y : V}
    (hy : y ∈ h.dihedral_L hdihe) :
    h.τ y = y := by
  sorry

theorem dihedral_L_subset_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_L hdihe ⊆ h.dihedral_F0 hdihe := by
  unfold dihedral_L
  exact Finset.sdiff_subset

end Order22ActsOnMoore57

end Moore57
