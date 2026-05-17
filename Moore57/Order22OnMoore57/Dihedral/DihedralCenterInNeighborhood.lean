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

/-! ## Step 2: center は u_τ ではない (leaf) -/

theorem dihedral_center_ne_uτ
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ_fix.center ≠ h.dihedral_uτ hdihe := by
  sorry

/-! ## Step 2/3: x_0 ∈ N(u_τ) -/

theorem dihedral_adj_uτ_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Γ.Adj (h.dihedral_uτ hdihe) h.τ_fix.center := by
  sorry

/-! ## Step 3: x_0 ∉ Fix(σ) -/

theorem dihedral_center_not_σ_fixed
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.σ h.τ_fix.center ≠ h.τ_fix.center := by
  sorry

/-! ## Step 4: σ-stability of N(u_τ) と B_0 -/

theorem dihedral_σ_mem_neighborFinset_uτ_iff
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) (x : V) :
    h.σ x ∈ Γ.neighborFinset (h.dihedral_uτ hdihe) ↔
      x ∈ Γ.neighborFinset (h.dihedral_uτ hdihe) := by
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
  conv_lhs => rw [show h.dihedral_uτ hdihe = h.σ (h.dihedral_uτ hdihe)
    from (h.dihedral_σ_uτ hdihe).symm]
  exact (h.σ_aut (h.dihedral_uτ hdihe) x).symm

theorem dihedral_σ_pow_adj_uτ_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) (k : ℕ) :
    Γ.Adj (h.dihedral_uτ hdihe) ((h.σ ^ k) h.τ_fix.center) := by
  sorry

/-! ## Step 7 用: b_τ, c_τ は x_0 と非隣接 -/

theorem dihedral_bτ_ne_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_bτ hdihe ≠ h.τ_fix.center := by
  sorry

theorem dihedral_cτ_ne_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.dihedral_cτ hdihe ≠ h.τ_fix.center := by
  sorry

theorem dihedral_not_adj_bτ_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    ¬ Γ.Adj (h.dihedral_bτ hdihe) h.τ_fix.center := by
  sorry

theorem dihedral_not_adj_cτ_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    ¬ Γ.Adj (h.dihedral_cτ hdihe) h.τ_fix.center := by
  sorry

end Order22ActsOnMoore57

end Moore57
