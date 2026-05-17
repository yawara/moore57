import Moore57.Order22OnMoore57.Dihedral.DihedralLDefinition

/-!
# Steps 10-14 (Dihedral): π_1 と ρ_1 の involution 性

* (Step 10) `m_1 : F_0 ≃ F_1` — branchFiber matching equivalence.
* (Step 11) `π_1 : F_0 → F_0` via `σ⁻¹ ∘ m_1`. y ∈ F_0 で `π_1(y) = y ↔ y ~ σ y`.
* (Step 12) `τ ∘ π_1 = π_{-1} ∘ τ` on F_0.
* (Step 13) `π_{-1} = π_1⁻¹`.
* (Step 14) `ρ_1 := τ ∘ π_1` is involution on F_0.

サブタイプ `{y // y ∈ F_0}` 上の関数として定義.
-/

namespace Moore57

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable (h : Order22ActsOnMoore57 V Γ)

/-! ## Step 10: m_1 matching -/

/-- F_0 ≃ F_1 (subtype-valued matching). -/
noncomputable def dihedral_m1 (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    {y // y ∈ h.dihedral_F0 hdihe} ≃ {y // y ∈ h.dihedral_F1 hdihe} := by
  sorry

/-! ## Step 11: π_1 : F_0 → F_0 -/

/-- π_1 := σ⁻¹ ∘ m_1, viewed on subtype. -/
noncomputable def dihedral_π1 (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    {y // y ∈ h.dihedral_F0 hdihe} → {y // y ∈ h.dihedral_F0 hdihe} := by
  sorry

theorem dihedral_π1_fix_iff_adj
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (y : {y // y ∈ h.dihedral_F0 hdihe}) :
    h.dihedral_π1 hdihe y = y ↔ Γ.Adj y.val (h.σ y.val) := by
  sorry

/-! ## Step 12-13: π_{-1} と equivariance -/

/-- F_{-1} := branchFiber Γ u_τ (σ⁻¹ x_0). -/
noncomputable def dihedral_Fminus1 (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) : Finset V :=
  branchFiber Γ (h.dihedral_uτ hdihe) (h.σ⁻¹ h.τ_fix.center)

/-- m_{-1} : F_0 ≃ F_{-1}. -/
noncomputable def dihedral_mMinus1 (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    {y // y ∈ h.dihedral_F0 hdihe} ≃ {y // y ∈ h.dihedral_Fminus1 hdihe} := by
  sorry

/-- π_{-1} := σ ∘ m_{-1}, on subtype. -/
noncomputable def dihedral_πMinus1 (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    {y // y ∈ h.dihedral_F0 hdihe} → {y // y ∈ h.dihedral_F0 hdihe} := by
  sorry

/-! ## Step 14: ρ_1 involution -/

/-- ρ_1 := τ ∘ π_1, viewed on subtype (τ stabilizes F_0). -/
noncomputable def dihedral_ρ1 (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    {y // y ∈ h.dihedral_F0 hdihe} → {y // y ∈ h.dihedral_F0 hdihe} := by
  sorry

theorem dihedral_ρ1_involutive
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Function.Involutive (h.dihedral_ρ1 hdihe) := by
  sorry

/-- ρ_1 を `Equiv.Perm {y // y ∈ F_0}` として持ち上げる. -/
noncomputable def dihedral_ρ1Perm (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Equiv.Perm {y // y ∈ h.dihedral_F0 hdihe} where
  toFun := h.dihedral_ρ1 hdihe
  invFun := h.dihedral_ρ1 hdihe
  left_inv := h.dihedral_ρ1_involutive hdihe
  right_inv := h.dihedral_ρ1_involutive hdihe

end Order22ActsOnMoore57

end Moore57
