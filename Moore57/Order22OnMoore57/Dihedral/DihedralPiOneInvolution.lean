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

/-- F_0 と F_1 の中心 x_0, σ x_0 は相異 (B_0 が length 11). -/
theorem dihedral_center_ne_σ_center
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ_fix.center ≠ h.σ h.τ_fix.center :=
  fun heq => h.dihedral_center_not_σ_fixed hdihe heq.symm

/-- F_0 ≃ F_1 (subtype-valued matching). -/
noncomputable def dihedral_m1 (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    {y // y ∈ h.dihedral_F0 hdihe} ≃ {y // y ∈ h.dihedral_F1 hdihe} :=
  h.isMoore.branchFiberMatchingEquiv
    (h.dihedral_adj_uτ_center hdihe)
    (h.dihedral_σ_pow_adj_uτ_center hdihe 1)
    (h.dihedral_center_ne_σ_center hdihe)

/-! ## Step 11: π_1 : F_0 → F_0 -/

/-- σ⁻¹ は F_1 を F_0 に送る (集合論的逆像). -/
theorem dihedral_σinv_mem_F0_of_mem_F1
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) {z : V}
    (hz : z ∈ h.dihedral_F1 hdihe) :
    h.σ⁻¹ z ∈ h.dihedral_F0 hdihe := by
  unfold dihedral_F0
  rw [mem_branchFiber]
  unfold dihedral_F1 at hz
  rw [mem_branchFiber] at hz
  refine ⟨?_, ?_⟩
  · -- σ⁻¹ z ≠ uτ. uτ ∈ Fix(σ) ⟹ σ⁻¹ uτ = uτ. もし σ⁻¹ z = uτ then z = σ uτ = uτ.
    intro heq
    apply hz.1
    have hσ_uτ : h.σ (h.dihedral_uτ hdihe) = h.dihedral_uτ hdihe := h.dihedral_σ_uτ hdihe
    have : z = h.σ (h.σ⁻¹ z) := by
      show z = (h.σ * h.σ⁻¹) z
      rw [mul_inv_cancel]; rfl
    rw [this, heq, hσ_uτ]
  · -- Γ.Adj center (σ⁻¹ z). σ aut applied to center, σ⁻¹ z: Γ.Adj σ(center) (σ(σ⁻¹ z)) = Γ.Adj (σ center) z.
    have h_aut : Γ.Adj h.τ_fix.center (h.σ⁻¹ z) ↔
        Γ.Adj (h.σ h.τ_fix.center) (h.σ (h.σ⁻¹ z)) := h.σ_aut _ _
    rw [show h.σ (h.σ⁻¹ z) = z from by
      show (h.σ * h.σ⁻¹) z = z
      rw [mul_inv_cancel]; rfl] at h_aut
    exact h_aut.mpr hz.2

/-- π_1 := σ⁻¹ ∘ m_1, viewed on subtype. -/
noncomputable def dihedral_π1 (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    {y // y ∈ h.dihedral_F0 hdihe} → {y // y ∈ h.dihedral_F0 hdihe} := fun y =>
  let z := h.dihedral_m1 hdihe y
  ⟨h.σ⁻¹ z.val, h.dihedral_σinv_mem_F0_of_mem_F1 hdihe z.property⟩

theorem dihedral_π1_val
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (y : {y // y ∈ h.dihedral_F0 hdihe}) :
    (h.dihedral_π1 hdihe y).val = h.σ⁻¹ (h.dihedral_m1 hdihe y).val := rfl

theorem dihedral_m1_val_adj
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (y : {y // y ∈ h.dihedral_F0 hdihe}) :
    Γ.Adj y.val (h.dihedral_m1 hdihe y).val :=
  h.isMoore.branchFiberMate_adj
    (h.dihedral_adj_uτ_center hdihe)
    (h.dihedral_σ_pow_adj_uτ_center hdihe 1)
    (h.dihedral_center_ne_σ_center hdihe) y

theorem dihedral_σ_mem_F1_of_mem_F0
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) {y : V}
    (hy : y ∈ h.dihedral_F0 hdihe) :
    h.σ y ∈ h.dihedral_F1 hdihe := by
  rw [← h.dihedral_σ_image_F0 hdihe]
  exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

theorem dihedral_π1_fix_iff_adj
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (y : {y // y ∈ h.dihedral_F0 hdihe}) :
    h.dihedral_π1 hdihe y = y ↔ Γ.Adj y.val (h.σ y.val) := by
  constructor
  · intro hfix
    -- π_1(y) = y ⟹ σ⁻¹(m_1 y) = y ⟹ m_1 y = σ y ⟹ y ~ σ y.
    have hval : h.σ⁻¹ (h.dihedral_m1 hdihe y).val = y.val := by
      have := congr_arg Subtype.val hfix
      exact this
    have h_m1_eq : (h.dihedral_m1 hdihe y).val = h.σ y.val := by
      have hcong := congr_arg h.σ hval
      rw [show h.σ (h.σ⁻¹ (h.dihedral_m1 hdihe y).val) = (h.dihedral_m1 hdihe y).val from by
        show (h.σ * h.σ⁻¹) (h.dihedral_m1 hdihe y).val = (h.dihedral_m1 hdihe y).val
        rw [mul_inv_cancel]; rfl] at hcong
      exact hcong
    have hadj : Γ.Adj y.val (h.dihedral_m1 hdihe y).val := h.dihedral_m1_val_adj hdihe y
    rw [h_m1_eq] at hadj
    exact hadj
  · intro hadj
    -- y ~ σ y, σ y ∈ F_1 ⟹ m_1 y = σ y ⟹ π_1 y = σ⁻¹ σ y = y.
    have h_σy_F1 : h.σ y.val ∈ h.dihedral_F1 hdihe :=
      h.dihedral_σ_mem_F1_of_mem_F0 hdihe y.property
    have h_m1_eq : h.dihedral_m1 hdihe y = ⟨h.σ y.val, h_σy_F1⟩ :=
      h.isMoore.branchFiberMate_eq_of_adj
        (h.dihedral_adj_uτ_center hdihe)
        (h.dihedral_σ_pow_adj_uτ_center hdihe 1)
        (h.dihedral_center_ne_σ_center hdihe) y ⟨h.σ y.val, h_σy_F1⟩ hadj
    apply Subtype.ext
    rw [h.dihedral_π1_val hdihe y, h_m1_eq]
    show h.σ⁻¹ (h.σ y.val) = y.val
    show (h.σ⁻¹ * h.σ) y.val = y.val
    rw [inv_mul_cancel]; rfl

/-! ## Step 12-13: τ ∘ π_1 の involution 性 (中間補題) -/

/-- 鍵となる関係式: σ(τ y) = τ(σ⁻¹ y) (dihedral から). -/
private theorem dihedral_στ_eq_τσinv_apply
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) (y : V) :
    h.σ (h.τ y) = h.τ (h.σ⁻¹ y) := by
  -- τστ = σ⁻¹ ⟹ στ = τσ⁻¹ (両側に τ を掛けて). 関数値版:
  -- σ(τ y) = τ(σ⁻¹ y).
  -- 与えられた dihedral_τσ_eq_σinv_τ_apply は τ(σ x) = σ⁻¹(τ x).
  -- ここから σ(τ y) = τ(σ⁻¹ y) を導く.
  have hkey := h.dihedral_τσ_eq_σinv_τ_apply hdihe (h.τ y)
  -- hkey : τ (σ (τ y)) = σ⁻¹ (τ (τ y)) = σ⁻¹ y
  rw [h.τ_involutive y] at hkey
  -- hkey : τ (σ (τ y)) = σ⁻¹ y
  -- Apply τ to both sides.
  have hcong := congr_arg h.τ hkey
  rw [h.τ_involutive] at hcong
  -- hcong : σ (τ y) = τ (σ⁻¹ y)
  exact hcong

/-! ## Step 14: ρ_1 involution -/

/-- π_1 (y).val = σ⁻¹ (m_1 y).val を minor helper として. -/
theorem dihedral_π1_val_eq
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (y : {y // y ∈ h.dihedral_F0 hdihe}) :
    (h.dihedral_π1 hdihe y).val = h.σ⁻¹ (h.dihedral_m1 hdihe y).val := rfl

theorem dihedral_m1_val_mem_F1
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (y : {y // y ∈ h.dihedral_F0 hdihe}) :
    (h.dihedral_m1 hdihe y).val ∈ h.dihedral_F1 hdihe :=
  (h.dihedral_m1 hdihe y).property

/-- y ~ σ (π_1 y).val (∵ π_1 y = σ⁻¹ (m_1 y) ⟹ σ (π_1 y) = m_1 y). -/
theorem dihedral_adj_y_σπ1
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (y : {y // y ∈ h.dihedral_F0 hdihe}) :
    Γ.Adj y.val (h.σ (h.dihedral_π1 hdihe y).val) := by
  rw [h.dihedral_π1_val_eq hdihe y]
  rw [show h.σ (h.σ⁻¹ (h.dihedral_m1 hdihe y).val) = (h.dihedral_m1 hdihe y).val from by
    show (h.σ * h.σ⁻¹) (h.dihedral_m1 hdihe y).val = (h.dihedral_m1 hdihe y).val
    rw [mul_inv_cancel]; rfl]
  exact h.dihedral_m1_val_adj hdihe y

/-- ρ_1 := τ ∘ π_1, viewed on subtype (τ stabilizes F_0). -/
noncomputable def dihedral_ρ1 (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    {y // y ∈ h.dihedral_F0 hdihe} → {y // y ∈ h.dihedral_F0 hdihe} := fun y =>
  let z := h.dihedral_π1 hdihe y
  ⟨h.τ z.val, h.dihedral_τ_mem_F0 hdihe z.property⟩

theorem dihedral_ρ1_val
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹)
    (y : {y // y ∈ h.dihedral_F0 hdihe}) :
    (h.dihedral_ρ1 hdihe y).val = h.τ (h.dihedral_π1 hdihe y).val := rfl

theorem dihedral_ρ1_involutive
    (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Function.Involutive (h.dihedral_ρ1 hdihe) := by
  intro y
  apply Subtype.ext
  -- Goal: (ρ_1 (ρ_1 y)).val = y.val
  -- = τ (π_1 (ρ_1 y)).val = y.val
  show h.τ (h.dihedral_π1 hdihe (h.dihedral_ρ1 hdihe y)).val = y.val
  -- 戦略: π_1 (ρ_1 y) = ⟨τ y.val, _⟩ を示す (m_1 (ρ_1 y) = ⟨σ(τ y.val), _⟩).
  have h_τy_F0 : h.τ y.val ∈ h.dihedral_F0 hdihe :=
    h.dihedral_τ_mem_F0 hdihe y.property
  have h_στy_F1 : h.σ (h.τ y.val) ∈ h.dihedral_F1 hdihe :=
    h.dihedral_σ_mem_F1_of_mem_F0 hdihe h_τy_F0
  -- 隣接: τ(π_1 y) ~ σ(τ y).
  have h_y_σπ1 : Γ.Adj y.val (h.σ (h.dihedral_π1 hdihe y).val) :=
    h.dihedral_adj_y_σπ1 hdihe y
  have h_τy_τσπ1 : Γ.Adj (h.τ y.val) (h.τ (h.σ (h.dihedral_π1 hdihe y).val)) :=
    (h.τ_aut _ _).mp h_y_σπ1
  rw [h.dihedral_τσ_eq_σinv_τ_apply hdihe] at h_τy_τσπ1
  -- h_τy_τσπ1 : Γ.Adj (τ y.val) (σ⁻¹ (τ (π_1 y).val))
  have h_στy_τπ1 :
      Γ.Adj (h.σ (h.τ y.val)) (h.σ (h.σ⁻¹ (h.τ (h.dihedral_π1 hdihe y).val))) :=
    (h.σ_aut _ _).mp h_τy_τσπ1
  rw [show h.σ (h.σ⁻¹ (h.τ (h.dihedral_π1 hdihe y).val)) =
       h.τ (h.dihedral_π1 hdihe y).val from by
    show (h.σ * h.σ⁻¹) (h.τ (h.dihedral_π1 hdihe y).val) =
         h.τ (h.dihedral_π1 hdihe y).val
    rw [mul_inv_cancel]; rfl] at h_στy_τπ1
  -- h_στy_τπ1 : Γ.Adj (σ(τ y.val)) (τ(π_1 y).val)
  -- (ρ_1 y).val = τ(π_1 y).val by definition, so:
  have h_adj : Γ.Adj (h.dihedral_ρ1 hdihe y).val (h.σ (h.τ y.val)) :=
    h_στy_τπ1.symm
  -- m_1 (ρ_1 y) = ⟨σ(τ y.val), h_στy_F1⟩.
  have h_m1_ρ1y :
      h.dihedral_m1 hdihe (h.dihedral_ρ1 hdihe y) =
        ⟨h.σ (h.τ y.val), h_στy_F1⟩ :=
    h.isMoore.branchFiberMate_eq_of_adj
      (h.dihedral_adj_uτ_center hdihe)
      (h.dihedral_σ_pow_adj_uτ_center hdihe 1)
      (h.dihedral_center_ne_σ_center hdihe)
      (h.dihedral_ρ1 hdihe y) ⟨h.σ (h.τ y.val), h_στy_F1⟩ h_adj
  -- π_1 (ρ_1 y).val = σ⁻¹ (m_1 (ρ_1 y)).val = σ⁻¹ (σ (τ y.val)) = τ y.val.
  rw [h.dihedral_π1_val_eq hdihe (h.dihedral_ρ1 hdihe y), h_m1_ρ1y]
  show h.τ (h.σ⁻¹ (h.σ (h.τ y.val))) = y.val
  rw [show h.σ⁻¹ (h.σ (h.τ y.val)) = h.τ y.val from by
    show (h.σ⁻¹ * h.σ) (h.τ y.val) = h.τ y.val
    rw [inv_mul_cancel]; rfl]
  exact h.τ_involutive y.val

/-- ρ_1 を `Equiv.Perm {y // y ∈ F_0}` として持ち上げる. -/
noncomputable def dihedral_ρ1Perm (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    Equiv.Perm {y // y ∈ h.dihedral_F0 hdihe} where
  toFun := h.dihedral_ρ1 hdihe
  invFun := h.dihedral_ρ1 hdihe
  left_inv := h.dihedral_ρ1_involutive hdihe
  right_inv := h.dihedral_ρ1_involutive hdihe

end Order22ActsOnMoore57

end Moore57
