import Moore57.Order22OnMoore57.Action

/-!
# 自然言語証明 §1: 固定 5-cycle と N(u) の基本構造

`Order22ActsOnMoore57` から外部入力 `σ_fix : C5FixedData Γ σ` の構造を取り出し,
自然言語証明 §1 で使う基本事実を整える.

主な内容:
* 5 頂点 `u, a, b, c, d` の命名アクセス (構造体 `h.σ_fix.v` の薄い別名).
* 10 個の相異対と σ-不変性.
* 循環隣接 `u-a-b-c-d-u` と対角の非隣接.
* `a, d ∈ N(u)`, `u, b, c ∉ N(u)`.
* σ は N(u) を保ち, N(u) 内での σ-固定点は丁度 `{a, d}`.

下層 (Foundations / Moore57Graph) との関係:
* `branchFiber Γ u b = N(b) ∖ {u}` と `branchFiber_card = 56`, fiber matching
  (`branchFiberMatchingEquiv`) は既に `Moore57Graph/BranchFiber/Matching.lean`
  に存在. 本ファイルは作用 (σ) を絡める時にこれらを参照する.
-/

namespace Moore57

namespace Order22ActsOnMoore57

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ## 5 fixed-cycle accessors -/

/-- 自然言語証明の `u` (固定 5-cycle 上の基点). -/
def u (h : Order22ActsOnMoore57 V Γ) : V := h.σ_fix.v 0
/-- 自然言語証明の `a` (cycle 上 u の片隣). -/
def a (h : Order22ActsOnMoore57 V Γ) : V := h.σ_fix.v 1
/-- 自然言語証明の `b` (cycle 上 a の隣). -/
def b (h : Order22ActsOnMoore57 V Γ) : V := h.σ_fix.v 2
/-- 自然言語証明の `c` (cycle 上 b の隣). -/
def c (h : Order22ActsOnMoore57 V Γ) : V := h.σ_fix.v 3
/-- 自然言語証明の `d` (cycle 上 u の他方隣). -/
def d (h : Order22ActsOnMoore57 V Γ) : V := h.σ_fix.v 4

variable (h : Order22ActsOnMoore57 V Γ)

/-! ## 相異対 (10 個) -/

private theorem v_ne_v_of_ne {i j : Fin 5} (hij : i ≠ j) :
    h.σ_fix.v i ≠ h.σ_fix.v j := fun heq =>
  hij (h.σ_fix.v_injective heq)

theorem u_ne_a : h.u ≠ h.a := h.v_ne_v_of_ne (by decide)
theorem u_ne_b : h.u ≠ h.b := h.v_ne_v_of_ne (by decide)
theorem u_ne_c : h.u ≠ h.c := h.v_ne_v_of_ne (by decide)
theorem u_ne_d : h.u ≠ h.d := h.v_ne_v_of_ne (by decide)
theorem a_ne_b : h.a ≠ h.b := h.v_ne_v_of_ne (by decide)
theorem a_ne_c : h.a ≠ h.c := h.v_ne_v_of_ne (by decide)
theorem a_ne_d : h.a ≠ h.d := h.v_ne_v_of_ne (by decide)
theorem b_ne_c : h.b ≠ h.c := h.v_ne_v_of_ne (by decide)
theorem b_ne_d : h.b ≠ h.d := h.v_ne_v_of_ne (by decide)
theorem c_ne_d : h.c ≠ h.d := h.v_ne_v_of_ne (by decide)

/-! ## σ-不変性 -/

@[simp] theorem σ_u_eq : h.σ h.u = h.u := h.σ_fix.v_fixed 0
@[simp] theorem σ_a_eq : h.σ h.a = h.a := h.σ_fix.v_fixed 1
@[simp] theorem σ_b_eq : h.σ h.b = h.b := h.σ_fix.v_fixed 2
@[simp] theorem σ_c_eq : h.σ h.c = h.c := h.σ_fix.v_fixed 3
@[simp] theorem σ_d_eq : h.σ h.d = h.d := h.σ_fix.v_fixed 4

/-! ## 循環隣接 (u-a-b-c-d-u) -/

theorem adj_u_a : Γ.Adj h.u h.a := h.σ_fix.cycle_adj 0
theorem adj_a_b : Γ.Adj h.a h.b := h.σ_fix.cycle_adj 1
theorem adj_b_c : Γ.Adj h.b h.c := h.σ_fix.cycle_adj 2
theorem adj_c_d : Γ.Adj h.c h.d := h.σ_fix.cycle_adj 3
theorem adj_d_u : Γ.Adj h.d h.u := h.σ_fix.cycle_adj 4

/-! ## 対角の非隣接 -/

private theorem not_adj_v_v {i j : Fin 5}
    (hij1 : j ≠ i + 1) (hij2 : j ≠ i - 1) :
    ¬ Γ.Adj (h.σ_fix.v i) (h.σ_fix.v j) := fun hadj =>
  (h.σ_fix.cycle_only i j hadj).elim hij1 hij2

theorem not_adj_u_b : ¬ Γ.Adj h.u h.b := h.not_adj_v_v (by decide) (by decide)
theorem not_adj_u_c : ¬ Γ.Adj h.u h.c := h.not_adj_v_v (by decide) (by decide)
theorem not_adj_a_c : ¬ Γ.Adj h.a h.c := h.not_adj_v_v (by decide) (by decide)
theorem not_adj_a_d : ¬ Γ.Adj h.a h.d := h.not_adj_v_v (by decide) (by decide)
theorem not_adj_b_d : ¬ Γ.Adj h.b h.d := h.not_adj_v_v (by decide) (by decide)

/-! ## N(u) との関係: a, d は含まれ, u, b, c は含まれない -/

theorem a_mem_neighborFinset_u : h.a ∈ Γ.neighborFinset h.u := by
  rw [SimpleGraph.mem_neighborFinset]
  exact h.adj_u_a

theorem d_mem_neighborFinset_u : h.d ∈ Γ.neighborFinset h.u := by
  rw [SimpleGraph.mem_neighborFinset]
  exact h.adj_d_u.symm

theorem u_not_mem_neighborFinset_u : h.u ∉ Γ.neighborFinset h.u := by
  simp

theorem b_not_mem_neighborFinset_u : h.b ∉ Γ.neighborFinset h.u := by
  rw [SimpleGraph.mem_neighborFinset]
  exact h.not_adj_u_b

theorem c_not_mem_neighborFinset_u : h.c ∉ Γ.neighborFinset h.u := by
  rw [SimpleGraph.mem_neighborFinset]
  exact h.not_adj_u_c

/-! ## σ は N(u) を保ち, 固定点は {a, d} -/

/-- σ は N(u) 上の置換 (`u` を固定し, 隣接を保つ). -/
theorem σ_mem_neighborFinset_u_iff (x : V) :
    h.σ x ∈ Γ.neighborFinset h.u ↔ x ∈ Γ.neighborFinset h.u := by
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
  conv_lhs => rw [show h.u = h.σ h.u from h.σ_u_eq.symm]
  exact (h.σ_aut h.u x).symm

/-- dihedral case 関係式: `τστ⁻¹ = σ⁻¹` から `τσ = σ⁻¹τ`. -/
theorem dihedral_τσ_eq_σinv_τ (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) :
    h.τ * h.σ = h.σ⁻¹ * h.τ := by
  have : h.τ * h.σ * h.τ * h.τ = h.σ⁻¹ * h.τ := by rw [hdihe]
  rw [mul_assoc (h.τ * h.σ), show h.τ * h.τ = 1 from by
    rw [show h.τ * h.τ = h.τ ^ 2 from (pow_two _).symm, h.τ_pow_two], mul_one] at this
  exact this

/-- dihedral case の頂点単位の関係式: `τ (σ x) = σ⁻¹ (τ x)`. -/
theorem dihedral_τσ_eq_σinv_τ_apply (hdihe : h.τ * h.σ * h.τ = h.σ⁻¹) (x : V) :
    h.τ (h.σ x) = h.σ⁻¹ (h.τ x) := by
  have heq : h.τ * h.σ = h.σ⁻¹ * h.τ := h.dihedral_τσ_eq_σinv_τ hdihe
  have := congrArg (· x) heq
  simpa [Equiv.Perm.mul_apply] using this

/-- 両ケース共通: τ は Fix(σ) を保つ.

cyclic case では `(στ) x = (τσ) x ⟹ σ (τ x) = τ (σ x) = τ x`.
dihedral case では `τ (σ x) = σ⁻¹ (τ x), σ x = x ⟹ τ x = σ⁻¹ (τ x) ⟹ σ (τ x) = τ x`. -/
theorem τ_preserves_σ_fix {x : V} (hx : h.σ x = x) :
    h.σ (h.τ x) = h.τ x := by
  rcases h.στ_relation with hcomm | hdihe
  · -- cyclic: σ * τ = τ * σ
    have := congrArg (· x) hcomm
    simp only [Equiv.Perm.mul_apply, hx] at this
    exact this
  · -- dihedral: τ * σ * τ = σ⁻¹
    have hτσ := h.dihedral_τσ_eq_σinv_τ_apply hdihe x
    -- hτσ : τ (σ x) = σ⁻¹ (τ x); hx : σ x = x
    rw [hx] at hτσ
    -- hτσ : τ x = σ⁻¹ (τ x)
    have hcancel : h.σ (h.σ⁻¹ (h.τ x)) = h.τ x := by
      show (h.σ * h.σ⁻¹) (h.τ x) = h.τ x
      rw [mul_inv_cancel]; rfl
    have := congrArg h.σ hτσ
    rwa [hcancel] at this

/-- N(u) における σ の固定点は丁度 `{a, d}`. -/
theorem σ_fixed_in_neighborFinset_u_iff_aOrD {x : V}
    (hx : x ∈ Γ.neighborFinset h.u) :
    h.σ x = x ↔ (x = h.a ∨ x = h.d) := by
  constructor
  · intro hfix
    obtain ⟨i, hi⟩ := h.σ_fix.span x hfix
    -- hi : x = h.σ_fix.v i
    have hadj : Γ.Adj (h.σ_fix.v 0) (h.σ_fix.v i) := by
      have hadj0 : Γ.Adj h.u x := by
        rwa [SimpleGraph.mem_neighborFinset] at hx
      rw [hi] at hadj0
      exact hadj0
    rcases h.σ_fix.cycle_only 0 i hadj with hi1 | hi4
    · left
      rw [hi, hi1]
      rfl
    · right
      rw [hi, hi4]
      rfl
  · rintro (rfl | rfl)
    · exact h.σ_a_eq
    · exact h.σ_d_eq

end Order22ActsOnMoore57

end Moore57
