import Moore57.Order22OnMoore57.Phase3RepTheory

/-!
# 自然言語証明 §3 Step (B): 4-cycle bound `n ≤ 59`

各長さ-11 軌道 O は高々 1 つの canonical slope `d ∈ {1, .., 5}` で内部辺を持つ
(no_four_cycle より). よって

  `Σ_{d=1}^{5} #{x : x ~ σ^d x} = 5 · 11 n ≤ |V| = 3250`

から `55 n ≤ 3250`, したがって `n ≤ 59`.

実装は組合せ的:
* `slopesAdj h x = #{d ∈ {1..5} : Γ.Adj x (σ^d x)}`.
* `slopesAdj_card_le_one`: x ごとに `|slopesAdj h x| ≤ 1` (4-cycle 引数).
* sum identity: `Σ_x |slopesAdj h x| = Σ_d |Sd|` where `Sd := {x : x ~ σ^d x}`.
* `|Sd| = h.Tk d = 11 n` for d = 1..10 (Tk_constant + Tk_one_eq_eleven_mul).
* 結論: `55n ≤ 3250`, よって `n ≤ 59`.
-/

namespace Moore57

namespace Order22ActsOnMoore57

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

variable (h : Order22ActsOnMoore57 V Γ)

/-! ## (B-1) σ^k x = x ⟺ σ x = x for k ∈ {1..10} (orbit length 11) -/

/-- σ の order は 11. -/
private theorem orderOf_σ :
    orderOf h.σ = 11 := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact orderOf_eq_prime h.σ_pow_eleven h.σ_ne_one

/-- σ x = x → σ^n x = x for any n. -/
private theorem σ_pow_fix_of_σ_fix (n : ℕ) {x : V} (hx : h.σ x = x) :
    (h.σ ^ n) x = x := by
  induction n with
  | zero => simp
  | succ m ih => rw [pow_succ, Equiv.Perm.mul_apply, hx, ih]

/-- For k ∈ {1..10}, `Fix(σ^k) = Fix(σ)`. -/
private theorem σ_pow_fix_iff {k : ℕ} (hk_pos : 1 ≤ k) (hk_lt : k < 11) (x : V) :
    (h.σ ^ k) x = x ↔ h.σ x = x := by
  classical
  have hcop : Nat.Coprime k (orderOf h.σ) := by
    rw [h.orderOf_σ]
    haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
    rw [Nat.Coprime, Nat.gcd_comm]
    apply (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime 11)).mpr
    intro hdvd
    have := Nat.le_of_dvd hk_pos hdvd
    omega
  have h_support_eq : (h.σ ^ k).support = h.σ.support :=
    Equiv.Perm.support_pow_coprime hcop
  constructor
  · intro hfix
    by_contra hne
    have hin_supp : x ∈ h.σ.support := by
      rw [Equiv.Perm.mem_support]; exact hne
    have hin_supp_k : x ∈ (h.σ ^ k).support := h_support_eq ▸ hin_supp
    rw [Equiv.Perm.mem_support] at hin_supp_k
    exact hin_supp_k hfix
  · intro hfix
    exact h.σ_pow_fix_of_σ_fix k hfix

/-- Helper: σ^b x = σ^a (σ^(b-a) x) for a ≤ b. -/
private theorem σ_pow_split {a b : ℕ} (hab : a ≤ b) (x : V) :
    (h.σ ^ b) x = (h.σ ^ a) ((h.σ ^ (b - a)) x) := by
  rw [← Equiv.Perm.mul_apply, ← pow_add]
  congr 2
  omega

/-- For x not σ-fixed and a ≠ b in {0..10}, `σ^a x ≠ σ^b x`. -/
theorem σ_pow_inj_of_not_fix {x : V} (hx : h.σ x ≠ x)
    {a b : ℕ} (ha : a < 11) (hb : b < 11) (hab : a ≠ b) :
    (h.σ ^ a) x ≠ (h.σ ^ b) x := by
  rcases lt_or_gt_of_ne hab with hab' | hab'
  · intro heq
    -- σ^a x = σ^b x ⟹ σ^(b-a) x = x
    have h_split := h.σ_pow_split hab'.le x
    rw [← heq] at h_split
    -- h_split : (h.σ^a) x = (h.σ^a) ((h.σ^(b-a)) x)
    have h_pow : (h.σ ^ (b - a)) x = x :=
      ((h.σ ^ a).injective h_split).symm
    have h_diff_pos : 1 ≤ b - a := by omega
    have h_diff_lt : b - a < 11 := by omega
    have h_fix := (h.σ_pow_fix_iff h_diff_pos h_diff_lt x).mp h_pow
    exact hx h_fix
  · intro heq
    have h_split := h.σ_pow_split hab'.le x
    rw [heq] at h_split
    have h_pow : (h.σ ^ (a - b)) x = x :=
      ((h.σ ^ b).injective h_split).symm
    have h_diff_pos : 1 ≤ a - b := by omega
    have h_diff_lt : a - b < 11 := by omega
    have h_fix := (h.σ_pow_fix_iff h_diff_pos h_diff_lt x).mp h_pow
    exact hx h_fix

/-! ## (B-2) `slopesAdj_card_le_one`: 4-cycle bound at each vertex -/

/-- 各頂点 `x` での canonical slope set `{d ∈ {1..5} : Γ.Adj x (σ^d x)}`. -/
noncomputable def slopesAdj (x : V) : Finset ℕ :=
  (Finset.Icc 1 5).filter (fun d => Γ.Adj x ((h.σ ^ d) x))

/-- σ x = x ⟹ slopesAdj は空. -/
theorem slopesAdj_empty_of_fixed {x : V} (hx : h.σ x = x) :
    h.slopesAdj x = ∅ := by
  unfold slopesAdj
  rw [Finset.filter_eq_empty_iff]
  intro d _ hadj
  have h_pow_fix : (h.σ ^ d) x = x := h.σ_pow_fix_of_σ_fix d hx
  rw [h_pow_fix] at hadj
  exact SimpleGraph.irrefl Γ hadj

/-- x が固定でないとき, slopesAdj x には高々 1 つの slope.

証明: 仮に 2 つの distinct slopes d₁ < d₂ ∈ {1..5} があるとすると, 4 頂点
x, σ^d₁ x, σ^(d₁+d₂) x, σ^d₂ x は no_four_cycle で禁止される 4-cycle を形成. -/
theorem slopesAdj_card_le_one_of_not_fixed {x : V} (hx : h.σ x ≠ x) :
    (h.slopesAdj x).card ≤ 1 := by
  classical
  by_contra h_ge
  push Not at h_ge
  -- h_ge : 1 < |slopesAdj h x|; extract two distinct slopes
  rw [Finset.one_lt_card] at h_ge
  obtain ⟨e₁, he₁, e₂, he₂, he₁₂⟩ := h_ge
  -- Set d₁ := min e₁ e₂, d₂ := max e₁ e₂
  set d₁ := min e₁ e₂ with hdef_d₁
  set d₂ := max e₁ e₂ with hdef_d₂
  have hd₁_mem : d₁ ∈ h.slopesAdj x := by
    by_cases hee : e₁ ≤ e₂
    · rw [hdef_d₁, min_eq_left hee]; exact he₁
    · push Not at hee
      rw [hdef_d₁, min_eq_right hee.le]; exact he₂
  have hd₂_mem : d₂ ∈ h.slopesAdj x := by
    by_cases hee : e₁ ≤ e₂
    · rw [hdef_d₂, max_eq_right hee]; exact he₂
    · push Not at hee
      rw [hdef_d₂, max_eq_left hee.le]; exact he₁
  have hlt : d₁ < d₂ := by
    rcases lt_or_gt_of_ne he₁₂ with hee | hee
    · rw [hdef_d₁, hdef_d₂, min_eq_left hee.le, max_eq_right hee.le]; exact hee
    · rw [hdef_d₁, hdef_d₂, min_eq_right hee.le, max_eq_left hee.le]; exact hee
  rw [show h.slopesAdj x = (Finset.Icc 1 5).filter (fun d => Γ.Adj x ((h.σ ^ d) x))
      from rfl] at hd₁_mem hd₂_mem
  rw [Finset.mem_filter, Finset.mem_Icc] at hd₁_mem hd₂_mem
  obtain ⟨⟨hd₁_lo, hd₁_hi⟩, hd₁_adj⟩ := hd₁_mem
  obtain ⟨⟨hd₂_lo, hd₂_hi⟩, hd₂_adj⟩ := hd₂_mem
  -- The 4 vertices x, σ^d₁ x, σ^(d₁+d₂) x, σ^d₂ x are all distinct
  set v₀ := x with hv₀
  set v₁ := (h.σ ^ d₁) x with hv₁
  set v₂ := (h.σ ^ (d₁ + d₂)) x with hv₂
  set v₃ := (h.σ ^ d₂) x with hv₃
  -- All 4 are distinct because exponents 0, d₁, d₁+d₂, d₂ are distinct mod 11
  have hd₁_lt_11 : d₁ < 11 := by omega
  have hd₂_lt_11 : d₂ < 11 := by omega
  have hd₁₂_sum_lt_11 : d₁ + d₂ < 11 := by omega
  have h_v₀_v₁ : v₀ ≠ v₁ := by
    have := h.σ_pow_inj_of_not_fix hx (a := 0) (b := d₁)
      (by norm_num) hd₁_lt_11 (by omega)
    simp at this
    exact this
  have h_v₀_v₂ : v₀ ≠ v₂ := by
    have := h.σ_pow_inj_of_not_fix hx (a := 0) (b := d₁ + d₂)
      (by norm_num) hd₁₂_sum_lt_11 (by omega)
    simp at this
    exact this
  have h_v₀_v₃ : v₀ ≠ v₃ := by
    have := h.σ_pow_inj_of_not_fix hx (a := 0) (b := d₂)
      (by norm_num) hd₂_lt_11 (by omega)
    simp at this
    exact this
  have h_v₁_v₂ : v₁ ≠ v₂ :=
    h.σ_pow_inj_of_not_fix hx hd₁_lt_11 hd₁₂_sum_lt_11 (by omega)
  have h_v₁_v₃ : v₁ ≠ v₃ :=
    h.σ_pow_inj_of_not_fix hx hd₁_lt_11 hd₂_lt_11 (by omega)
  have h_v₂_v₃ : v₂ ≠ v₃ :=
    h.σ_pow_inj_of_not_fix hx hd₁₂_sum_lt_11 hd₂_lt_11 (by omega)
  -- 4 edges
  have h_adj_v₀_v₁ : Γ.Adj v₀ v₁ := hd₁_adj
  have h_adj_v₀_v₃ : Γ.Adj v₀ v₃ := hd₂_adj
  -- σ^d₁ aut: x ~ σ^d₂ x ⟹ σ^d₁ x ~ σ^(d₁+d₂) x
  have h_adj_v₁_v₂ : Γ.Adj v₁ v₂ := by
    have := h.σ_pow_aut d₁ x ((h.σ ^ d₂) x)
    rw [this] at hd₂_adj
    rw [show (h.σ ^ d₁) ((h.σ ^ d₂) x) = (h.σ ^ (d₁ + d₂)) x from ?_] at hd₂_adj
    · exact hd₂_adj
    · rw [← Equiv.Perm.mul_apply, ← pow_add]
  -- σ^d₂ aut: x ~ σ^d₁ x ⟹ σ^d₂ x ~ σ^(d₂+d₁) x = σ^(d₁+d₂) x
  have h_adj_v₃_v₂ : Γ.Adj v₃ v₂ := by
    have := h.σ_pow_aut d₂ x ((h.σ ^ d₁) x)
    rw [this] at hd₁_adj
    rw [show (h.σ ^ d₂) ((h.σ ^ d₁) x) = (h.σ ^ (d₁ + d₂)) x from ?_] at hd₁_adj
    · exact hd₁_adj
    · rw [← Equiv.Perm.mul_apply, ← pow_add]
      congr 2
      omega
  -- Now apply no_four_cycle: cycle v₀ -- v₁ -- v₂ -- v₃ -- v₀
  exact h.isMoore.no_four_cycle
    h_v₀_v₁ h_v₀_v₂ h_v₀_v₃ h_v₁_v₂ h_v₁_v₃ h_v₂_v₃
    h_adj_v₀_v₁ h_adj_v₁_v₂ h_adj_v₃_v₂.symm h_adj_v₀_v₃.symm

/-- 任意の `x` で `|slopesAdj h x| ≤ 1`. -/
theorem slopesAdj_card_le_one (x : V) :
    (h.slopesAdj x).card ≤ 1 := by
  by_cases hx : h.σ x = x
  · rw [h.slopesAdj_empty_of_fixed hx]; simp
  · exact h.slopesAdj_card_le_one_of_not_fixed hx

/-! ## (B-3) Sum identity: `Σ_x |slopesAdj h x| = 55 n` -/

/-- Fubini: 各 x の slope 数の和は各 slope d ∈ {1..5} の `h.Tk d` の和に等しい. -/
theorem sum_slopesAdj_eq_sum_Tk :
    ∑ x : V, (h.slopesAdj x).card =
      ∑ d ∈ Finset.Icc 1 5, h.Tk d := by
  classical
  unfold slopesAdj
  -- LHS = Σ x, |Icc.filter (λd => Adj x (σ^d x))| = Σ x Σ d, ite ...
  -- Use Finset.card_filter then sum_comm
  have heq_x : ∀ x : V,
      ((Finset.Icc 1 5).filter (fun d => Γ.Adj x ((h.σ ^ d) x))).card =
      ∑ d ∈ Finset.Icc 1 5, (if Γ.Adj x ((h.σ ^ d) x) then 1 else 0 : ℕ) := by
    intro x
    rw [Finset.card_filter]
  simp_rw [heq_x]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intros d _
  rw [show ∑ x : V, (if Γ.Adj x ((h.σ ^ d) x) then 1 else 0 : ℕ) =
    (Finset.univ.filter (fun x : V => Γ.Adj x ((h.σ ^ d) x))).card from
    (Finset.card_filter _ _).symm]
  rfl

/-- 主等式: `Σ_x |slopesAdj h x| = 55 n`. -/
theorem sum_slopesAdj_eq_55n :
    ∑ x : V, (h.slopesAdj x).card = 55 * h.traceNumber := by
  rw [h.sum_slopesAdj_eq_sum_Tk]
  -- Σ_{d ∈ Icc 1 5} Tk d = 5 * (11 n) = 55 n
  have h_Tk : ∀ d ∈ Finset.Icc 1 5, h.Tk d = 11 * h.traceNumber := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    exact h.Tk_eq_eleven_mul_traceNumber hd.1 (by omega)
  rw [Finset.sum_congr rfl h_Tk]
  rw [Finset.sum_const]
  have hcard : (Finset.Icc 1 5).card = 5 := by decide
  rw [hcard]
  ring

/-! ## (B-4) Conclude `n ≤ 59` -/

/-- **4-cycle bound**: `traceNumber ≤ 59`. -/
theorem traceNumber_le_59 :
    h.traceNumber ≤ 59 := by
  classical
  have h_sum := h.sum_slopesAdj_eq_55n
  have h_bound : ∑ x : V, (h.slopesAdj x).card ≤ Fintype.card V := by
    calc ∑ x : V, (h.slopesAdj x).card
        ≤ ∑ _ : V, 1 := Finset.sum_le_sum (fun x _ => h.slopesAdj_card_le_one x)
      _ = Fintype.card V := by simp
  rw [h_sum, h.isMoore.card] at h_bound
  -- 55 * traceNumber ≤ 3250 ⟹ traceNumber ≤ 59
  omega

/-! ## (B-5) Phase 3 主結論 -/

/-- **Phase 3 主結論 (sorry-free)**: `traceNumber ∈ {5, 20, 35, 50}`. -/
theorem traceNumber_mem_candidates :
    h.traceNumber = 5 ∨ h.traceNumber = 20 ∨
      h.traceNumber = 35 ∨ h.traceNumber = 50 := by
  have h_form := h.traceNumber_exists_form
  have h_bound := h.traceNumber_le_59
  exact Moore57.Order22ActsOnMoore57.traceNumber.mem_candidates_of_form h_form h_bound

-- Phase 3 + Phase 4 統合 (traceNumber_eq_five) は `Phase4RepTheory.lean` に
-- 移動 (Phase 4 への依存があるため).

end Order22ActsOnMoore57

end Moore57
