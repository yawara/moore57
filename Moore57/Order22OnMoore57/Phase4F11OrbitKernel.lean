import Moore57.Order22OnMoore57.Phase4F11Module
import Moore57.Foundations.LinearAlgebra.JordanMonotonicity
import Moore57.Foundations.LinearAlgebra.GeomSeriesCharP
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Phase 4 Step 3: dim ker((σ-I)^j on V_F_11) = 5 + 295 j

orbital decomposition を経由せず, 以下 3 つの数値計算で結論:

1. `(σ - I)^{11} = 0` (Frobenius binomial over F_11).
2. `dim ker(σ - I) on V_F_11 = 300` (= #σ-orbits).
3. `dim range((σ - I)^{10}) on V_F_11 = 295` (= #free orbits).

組み合わせ + Jordan 単調性 (`finrank_ker_pow_concave`) で:
`dim ker((σ-I)^j on V_F_11) = 5 + 295 j` for `1 ≤ j ≤ 11`.

## Step 3 構成

* `permMatrixF11_sub_one_pow_eleven_eq_zero`: (σ - I)^{11} = 0 over F_11 (本ファイル).
* `finrank_ker_permMatrixF11_sub_one`: dim ker(σ - I) = #orbits = 300 (次段階).
* `finrank_range_permMatrixF11_sub_one_pow_ten`: dim range = 295 (次段階).
* `finrank_ker_T_F11_pow`: 主 dim 公式 (組み合わせ).
-/

namespace Moore57

namespace Order22ActsOnMoore57

open LinearMap Submodule Module

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ## Step 3.1: Frobenius binomial で `(σ - I)^{11} = 0` -/

/-- F_11 上の matrix ring に CharP 11. -/
instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- `Order22ActsOnMoore57` から `Nonempty V` を導出. -/
private theorem nonempty_V_of_action (h : Order22ActsOnMoore57 V Γ) : Nonempty V :=
  ⟨h.σ_fix.v 0⟩

/-- **Frobenius binomial 帰結**: `(permMatrixF11 σ - 1)^{11} = 0` over F_11.

証明: char 11 の commute element に対する Frobenius:
`(σ - 1)^{11} = σ^{11} - 1^{11} = σ^{11} - 1 = 1 - 1 = 0` (∵ σ^{11} = 1). -/
theorem permMatrixF11_sub_one_pow_eleven_eq_zero (h : Order22ActsOnMoore57 V Γ) :
    ((permMatrixF11 h.σ) - 1) ^ 11 = (0 : Matrix V V (ZMod 11)) := by
  haveI : Nonempty V := h.nonempty_V_of_action
  haveI : CharP (Matrix V V (ZMod 11)) 11 := Matrix.charP 11
  have h_comm : Commute (permMatrixF11 h.σ) (1 : Matrix V V (ZMod 11)) :=
    Commute.one_right _
  have h_eq : ((permMatrixF11 h.σ) - 1)^11 =
      (permMatrixF11 h.σ)^11 - (1 : Matrix V V (ZMod 11))^11 :=
    sub_pow_char_of_commute (p := 11) (R := Matrix V V (ZMod 11)) h_comm
  rw [h_eq, h.permMatrixF11_σ_pow_eleven, one_pow]
  simp

/-- toLin' 版: `((permMatrixF11 σ - 1).toLin')^{11} = 0`. -/
theorem permMatrixF11_sub_one_toLin'_pow_eleven_eq_zero
    (h : Order22ActsOnMoore57 V Γ) :
    (((permMatrixF11 h.σ) - 1 : Matrix V V (ZMod 11)).toLin' :
        (V → ZMod 11) →ₗ[ZMod 11] (V → ZMod 11)) ^ 11 = 0 := by
  rw [← Matrix.toLin'_pow, h.permMatrixF11_sub_one_pow_eleven_eq_zero]
  ext v
  simp

/-! ## Step 3.2: dim ker(σ - I) = 300 (= #σ-orbits)

`Equiv.Perm.SameCycle.setoid σ` を使い orbit Quotient と σ-fixed function を
linearly equivalence 付けて Module.finrank_pi で dim を出す.

詳細実装は ~150 行. ここでは結論のみ sorry. -/

/-- T := (permMatrixF11 σ - 1).toLin' (略記).
`@[irreducible]` で whnf 暴走を抑制. -/
@[irreducible]
noncomputable def T_F11 (h : Order22ActsOnMoore57 V Γ) :
    (V → ZMod 11) →ₗ[ZMod 11] (V → ZMod 11) :=
  ((permMatrixF11 h.σ) - 1).toLin'

theorem T_F11_def (h : Order22ActsOnMoore57 V Γ) :
    T_F11 h = ((permMatrixF11 h.σ) - 1).toLin' := by
  unfold T_F11; rfl

/-- `(T_F11 h)^11 = 0`. `permMatrixF11_sub_one_toLin'_pow_eleven_eq_zero` の
`T_F11` バージョン. -/
theorem T_F11_pow_eleven_eq_zero (h : Order22ActsOnMoore57 V Γ) :
    (T_F11 h) ^ 11 = 0 := by
  rw [T_F11_def]
  exact h.permMatrixF11_sub_one_toLin'_pow_eleven_eq_zero

/-- F_11 kernel dim sequence (opaque wrapper to suppress unfolding). -/
@[irreducible]
noncomputable def kerDimSeq (h : Order22ActsOnMoore57 V Γ) (k : ℕ) : ℕ :=
  Module.finrank (ZMod 11) (LinearMap.ker ((T_F11 h)^k))

theorem kerDimSeq_eq (h : Order22ActsOnMoore57 V Γ) (k : ℕ) :
    kerDimSeq h k = Module.finrank (ZMod 11) (LinearMap.ker ((T_F11 h)^k)) := by
  unfold kerDimSeq; rfl

/-! ### Step 3.2 用 helper: orbit count via cycleType -/

/-- `|Fix(σ)| = 5` (`Function.fixedPoints` 形). -/
private theorem card_fixedPoints_σ_eq_five (h : Order22ActsOnMoore57 V Γ) :
    Fintype.card (Function.fixedPoints h.σ) = 5 := by
  classical
  -- Function.fixedPoints σ = {v : σ v = v} ↔ image of h.σ_fix.v.
  have h_card_eq : Fintype.card (Function.fixedPoints (h.σ : V → V)) =
      Fintype.card (Set.range h.σ_fix.v) := by
    apply Fintype.card_congr
    refine Equiv.setCongr ?_
    ext v
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, Set.mem_range]
    exact ⟨fun hv => (h.σ_fix.span v hv).imp (fun _ h => h.symm),
           fun ⟨i, hi⟩ => hi ▸ h.σ_fix.v_fixed i⟩
  rw [h_card_eq, Set.card_range_of_injective h.σ_fix.v_injective]
  simp

/-- σ has order 11 (prime). -/
private theorem orderOf_σ_eq_11 (h : Order22ActsOnMoore57 V Γ) :
    orderOf h.σ = 11 := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact orderOf_eq_prime h.σ_pow_eleven h.σ_ne_one

/-- σ.cycleType の全 entry が 11. -/
private theorem cycleType_σ_eq_replicate (h : Order22ActsOnMoore57 V Γ) :
    h.σ.cycleType = Multiset.replicate h.σ.cycleType.card 11 := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h_prime : (orderOf h.σ).Prime := by
    rw [orderOf_σ_eq_11 h]; exact (Fact.out : Nat.Prime 11)
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order h_prime
  -- hn : h.σ.cycleType = Multiset.replicate (n+1) (orderOf h.σ)
  have h_orderOf : orderOf h.σ = 11 := orderOf_σ_eq_11 h
  rw [h_orderOf] at hn
  -- hn : h.σ.cycleType = Multiset.replicate (n+1) 11
  have h_card : h.σ.cycleType.card = n + 1 := by
    rw [hn, Multiset.card_replicate]
  conv_lhs => rw [hn]
  rw [h_card]

/-- σ.cycleType.card = 295. -/
private theorem cycleType_σ_card_eq_295 (h : Order22ActsOnMoore57 V Γ) :
    h.σ.cycleType.card = 295 := by
  have h_card_fix := card_fixedPoints_σ_eq_five h
  have h_card_V : Fintype.card V = 3250 := h.isMoore.card
  have h_repl := cycleType_σ_eq_replicate h
  have h_sum : h.σ.cycleType.sum = 11 * h.σ.cycleType.card := by
    have h1 : h.σ.cycleType.sum = (h.σ.cycleType.card) • 11 := by
      conv_lhs => rw [h_repl]
      exact Multiset.sum_replicate _ _
    rw [h1, smul_eq_mul, Nat.mul_comm]
  have h_fix := Equiv.Perm.card_fixedPoints h.σ
  rw [h_card_fix, h_card_V, h_sum] at h_fix
  omega

/-! ### `Quotient (SameCycle.setoid σ) ≃ Fix σ ⊕ cycleFactorsFinset σ`

各 σ-orbit は (a) σ-fixed point の singleton か (b) cycle factor の support と一致.
explicit Equiv を構築.

**注意**: `DecidableRel σ.SameCycle` は explicit に渡さず, Mathlib の
`Equiv.Perm.instDecidableRelSameCycle` ([DecidableEq V] [Fintype V] から) に頼る.
これにより `cycleOf_mem_cycleFactorsFinset_iff` 等の lemma との instance 不整合を
回避. -/

/-- `σ v ≠ v ⟹ σ.cycleOf v ∈ σ.cycleFactorsFinset`. -/
private theorem mem_factors_of_cycleOf {σ : Equiv.Perm V}
    {v : V} (hv : σ v ≠ v) :
    σ.cycleOf v ∈ σ.cycleFactorsFinset :=
  Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hv)

/-- Forward map. -/
private noncomputable def toFixOrCycleAux (σ : Equiv.Perm V) (v : V) :
    {y : V // y ∈ Function.fixedPoints σ} ⊕
      {p : Equiv.Perm V // p ∈ σ.cycleFactorsFinset} :=
  if hv : σ v = v then Sum.inl ⟨v, hv⟩
  else Sum.inr ⟨σ.cycleOf v, mem_factors_of_cycleOf hv⟩

private theorem toFixOrCycleAux_eq_inl {σ : Equiv.Perm V}
    {v : V} (hv : σ v = v) :
    toFixOrCycleAux σ v = Sum.inl ⟨v, hv⟩ := by
  unfold toFixOrCycleAux; rw [dif_pos hv]

private theorem toFixOrCycleAux_eq_inr {σ : Equiv.Perm V}
    {v : V} (hv : σ v ≠ v) :
    toFixOrCycleAux σ v =
      Sum.inr ⟨σ.cycleOf v, mem_factors_of_cycleOf hv⟩ := by
  unfold toFixOrCycleAux; rw [dif_neg hv]

/-- Representative of a cycle factor. -/
private noncomputable def cycleRepAux (σ : Equiv.Perm V)
    (c : {p : Equiv.Perm V // p ∈ σ.cycleFactorsFinset}) : V :=
  ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.prop).1.nonempty_support).choose

private theorem cycleRepAux_mem (σ : Equiv.Perm V)
    (c : {p : Equiv.Perm V // p ∈ σ.cycleFactorsFinset}) :
    cycleRepAux σ c ∈ (c : Equiv.Perm V).support :=
  ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.prop).1.nonempty_support).choose_spec

private theorem toFixOrCycleAux_well_def (σ : Equiv.Perm V)
    {a b : V} (hab : σ.SameCycle a b) :
    toFixOrCycleAux σ a = toFixOrCycleAux σ b := by
  by_cases ha : σ a = a
  · have hb : σ b = b := (Equiv.Perm.SameCycle.apply_eq_self_iff hab).mp ha
    have hab_eq : a = b := Equiv.Perm.SameCycle.eq_of_left hab ha
    rw [toFixOrCycleAux_eq_inl ha, toFixOrCycleAux_eq_inl hb]
    subst hab_eq; rfl
  · have hb : σ b ≠ b := fun hb_fix =>
      ha ((Equiv.Perm.SameCycle.apply_eq_self_iff hab).mpr hb_fix)
    rw [toFixOrCycleAux_eq_inr ha, toFixOrCycleAux_eq_inr hb]
    refine congrArg Sum.inr (Subtype.ext ?_)
    exact Equiv.Perm.SameCycle.cycleOf_eq hab

private noncomputable def quotientSameCycleEquiv (σ : Equiv.Perm V) :
    Quotient (Equiv.Perm.SameCycle.setoid σ) ≃
      {y : V // y ∈ Function.fixedPoints σ} ⊕
        {p : Equiv.Perm V // p ∈ σ.cycleFactorsFinset} where
  toFun := Quotient.lift (toFixOrCycleAux σ) (fun _ _ => toFixOrCycleAux_well_def σ)
  invFun := Sum.elim
    (fun v => Quotient.mk (Equiv.Perm.SameCycle.setoid σ) v.1)
    (fun c => Quotient.mk (Equiv.Perm.SameCycle.setoid σ) (cycleRepAux σ c))
  left_inv := by
    intro q
    induction q using Quotient.ind with
    | _ v =>
      show Sum.elim
          (fun (v : {y // y ∈ Function.fixedPoints σ}) =>
            Quotient.mk (Equiv.Perm.SameCycle.setoid σ) v.1)
          (fun c => Quotient.mk (Equiv.Perm.SameCycle.setoid σ) (cycleRepAux σ c))
          (toFixOrCycleAux σ v) = Quotient.mk (Equiv.Perm.SameCycle.setoid σ) v
      by_cases hv : σ v = v
      · rw [toFixOrCycleAux_eq_inl hv, Sum.elim_inl]
      · rw [toFixOrCycleAux_eq_inr hv, Sum.elim_inr]
        apply Quotient.sound
        have h_mem :=
          cycleRepAux_mem σ ⟨σ.cycleOf v, mem_factors_of_cycleOf hv⟩
        change cycleRepAux σ _ ∈ (σ.cycleOf v).support at h_mem
        rw [Equiv.Perm.mem_support_cycleOf_iff] at h_mem
        exact h_mem.1.symm
  right_inv := by
    rintro (⟨v, hv⟩ | ⟨c, hc⟩)
    · show Quotient.lift (toFixOrCycleAux σ) _
          (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) v) = Sum.inl ⟨v, hv⟩
      rw [Quotient.lift_mk, toFixOrCycleAux_eq_inl hv]
    · show Quotient.lift (toFixOrCycleAux σ) _
          (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) (cycleRepAux σ ⟨c, hc⟩)) =
            Sum.inr ⟨c, hc⟩
      rw [Quotient.lift_mk]
      have h_in_supp : cycleRepAux σ ⟨c, hc⟩ ∈ c.support := cycleRepAux_mem σ ⟨c, hc⟩
      have hv_in_σ_supp : cycleRepAux σ ⟨c, hc⟩ ∈ σ.support :=
        Equiv.Perm.mem_cycleFactorsFinset_support_le hc h_in_supp
      have hv_not_fix : σ (cycleRepAux σ ⟨c, hc⟩) ≠ cycleRepAux σ ⟨c, hc⟩ :=
        Equiv.Perm.mem_support.mp hv_in_σ_supp
      rw [toFixOrCycleAux_eq_inr hv_not_fix]
      refine congrArg Sum.inr (Subtype.ext ?_)
      exact (Equiv.Perm.cycle_is_cycleOf h_in_supp hc).symm

/-- `|Quotient (SameCycle.setoid σ)| = |Fix σ| + |cycleFactorsFinset σ|`. -/
private theorem card_quotient_sameCycle_eq (h : Order22ActsOnMoore57 V Γ) :
    @Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid h.σ))
        (@Quotient.fintype _ _ _ (fun _ _ => Classical.dec _)) =
      Fintype.card (Function.fixedPoints h.σ) + h.σ.cycleFactorsFinset.card := by
  classical
  haveI : Fintype (Quotient (Equiv.Perm.SameCycle.setoid h.σ)) :=
    Quotient.fintype _
  have h_card : Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid h.σ)) =
      Fintype.card (Function.fixedPoints h.σ) + h.σ.cycleFactorsFinset.card := by
    rw [Fintype.card_congr (quotientSameCycleEquiv h.σ), Fintype.card_sum,
      Fintype.card_coe]
  convert h_card using 2

/-- `Fintype.card (Quotient (SameCycle.setoid h.σ)) = 300`. -/
private theorem card_quotient_sameCycle_eq_300 (h : Order22ActsOnMoore57 V Γ) :
    @Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid h.σ))
        (@Quotient.fintype _ _ _ (fun _ _ => Classical.dec _)) = 300 := by
  rw [card_quotient_sameCycle_eq, card_fixedPoints_σ_eq_five]
  -- Bridge cycleFactorsFinset.card to cycleType.card
  have h_eq : h.σ.cycleFactorsFinset.card = h.σ.cycleType.card := by
    rw [Equiv.Perm.cycleType_def]
    simp [Multiset.card_map]
  rw [h_eq, cycleType_σ_card_eq_295 h]

/-- `permMatrixF11 σ.mulVec f = f ∘ σ.symm`. -/
private theorem permMatrixF11_mulVec_eq (σ : Equiv.Perm V) (f : V → ZMod 11) :
    (permMatrixF11 σ).mulVec f = f ∘ σ.symm := by
  -- permMatrixF11 σ = σ.symm.toPEquiv.toMatrix = (σ⁻¹).permMatrix (ZMod 11)
  show (σ.symm.toPEquiv.toMatrix : Matrix V V (ZMod 11)).mulVec f = f ∘ σ.symm
  have h_eq : (σ.symm.toPEquiv.toMatrix : Matrix V V (ZMod 11)) =
      σ⁻¹.permMatrix (ZMod 11) := rfl
  rw [h_eq, Matrix.permMatrix_mulVec]
  rfl

/-- T_F11 のカーネル条件: `f ∈ ker T_F11 ↔ ∀ v, f (σ v) = f v`. -/
private theorem mem_ker_T_F11_iff (h : Order22ActsOnMoore57 V Γ) (f : V → ZMod 11) :
    f ∈ LinearMap.ker (T_F11 h) ↔ ∀ v, f (h.σ v) = f v := by
  rw [LinearMap.mem_ker, T_F11_def]
  rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
      permMatrixF11_mulVec_eq]
  -- Goal: f ∘ σ.symm - f = 0 ↔ ∀ v, f (σ v) = f v
  rw [sub_eq_zero, funext_iff]
  constructor
  · intro hσ v
    have := hσ (h.σ v)
    simp only [Function.comp_apply, Equiv.symm_apply_apply] at this
    exact this.symm
  · intro hσ v
    show (f ∘ h.σ.symm) v = f v
    simp only [Function.comp_apply]
    have := hσ (h.σ.symm v)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm

/-- σ-不変関数は σ^i (i : ℤ) でも不変. -/
private theorem sigma_invariant_zpow (h : Order22ActsOnMoore57 V Γ)
    {f : V → ZMod 11} (hσ : ∀ v, f (h.σ v) = f v) :
    ∀ (i : ℤ) (v : V), f ((h.σ^i) v) = f v := by
  have hf_inv : ∀ v, f (h.σ⁻¹ v) = f v := fun v => by
    have h_app : h.σ (h.σ⁻¹ v) = v := by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel]; rfl
    have := hσ (h.σ⁻¹ v)
    rw [h_app] at this
    exact this.symm
  have hf_pow_nat : ∀ (n : ℕ) (v : V), f ((h.σ^n) v) = f v := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [pow_succ]
      simp only [Equiv.Perm.mul_apply]
      rw [ih (h.σ v)]
      exact hσ v
  have hf_inv_pow_nat : ∀ (n : ℕ) (v : V), f ((h.σ⁻¹^n) v) = f v := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [pow_succ]
      simp only [Equiv.Perm.mul_apply]
      rw [ih (h.σ⁻¹ v)]
      exact hf_inv v
  intro i v
  cases i with
  | ofNat n =>
    show f ((h.σ ^ (n : ℤ)) v) = f v
    rw [zpow_natCast]; exact hf_pow_nat n v
  | negSucc n =>
    show f ((h.σ ^ (Int.negSucc n)) v) = f v
    rw [zpow_negSucc, ← inv_pow]
    exact hf_inv_pow_nat (n+1) v

/-- **Step 3.2**: `dim_F_11 ker T = #σ-orbits = 300`.

Moore57 の σ (order 11, 5 fixed points, 295 free orbits) に対し orbit 数 300.
σ-不変関数空間 ≃ (Quotient (Equiv.Perm.SameCycle.setoid σ) → F_11), dim = 300. -/
theorem finrank_ker_T_F11_eq_300 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (LinearMap.ker (T_F11 h)) = 300 := by
  classical
  haveI : FiniteDimensional (ZMod 11) (V → ZMod 11) := by infer_instance
  -- σ-orbit setoid
  set s : Setoid V := Equiv.Perm.SameCycle.setoid h.σ with hs_def
  haveI : DecidableRel s.r := fun _ _ => Classical.dec _
  haveI : Fintype (Quotient s) := Quotient.fintype s
  -- Pull-back along Quotient.mk
  set pb : (Quotient s → ZMod 11) →ₗ[ZMod 11] (V → ZMod 11) :=
    LinearMap.funLeft (ZMod 11) (ZMod 11) (Quotient.mk s) with hpb_def
  -- pb injective from Quotient.mk surjective
  have h_pb_inj : Function.Injective pb :=
    LinearMap.funLeft_injective_of_surjective (ZMod 11) (ZMod 11)
      (Quotient.mk s) Quotient.mk_surjective
  -- range pb = ker T_F11
  have h_range : LinearMap.range pb = LinearMap.ker (T_F11 h) := by
    ext f
    rw [LinearMap.mem_range, mem_ker_T_F11_iff]
    constructor
    · rintro ⟨g, rfl⟩
      -- pb g = g ∘ Quotient.mk. Show σ-invariant.
      intro v
      show g (Quotient.mk s (h.σ v)) = g (Quotient.mk s v)
      congr 1
      apply Quotient.sound
      -- s.r (h.σ v) v ↔ ∃ i : ℤ, (h.σ^i) (h.σ v) = v
      refine ⟨(-1 : ℤ), ?_⟩
      simp [zpow_neg, zpow_one]
    · intro hσ
      -- σ-invariant ⟹ descends to Quotient.lift
      refine ⟨Quotient.lift f ?_, ?_⟩
      · -- well-definedness: a ~ b → f a = f b
        intro a b hab
        obtain ⟨i, hi⟩ := hab
        rw [← hi]
        exact (sigma_invariant_zpow h hσ i a).symm
      · ext v; rfl
  -- LinearEquiv: (Quotient s → ZMod 11) ≃ₗ LinearMap.range pb
  let e : (Quotient s → ZMod 11) ≃ₗ[ZMod 11] LinearMap.range pb :=
    LinearEquiv.ofInjective pb h_pb_inj
  -- finrank chain
  have h_finrank : Module.finrank (ZMod 11) (LinearMap.ker (T_F11 h)) =
      Module.finrank (ZMod 11) (Quotient s → ZMod 11) := by
    rw [← h_range]
    exact (LinearEquiv.finrank_eq e).symm
  rw [h_finrank, Module.finrank_pi]
  -- Fintype.card (Quotient s) = 300 (両者 Fintype instance が異なる場合 convert で吸収)
  convert card_quotient_sameCycle_eq_300 h using 2

/-! ## Step 3.3: dim range((σ - I)^10) = 295 (= #free orbits)

(σ - I)^10 = Σ_{k=0}^{10} σ^k (F_11 binomial; `sub_one_pow_prime_sub_one_eq_geom_sum`).
この operator は each free orbit の orbit-sum を返し, fixed orbit には 0. -/

/-- F_11 binomial: `(P - 1)^10 = Σ_k P^k` over Matrix V V (ZMod 11). -/
private theorem permMatrixF11_sub_one_pow_ten (h : Order22ActsOnMoore57 V Γ) :
    (permMatrixF11 h.σ - 1)^10 =
      ∑ k ∈ Finset.range 11, (permMatrixF11 h.σ)^k :=
  Moore57.LinearAlgebra.sub_one_pow_prime_sub_one_eq_geom_sum (p := 11)
    (R := Matrix V V (ZMod 11)) (permMatrixF11 h.σ)

/-- `(T_F11 h)^10 = Σ_k ((permMatrixF11 h.σ)^k).toLin'`. -/
private theorem T_F11_pow_ten_eq_sum_toLin' (h : Order22ActsOnMoore57 V Γ) :
    (T_F11 h)^10 = ∑ k ∈ Finset.range 11,
      ((permMatrixF11 h.σ : Matrix V V (ZMod 11))^k).toLin' := by
  rw [T_F11_def]
  rw [show ((permMatrixF11 h.σ - 1 : Matrix V V (ZMod 11)).toLin')^10 =
      ((permMatrixF11 h.σ - 1 : Matrix V V (ZMod 11))^10).toLin' from
    (Matrix.toLin'_pow _ _).symm]
  rw [permMatrixF11_sub_one_pow_ten h]
  exact map_sum _ _ _

/-- `((permMatrixF11 σ)^k).toLin' f v = f((σ^k).symm v)`. -/
private theorem permMatrixF11_pow_toLin'_apply
    (h : Order22ActsOnMoore57 V Γ) (k : ℕ) (f : V → ZMod 11) (v : V) :
    ((permMatrixF11 h.σ : Matrix V V (ZMod 11))^k).toLin' f v =
      f ((h.σ^k).symm v) := by
  rw [Matrix.toLin'_apply, permMatrixF11_pow, permMatrixF11_mulVec_eq]
  rfl

/-- Pointwise: `((T_F11 h)^10) f v = Σ_k f((σ^k).symm v)`. -/
private theorem T_F11_pow_ten_apply
    (h : Order22ActsOnMoore57 V Γ) (f : V → ZMod 11) (v : V) :
    ((T_F11 h)^10) f v = ∑ k ∈ Finset.range 11, f ((h.σ^k).symm v) := by
  have h_eq := T_F11_pow_ten_eq_sum_toLin' h
  have h_apply : ((T_F11 h)^10) f v =
      (∑ k ∈ Finset.range 11,
        ((permMatrixF11 h.σ : Matrix V V (ZMod 11))^k).toLin') f v := by rw [h_eq]
  rw [h_apply, LinearMap.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => permMatrixF11_pow_toLin'_apply h k f v

/-- σ^k preserves σ-fixed points (any k ∈ ℕ). -/
private theorem σ_pow_fix_of_fix (h : Order22ActsOnMoore57 V Γ)
    {v : V} (hv : h.σ v = v) (k : ℕ) : (h.σ^k) v = v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, hv, ih]

/-- σ^k.symm preserves σ-fixed points. -/
private theorem σ_pow_symm_fix_of_fix (h : Order22ActsOnMoore57 V Γ)
    {v : V} (hv : h.σ v = v) (k : ℕ) : (h.σ^k).symm v = v := by
  have h_inv : (h.σ^k) v = v := σ_pow_fix_of_fix h hv k
  have h_app : (h.σ^k) ((h.σ^k).symm v) = v := (h.σ^k).apply_symm_apply v
  exact (h.σ^k).injective (h_app.trans h_inv.symm)

/-- v σ-fixed ⟹ `((T_F11 h)^10) f v = 0`. -/
private theorem T_F11_pow_ten_apply_of_fixed
    (h : Order22ActsOnMoore57 V Γ) (f : V → ZMod 11)
    {v : V} (hv : h.σ v = v) :
    ((T_F11 h)^10) f v = 0 := by
  rw [T_F11_pow_ten_apply]
  have h_each : ∀ k ∈ Finset.range 11, f ((h.σ^k).symm v) = f v :=
    fun k _ => by rw [σ_pow_symm_fix_of_fix h hv k]
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have h11 : ((11 : ℕ) : ZMod 11) = 0 := by decide
  rw [h11, zero_mul]

/-- σ.cycleOf v の support の card = 11 (cycleType analysis). -/
private theorem card_support_cycleOf_eq_eleven
    (h : Order22ActsOnMoore57 V Γ) {v : V} (hv : h.σ v ≠ v) :
    (h.σ.cycleOf v).support.card = 11 := by
  have h_mem : h.σ.cycleOf v ∈ h.σ.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hv)
  have h_in_type : ((h.σ.cycleOf v).support.card : ℕ) ∈ h.σ.cycleType := by
    rw [Equiv.Perm.cycleType_def]
    exact Multiset.mem_map.mpr ⟨h.σ.cycleOf v, h_mem, rfl⟩
  rw [cycleType_σ_eq_replicate h] at h_in_type
  exact Multiset.eq_of_mem_replicate h_in_type

/-- For v ∈ σ-orbit (σv ≠ v), (σ^k).symm v stays in cycle support. -/
private theorem σ_pow_symm_mem_cycle_support
    (h : Order22ActsOnMoore57 V Γ) {v : V} (hv : h.σ v ≠ v) (k : ℕ) :
    (h.σ^k).symm v ∈ (h.σ.cycleOf v).support := by
  rw [Equiv.Perm.mem_support_cycleOf_iff]
  refine ⟨⟨-(k : ℤ), ?_⟩, Equiv.Perm.mem_support.mpr
    ((Equiv.Perm.cycleOf_apply_self h.σ v).symm ▸ hv)⟩
  show (h.σ^(-(k : ℤ))) v = (h.σ^k).symm v
  rw [zpow_neg, zpow_natCast]; rfl

/-- The map `k ↦ (σ^k).symm v` is InjOn `range 11` (for v in free orbit). -/
private theorem σ_pow_symm_injOn
    (h : Order22ActsOnMoore57 V Γ) {v : V} (hv : h.σ v ≠ v) :
    Set.InjOn (fun k : ℕ => (h.σ^k).symm v) (Finset.range 11) := by
  intro k1 hk1 k2 hk2 h_eq
  simp only [Finset.coe_range, Set.mem_Iio] at hk1 hk2
  -- Apply h.σ^k1 to both sides: σ^k1 (σ^k1.symm v) = v and σ^k1 (σ^k2.symm v) = ?
  -- σ^k1 * σ^k2.symm = σ^k1 * (σ^k2)⁻¹ = σ^(k1-k2).
  -- σ^(k1-k2) v = v ⟹ k1 ≡ k2 mod 11.
  change (h.σ^k1).symm v = (h.σ^k2).symm v at h_eq
  have h_pow_v : (h.σ^((k1 : ℤ) - k2)) v = v := by
    have h_factor : h.σ^((k1 : ℤ) - k2) = h.σ^(k1 : ℤ) * (h.σ^(k2 : ℤ))⁻¹ := by
      rw [sub_eq_add_neg, zpow_add, zpow_neg]
    rw [h_factor]
    show ((h.σ^(k1 : ℤ)) * (h.σ^(k2 : ℤ))⁻¹) v = v
    rw [Equiv.Perm.mul_apply]
    rw [show ((h.σ^(k2 : ℤ))⁻¹ : Equiv.Perm V) = (h.σ^k2).symm from by
      rw [zpow_natCast]; rfl]
    rw [← h_eq, zpow_natCast]
    exact (h.σ^k1).apply_symm_apply v
  -- v ∈ cycle support, IsCycleOn ⟹ (σ^m) v = v iff #support ∣ m.
  have h_v_mem : v ∈ (h.σ.cycleOf v).support :=
    Equiv.Perm.mem_support.mpr ((Equiv.Perm.cycleOf_apply_self h.σ v).symm ▸ hv)
  have h_cycleOn := h.σ.isCycleOn_support_cycleOf v
  have h_card := card_support_cycleOf_eq_eleven h hv
  have h_dvd : (11 : ℤ) ∣ ((k1 : ℤ) - k2) := by
    have := (h_cycleOn.zpow_apply_eq h_v_mem (n := (k1 : ℤ) - k2)).mp h_pow_v
    rwa [h_card] at this
  -- |k1 - k2| < 11, so k1 = k2.
  have h_bound : -11 < (k1 : ℤ) - k2 ∧ (k1 : ℤ) - k2 < 11 := by omega
  have : (k1 : ℤ) = k2 := by
    rcases h_dvd with ⟨m, hm⟩
    omega
  exact_mod_cast this

/-- The image of `range 11` via `σ^·.symm v` = cycle support. -/
private theorem image_σ_pow_symm_eq_cycle_support
    (h : Order22ActsOnMoore57 V Γ) {v : V} (hv : h.σ v ≠ v) :
    (Finset.range 11).image (fun k : ℕ => (h.σ^k).symm v) =
      (h.σ.cycleOf v).support := by
  classical
  have h_card := card_support_cycleOf_eq_eleven h hv
  have h_inj := σ_pow_symm_injOn h hv
  have h_image_card :
      ((Finset.range 11).image (fun k : ℕ => (h.σ^k).symm v)).card = 11 := by
    rw [Finset.card_image_of_injOn h_inj, Finset.card_range]
  have h_image_subset :
      (Finset.range 11).image (fun k : ℕ => (h.σ^k).symm v) ⊆
        (h.σ.cycleOf v).support := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨k, _, rfl⟩ := hu
    exact σ_pow_symm_mem_cycle_support h hv k
  exact Finset.eq_of_subset_of_card_le h_image_subset
    (by rw [h_card, h_image_card])

/-- Free orbit case: `((T^10) f) v = Σ_{u ∈ (σ.cycleOf v).support} f u`. -/
private theorem T_F11_pow_ten_apply_of_cycle
    (h : Order22ActsOnMoore57 V Γ) (f : V → ZMod 11)
    {v : V} (hv : h.σ v ≠ v) :
    ((T_F11 h)^10) f v = ∑ u ∈ (h.σ.cycleOf v).support, f u := by
  classical
  rw [T_F11_pow_ten_apply]
  have h_inj := σ_pow_symm_injOn h hv
  have h_image := image_σ_pow_symm_eq_cycle_support h hv
  calc ∑ k ∈ Finset.range 11, f ((h.σ^k).symm v)
      = ∑ u ∈ (Finset.range 11).image (fun k : ℕ => (h.σ^k).symm v), f u :=
        (Finset.sum_image (fun k1 hk1 k2 hk2 => h_inj hk1 hk2)).symm
    _ = ∑ u ∈ (h.σ.cycleOf v).support, f u := by rw [h_image]

/-! ### orbitSumProj LinearMap and surjectivity -/

/-- Orbit sum projection: `f ↦ (c ↦ Σ_{u ∈ c.support} f u)`. -/
noncomputable def orbitSumProj (h : Order22ActsOnMoore57 V Γ) :
    (V → ZMod 11) →ₗ[ZMod 11]
      ({p : Equiv.Perm V // p ∈ h.σ.cycleFactorsFinset} → ZMod 11) where
  toFun f c := ∑ u ∈ (c : Equiv.Perm V).support, f u
  map_add' f g := by ext c; simp [Finset.sum_add_distrib]
  map_smul' a f := by
    ext c
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

private theorem orbitSumProj_apply (h : Order22ActsOnMoore57 V Γ) (f : V → ZMod 11)
    (c : {p : Equiv.Perm V // p ∈ h.σ.cycleFactorsFinset}) :
    orbitSumProj h f c = ∑ u ∈ (c : Equiv.Perm V).support, f u := rfl

/-- Different cycles have disjoint supports. -/
private theorem disjoint_support_of_ne_cycles (h : Order22ActsOnMoore57 V Γ)
    {c1 c2 : {p : Equiv.Perm V // p ∈ h.σ.cycleFactorsFinset}} (h_ne : c1 ≠ c2) :
    _root_.Disjoint (c1 : Equiv.Perm V).support (c2 : Equiv.Perm V).support := by
  have h_perm_disj : (c1 : Equiv.Perm V).Disjoint (c2 : Equiv.Perm V) := by
    apply h.σ.cycleFactorsFinset_pairwise_disjoint c1.prop c2.prop
    intro h_eq
    exact h_ne (Subtype.ext h_eq)
  exact h_perm_disj.disjoint_support

/-- cycleRepAux c1 ∉ c2.support for c1 ≠ c2 (disjoint supports). -/
private theorem cycleRepAux_not_mem_of_ne (h : Order22ActsOnMoore57 V Γ)
    {c1 c2 : {p : Equiv.Perm V // p ∈ h.σ.cycleFactorsFinset}} (h_ne : c1 ≠ c2) :
    cycleRepAux h.σ c1 ∉ (c2 : Equiv.Perm V).support := by
  have h_mem := cycleRepAux_mem h.σ c1
  exact Finset.disjoint_left.mp (disjoint_support_of_ne_cycles h h_ne) h_mem

/-- orbitSumProj is surjective. Use `g ↦ Σ_c g c · indicator(cycleRepAux c)`. -/
private theorem orbitSumProj_surjective (h : Order22ActsOnMoore57 V Γ) :
    Function.Surjective (orbitSumProj h) := by
  classical
  intro g
  -- Define f := Σ_c g c · (indicator at cycleRepAux c).
  refine ⟨fun v => ∑ c : {p : Equiv.Perm V // p ∈ h.σ.cycleFactorsFinset},
            if v = cycleRepAux h.σ c then g c else 0, ?_⟩
  ext c0
  rw [orbitSumProj_apply]
  -- Σ_{u ∈ c0.support} Σ_c (if u = cycleRepAux c then g c else 0).
  -- Swap sums.
  rw [Finset.sum_comm]
  -- Σ_c Σ_{u ∈ c0.support} (if u = cycleRepAux c then g c else 0)
  -- = Σ_c g c · (if cycleRepAux c ∈ c0.support then 1 else 0).
  -- = g c0 (only c0 contributes).
  have h_inner : ∀ c : {p : Equiv.Perm V // p ∈ h.σ.cycleFactorsFinset},
      ∑ u ∈ (c0 : Equiv.Perm V).support,
        (if u = cycleRepAux h.σ c then g c else 0) =
      if c = c0 then g c0 else 0 := by
    intro c
    by_cases h_eq : c = c0
    · subst h_eq
      -- Σ_{u ∈ c.support} (if u = cycleRepAux c then g c else 0).
      -- Exactly one term has u = cycleRepAux c (= the rep).
      have h_rep_mem : cycleRepAux h.σ c ∈ (c : Equiv.Perm V).support :=
        cycleRepAux_mem h.σ c
      rw [Finset.sum_ite_eq' (c : Equiv.Perm V).support (cycleRepAux h.σ c)
        (fun _ => g c)]
      simp [h_rep_mem]
    · -- c ≠ c0. cycleRepAux c ∉ c0.support. All terms are 0.
      have h_not_mem : cycleRepAux h.σ c ∉ (c0 : Equiv.Perm V).support :=
        cycleRepAux_not_mem_of_ne h h_eq
      rw [if_neg h_eq]
      refine Finset.sum_eq_zero fun u hu => ?_
      rw [if_neg]
      intro h_u_eq
      exact h_not_mem (h_u_eq ▸ hu)
  rw [Finset.sum_congr rfl (fun c _ => h_inner c)]
  -- Σ_c (if c = c0 then g c0 else 0) = g c0.
  rw [Finset.sum_ite_eq' Finset.univ c0 (fun _ => g c0)]
  simp

/-- ker(T^10) = ker(orbitSumProj). -/
private theorem ker_T_F11_pow_ten_eq_ker_orbitSumProj
    (h : Order22ActsOnMoore57 V Γ) :
    LinearMap.ker ((T_F11 h)^10) = LinearMap.ker (orbitSumProj h) := by
  ext f
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h_T
    -- (T^10 f) = 0 ⟹ orbitSumProj f = 0.
    ext c
    -- (T^10 f) v = 0 ∀ v. Pick v = cycleRepAux c ∈ c.support.
    have h_rep_mem : cycleRepAux h.σ c ∈ (c : Equiv.Perm V).support :=
      cycleRepAux_mem h.σ c
    have h_not_fixed : h.σ (cycleRepAux h.σ c) ≠ cycleRepAux h.σ c := by
      have h_in_σ_supp : cycleRepAux h.σ c ∈ h.σ.support :=
        Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop h_rep_mem
      exact Equiv.Perm.mem_support.mp h_in_σ_supp
    have h_apply := T_F11_pow_ten_apply_of_cycle h f h_not_fixed
    have h_zero : ((T_F11 h)^10) f (cycleRepAux h.σ c) = 0 := by
      rw [h_T]; rfl
    rw [h_zero] at h_apply
    -- h_apply : 0 = Σ_{u ∈ (σ.cycleOf (cycleRepAux c)).support} f u.
    have h_cycle_eq : h.σ.cycleOf (cycleRepAux h.σ c) = c :=
      (Equiv.Perm.cycle_is_cycleOf h_rep_mem c.prop).symm
    rw [h_cycle_eq] at h_apply
    show (orbitSumProj h f) c = 0
    rw [orbitSumProj_apply]
    exact h_apply.symm
  · intro h_orbit
    -- orbitSumProj f = 0 ⟹ (T^10 f) = 0.
    ext v
    show ((T_F11 h)^10) f v = (0 : V → ZMod 11) v
    show ((T_F11 h)^10) f v = 0
    by_cases hv : h.σ v = v
    · exact T_F11_pow_ten_apply_of_fixed h f hv
    · rw [T_F11_pow_ten_apply_of_cycle h f hv]
      have h_mem : h.σ.cycleOf v ∈ h.σ.cycleFactorsFinset :=
        Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
          (Equiv.Perm.mem_support.mpr hv)
      have h_orbit_at := congrFun h_orbit ⟨h.σ.cycleOf v, h_mem⟩
      simp only [orbitSumProj_apply, Pi.zero_apply] at h_orbit_at
      exact h_orbit_at

/-- **Step 3.3**: `dim_F_11 range(T^10) = 295`. -/
theorem finrank_range_T_F11_pow_ten_eq_295 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (LinearMap.range ((T_F11 h)^10)) = 295 := by
  classical
  haveI : FiniteDimensional (ZMod 11) (V → ZMod 11) := by infer_instance
  -- dim range orbitSumProj = #cycleFactorsFinset = 295 (surjective).
  -- ker T^10 = ker orbitSumProj.
  -- dim range orbitSumProj + dim ker orbitSumProj = dim V_F_11 = 3250.
  -- dim range T^10 + dim ker T^10 = 3250.
  -- ⟹ dim range T^10 = dim range orbitSumProj = 295.
  have h_dim_V : Module.finrank (ZMod 11) (V → ZMod 11) = 3250 := by
    rw [Module.finrank_pi]; exact h.isMoore.card
  have h_dim_target :
      Module.finrank (ZMod 11)
        ({p : Equiv.Perm V // p ∈ h.σ.cycleFactorsFinset} → ZMod 11) = 295 := by
    rw [Module.finrank_pi, Fintype.card_coe]
    -- σ.cycleFactorsFinset.card = σ.cycleType.card (cycleType_def + card_map).
    have h_card : h.σ.cycleFactorsFinset.card = h.σ.cycleType.card := by
      rw [Equiv.Perm.cycleType_def]; simp [Multiset.card_map]
    rw [h_card, cycleType_σ_card_eq_295 h]
  have h_orbit_surj : Function.Surjective (orbitSumProj h) :=
    orbitSumProj_surjective h
  have h_dim_range_orbit :
      Module.finrank (ZMod 11) (LinearMap.range (orbitSumProj h)) = 295 := by
    rw [LinearMap.range_eq_top.mpr h_orbit_surj]
    rw [finrank_top]
    exact h_dim_target
  have h_rank_orbit :
      Module.finrank (ZMod 11) (LinearMap.range (orbitSumProj h)) +
        Module.finrank (ZMod 11) (LinearMap.ker (orbitSumProj h)) =
      Module.finrank (ZMod 11) (V → ZMod 11) :=
    LinearMap.finrank_range_add_finrank_ker _
  have h_rank_T10 :
      Module.finrank (ZMod 11) (LinearMap.range ((T_F11 h)^10)) +
        Module.finrank (ZMod 11) (LinearMap.ker ((T_F11 h)^10)) =
      Module.finrank (ZMod 11) (V → ZMod 11) :=
    LinearMap.finrank_range_add_finrank_ker _
  have h_ker_eq := ker_T_F11_pow_ten_eq_ker_orbitSumProj h
  rw [h_ker_eq] at h_rank_T10
  rw [h_dim_range_orbit, h_dim_V] at h_rank_orbit
  rw [h_dim_V] at h_rank_T10
  omega

/-! ## Step 3.4: 主 dim formula `dim ker((σ-I)^j) = 5 + 295 j`

Steps 3.1 (T^11 = 0), 3.2 (dim ker T = 300), 3.3 (dim range T^10 = 295) と
Jordan 単調性 (`Moore57.LinearAlgebra.finrank_ker_pow_concave`) から derive.

戦略:
* d(j) := dim ker T^j (j = 0, ..., 11).
* d(0) = 0, d(1) = 300 (Step 3.2), d(11) = 3250 (Step 3.1 + ker_zero),
  d(10) = 3250 - 295 = 2955 (Step 3.3 + rank-nullity).
* m_k := d(k+1) - d(k) (in ℤ) は k 非増加 (Jordan).
* m_10 = 295 (最小値). 非増加性 ⟹ m_k ≥ 295 for k ∈ [0, 10].
* Σ_{k=1}^{10} m_k = d(11) - d(1) = 2950 = 10·295. 各 ≥ 295 ⟹ all = 295.
* ⟹ d(j) = d(1) + 295·(j-1) = 5 + 295·j for j ∈ [1, 11].

実装は `Moore57.LinearAlgebra.concave_linearity_forcing` (pure ℕ helper) を経由. -/
theorem finrank_ker_T_F11_pow (h : Order22ActsOnMoore57 V Γ)
    {j : ℕ} (hj : 1 ≤ j) (hj_le : j ≤ 11) :
    Module.finrank (ZMod 11) (LinearMap.ker ((T_F11 h)^j)) = 5 + 295 * j := by
  -- Use opaque `kerDimSeq h` instead of `let f := fun k => ...` to avoid
  -- aggressive unfolding of `(T_F11 h)^k` during helper application.
  haveI : FiniteDimensional (ZMod 11) (V → ZMod 11) := by infer_instance
  -- 凹性
  have hf_concave : ∀ k, 1 ≤ k →
      kerDimSeq h (k+1) + kerDimSeq h (k-1) ≤ 2 * kerDimSeq h k := by
    intro k hk
    rw [kerDimSeq_eq, kerDimSeq_eq, kerDimSeq_eq]
    exact Moore57.LinearAlgebra.finrank_ker_pow_concave (T_F11 h) hk
  -- 単調性
  have hf_mono : ∀ k, kerDimSeq h k ≤ kerDimSeq h (k+1) := by
    intro k
    rw [kerDimSeq_eq, kerDimSeq_eq]
    exact Submodule.finrank_mono
      (Moore57.LinearAlgebra.ker_pow_le_succ (T_F11 h) k)
  -- kerDimSeq h 0 = 0
  have hf_0 : kerDimSeq h 0 = 0 := by
    rw [kerDimSeq_eq, pow_zero,
        show (1 : (V → ZMod 11) →ₗ[ZMod 11] (V → ZMod 11)) = LinearMap.id from rfl,
        LinearMap.ker_id, finrank_bot]
  -- kerDimSeq h 1 = 300
  have hf_1 : kerDimSeq h 1 = 300 := by
    rw [kerDimSeq_eq, pow_one]; exact h.finrank_ker_T_F11_eq_300
  -- dim V_F11 = 3250
  have h_dim_V : Module.finrank (ZMod 11) (V → ZMod 11) = 3250 := by
    rw [Module.finrank_pi]; exact h.isMoore.card
  -- kerDimSeq h 11 = 3250 (T^11 = 0)
  have hf_N : kerDimSeq h 11 = 3250 := by
    rw [kerDimSeq_eq, T_F11_pow_eleven_eq_zero, LinearMap.ker_zero, finrank_top]
    exact h_dim_V
  -- kerDimSeq h 10 = 2955 (rank-nullity)
  have hf_Nm1 : kerDimSeq h 10 = 2955 := by
    rw [kerDimSeq_eq]
    have h_rk :
        Module.finrank (ZMod 11) (LinearMap.range ((T_F11 h)^10)) +
            Module.finrank (ZMod 11) (LinearMap.ker ((T_F11 h)^10)) =
          Module.finrank (ZMod 11) (V → ZMod 11) := by
      apply LinearMap.finrank_range_add_finrank_ker
    rw [h_dim_V, h.finrank_range_T_F11_pow_ten_eq_295] at h_rk
    omega
  have h_consistency : 300 + (11 - 1) * (3250 - 2955) = 3250 := by decide
  have hβγ : (2955 : ℕ) ≤ 3250 := by decide
  have key : kerDimSeq h j = 300 + (j - 1) * (3250 - 2955) :=
    Moore57.LinearAlgebra.concave_linearity_forcing (kerDimSeq h) (by omega)
      hf_concave hf_mono hf_0 hf_1 hf_Nm1 hf_N h_consistency hβγ hj hj_le
  have h_simp : 300 + (j - 1) * (3250 - 2955) = 5 + 295 * j := by
    have h3 : (3250 - 2955 : ℕ) = 295 := by norm_num
    rw [h3]
    have hj' : j - 1 + 1 = j := Nat.sub_add_cancel hj
    have : 295 * j = 295 * (j - 1) + 295 := by
      conv_lhs => rw [← hj']
      ring
    linarith
  -- Chain: goal ← kerDimSeq_eq ← key ← h_simp
  exact (kerDimSeq_eq h j).symm.trans (key.trans h_simp)

end Order22ActsOnMoore57

end Moore57
