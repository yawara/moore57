import Moore57.Order22OnMoore57.Phase4F11Module
import Moore57.Foundations.LinearAlgebra.JordanMonotonicity
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

/-- `Fintype.card (Quotient (SameCycle.setoid σ))` を |Fix σ| + cycleFactorsFinset.card に
分解する補題. 各 orbit は fixed point の singleton か, cycle factor の support に対応. -/
private theorem card_quotient_sameCycle_eq (h : Order22ActsOnMoore57 V Γ) :
    @Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid h.σ))
        (@Quotient.fintype _ _ _ (fun _ _ => Classical.dec _)) =
      Fintype.card (Function.fixedPoints h.σ) + h.σ.cycleFactorsFinset.card := by
  -- Bijection: Quotient ≃ Function.fixedPoints σ ⊕ cycleFactorsFinset σ.
  -- Forward: [v] ↦ if σ v = v then inl ⟨v, hv⟩ else inr (cycleOf σ v).
  -- Backward: inl ⟨v, _⟩ ↦ [v], inr c ↦ [some v ∈ support c].
  sorry

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
  -- TODO: range pb = ker T_F11 (matrix calculation)
  -- TODO: LinearEquiv + finrank_pi + card_quotient_sameCycle_eq_300
  sorry

/-! ## Step 3.3: dim range((σ - I)^10) = 295 (= #free orbits)

(σ - I)^10 = Σ_{k=0}^{10} σ^k (F_11 binomial; C(10, k) ≡ ±1 mod 11 + 符号統合).
この operator は each free orbit の orbit-sum を返し, fixed orbit には 0.
よって range = span of free orbit-sum, dim = #free orbits = 295. -/

/-- **Step 3.3 (sorry)**: `dim_F_11 range(T^10) = 295`. -/
theorem finrank_range_T_F11_pow_ten_eq_295 (h : Order22ActsOnMoore57 V Γ) :
    Module.finrank (ZMod 11) (LinearMap.range ((T_F11 h)^10)) = 295 := by
  sorry

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
