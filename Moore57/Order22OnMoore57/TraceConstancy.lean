import Moore57.Order22OnMoore57.BasicStructure
import Moore57.Order22OnMoore57.TraceNumber
import Moore57.Foundations.GroupTheory.CyclicTraceConstancy
import Moore57.Moore57Graph.E7Matrix.SpectralDecomposition
import Moore57.Moore57Graph.E7Matrix.MatrixLinearMapBridge
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# 自然言語証明 §2: trace 数の組合せ的定義と一定性

`Tk h k` を `#{x : Γ.Adj x (σ^k x)}` で定義する.

主結果:
* `traceNumber_eq_Tk_one_div_eleven`: 定義に従う `traceNumber h = T_1 / 11`.
* `eleven_dvd_Tk` (完成): `k ≠ 0 (mod 11)` のとき `11 ∣ T_k`
  (orbit 寄与は 0 か 11; Subtype σ + card_compl_support_modEq).
* `Tk_constant` (sorry): `T_k = T_1` for k = 1..10
  (有理 C_11 表現の指標値が非自明元上で一定).
* `Tk_eq_eleven_mul_traceNumber`: 上記 2 つから `T_k = 11 * n`
  (Phase 3-4 が使う形).
-/

namespace Moore57

namespace Order22ActsOnMoore57

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

variable (h : Order22ActsOnMoore57 V Γ)

/-- `T_k` の組合せ的定義: `x ~ σ^k x` を満たす `x` の個数.

自然言語証明では `T_k = tr(A σ^k)` (行列 trace) として導入されるが,
組合せ的には隣接対の数になる. trace としての側面は Phase 3 (複素 spectral)
で使う. -/
noncomputable def Tk (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : V => Γ.Adj x ((h.σ ^ k) x))).card

/-- `traceNumber h = T_1 / 11` (定義の薄い書き換え). -/
theorem traceNumber_eq_Tk_one_div_eleven : h.traceNumber = h.Tk 1 / 11 := by
  show (Finset.univ.filter (fun x : V => Γ.Adj x (h.σ x))).card / 11
    = (Finset.univ.filter (fun x : V => Γ.Adj x ((h.σ ^ 1) x))).card / 11
  simp [pow_one]

/-- `σ^n x = x` if `σ x = x`, 任意の `n` で. -/
private theorem σ_pow_fix {x : V} (hx : h.σ x = x) (n : ℕ) :
    (h.σ ^ n) x = x := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, hx]

/-- `T_k` の 11 整除性 (orbit 論証).

`S = {x : Γ.Adj x (σ^k x)}` は σ-不変. σ を `Subtype S` に制限すると
位数 11 の置換 τ. τ の不動点は σ 不動点 ∩ S だが,
σ 不動点では `σ^k x = x` で `Γ.Adj x x = False` (loopless) ゆえ S に属さず空.
よって `S.card ≡ 0 (mod 11)`. -/
theorem eleven_dvd_Tk {k : ℕ} (hk : k % 11 ≠ 0) : 11 ∣ h.Tk k := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  -- σ-不変な述語 p
  let p : V → Prop := fun x => Γ.Adj x ((h.σ ^ k) x)
  -- σ と σ^k は可換
  have hcomm : ∀ x : V, (h.σ ^ k) (h.σ x) = h.σ ((h.σ ^ k) x) := fun x => by
    have heq : h.σ ^ k * h.σ = h.σ * h.σ ^ k := by
      rw [← pow_succ, ← pow_succ']
    have := congrArg (· x) heq
    simpa [Equiv.Perm.mul_apply] using this
  -- p の σ-不変性 (subtypePerm の要求形: p (σ x) ↔ p x)
  have hp_iff : ∀ x : V, p (h.σ x) ↔ p x := fun x => by
    show Γ.Adj (h.σ x) ((h.σ ^ k) (h.σ x)) ↔ Γ.Adj x ((h.σ ^ k) x)
    rw [hcomm x]
    exact (h.σ_aut x ((h.σ ^ k) x)).symm
  -- σ を Subtype p に制限
  let τ : Equiv.Perm (Subtype p) := h.σ.subtypePerm hp_iff
  -- τ^11 = 1
  have hτ_pow : τ ^ 11 ^ 1 = 1 := by
    ext ⟨w, _⟩
    show (h.σ ^ 11) w = w
    rw [h.σ_pow_eleven]; rfl
  -- 主補題: |Subtype p| ≡ |τ.supportᶜ| (mod 11)
  have hmod := Equiv.Perm.card_compl_support_modEq
    (α := Subtype p) (p := 11) (n := 1) (σ := τ) hτ_pow
  -- τ の不動点は無い: |τ.supportᶜ| = 0
  have hfix_empty : τ.supportᶜ.card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    rintro ⟨w, hwp⟩ hw
    rw [Finset.mem_compl, Equiv.Perm.mem_support] at hw
    push Not at hw
    -- hw : τ ⟨w, hwp⟩ = ⟨w, hwp⟩ ⟹ σ w = w
    have hwfix : h.σ w = w := congrArg Subtype.val hw
    -- σ w = w → σ^k w = w
    have hkfix : (h.σ ^ k) w = w := h.σ_pow_fix hwfix k
    -- hwp : Γ.Adj w (σ^k w) = Γ.Adj w w (loopless 矛盾)
    have hwp' : Γ.Adj w ((h.σ ^ k) w) := hwp
    rw [hkfix] at hwp'
    exact SimpleGraph.irrefl Γ hwp'
  rw [hfix_empty] at hmod
  -- |Subtype p| = Tk k
  have hcard : Fintype.card (Subtype p) = h.Tk k := by
    rw [Fintype.card_subtype]
    rfl
  rw [hcard] at hmod
  exact Nat.modEq_zero_iff_dvd.mp hmod.symm

end Order22ActsOnMoore57

end Moore57

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Moore57 convention: permMatrix 1 = 1. -/
private theorem moore57_permMatrix_one_local :
    (permMatrix (1 : Equiv.Perm V) : Matrix V V ℚ) = 1 := by
  change Equiv.Perm.permMatrix ℚ ((1 : Equiv.Perm V)⁻¹) = 1
  simp

/-- Moore57 convention: permMatrix is multiplicative (forward, since uses σ⁻¹). -/
private theorem moore57_permMatrix_mul_local (σ τ : Equiv.Perm V) :
    (permMatrix (σ * τ) : Matrix V V ℚ) = permMatrix σ * permMatrix τ := by
  change Equiv.Perm.permMatrix ℚ ((σ * τ)⁻¹) =
    Equiv.Perm.permMatrix ℚ σ⁻¹ * Equiv.Perm.permMatrix ℚ τ⁻¹
  rw [mul_inv_rev, Matrix.permMatrix_mul]

/-- σ permutation matrix の冪と permMatrix の冪は等しい (Moore57 convention). -/
theorem permMatrix_pow_eq (σ : Equiv.Perm V) (n : ℕ) :
    (permMatrix σ : Matrix V V ℚ) ^ n = permMatrix (σ ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact moore57_permMatrix_one_local.symm
  | succ k ih =>
    rw [pow_succ, ih, pow_succ, moore57_permMatrix_mul_local]

/-- (permMatrix σ).toLin' ^ n = (permMatrix (σ ^ n)).toLin'. -/
private theorem permMatrix_toLin'_pow_eq (σ : Equiv.Perm V) (n : ℕ) :
    ((permMatrix σ).toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)) ^ n =
    (permMatrix (σ ^ n)).toLin' := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, moore57_permMatrix_one_local, Matrix.toLin'_one]
    rfl
  | succ k ih =>
    rw [pow_succ, ih]
    rw [Module.End.mul_eq_comp, ← Moore57.matrix_toLin'_mul]
    rw [show permMatrix (σ ^ k) * permMatrix σ = permMatrix (σ ^ (k + 1)) from by
      rw [pow_succ, moore57_permMatrix_mul_local]]

/-- E57 の toLin' 形 idempotency. -/
private theorem E57Matrix_toLin'_isIdempotentElem' (hΓ : IsMoore57 Γ) :
    IsIdempotentElem ((E57Matrix V).toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)) := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Moore57.matrix_toLin'_mul,
    E57Matrix_mul_E57Matrix_eq_E57Matrix hΓ]

/-- E7 の toLin' 形 idempotency (E7Matrix_toLin'_isIdempotentElem の局所コピー). -/
private theorem E7Matrix_toLin'_isIdempotentElem' (hΓ : IsMoore57 Γ) :
    IsIdempotentElem ((E7Matrix Γ).toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)) := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Moore57.matrix_toLin'_mul,
    E7Matrix_mul_E7Matrix_eq_E7Matrix hΓ]

/-- EMinus8 の toLin' 形 idempotency. -/
private theorem EMinus8Matrix_toLin'_isIdempotentElem' (hΓ : IsMoore57 Γ) :
    IsIdempotentElem ((EMinus8Matrix Γ).toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)) := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Moore57.matrix_toLin'_mul,
    EMinus8Matrix_mul_EMinus8Matrix_eq_EMinus8Matrix hΓ]

/-- E57 と permMatrix の toLin' commute. -/
private theorem E57Matrix_toLin'_commute_permMatrix_toLin'
    (σ : Equiv.Perm V) :
    Commute ((E57Matrix V).toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)) (permMatrix σ).toLin' :=
  Moore57.toLin'_commute_of_mul_eq
    (E57Matrix_mul_permMatrix_eq_permMatrix_mul_E57Matrix σ)

/-- EMinus8 と permMatrix の toLin' commute. -/
private theorem EMinus8Matrix_toLin'_commute_permMatrix_toLin'
    (σ : Equiv.Perm V) (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    Commute ((EMinus8Matrix Γ).toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ))
      (permMatrix σ).toLin' :=
  Moore57.toLin'_commute_of_mul_eq
    (EMinus8Matrix_mul_permMatrix_eq_permMatrix_mul_EMinus8Matrix σ haut)

/-- E_λ の matrix trace と LinearMap trace の bridge for permMatrix. -/
private theorem trace_E_perm_eq_trace_toLin'_comp
    (E : Matrix V V ℚ) (σ : Equiv.Perm V) :
    Matrix.trace (E * permMatrix σ) =
    LinearMap.trace ℚ (V → ℚ) (E.toLin' ∘ₗ (permMatrix σ).toLin') := by
  rw [← Moore57.matrix_toLin'_mul, Moore57.trace_toLin'_eq_matrix_trace]

end Moore57

namespace Moore57

namespace Order22ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

variable (h : Order22ActsOnMoore57 V Γ)

/-- (permMatrix h.σ).toLin'^11 = 1, from σ^11 = 1. -/
private theorem permMatrix_toLin'_pow_eleven_eq_one :
    ((permMatrix h.σ).toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)) ^ 11 = 1 := by
  rw [Moore57.permMatrix_toLin'_pow_eq, h.σ_pow_eleven,
      Moore57.moore57_permMatrix_one_local, Matrix.toLin'_one]
  rfl

/-- **核心補題**: E が idempotent かつ permMatrix h.σ と可換のとき,
`tr(E * P_{h.σ^k})` は k ∈ {1..10} で一定. -/
private theorem trace_E_perm_pow_constant
    (E : Matrix V V ℚ)
    (hE_idem : IsIdempotentElem (E.toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)))
    (hE_comm : Commute (E.toLin' : (V → ℚ) →ₗ[ℚ] (V → ℚ)) (permMatrix h.σ).toLin')
    {j k : ℕ} (hj1 : 1 ≤ j) (hjp : j ≤ 10) (hk1 : 1 ≤ k) (hkp : k ≤ 10) :
    Matrix.trace (E * permMatrix (h.σ ^ j)) =
    Matrix.trace (E * permMatrix (h.σ ^ k)) := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  rw [Moore57.trace_E_perm_eq_trace_toLin'_comp,
      Moore57.trace_E_perm_eq_trace_toLin'_comp]
  rw [show (permMatrix (h.σ ^ j)).toLin' = (permMatrix h.σ).toLin' ^ j from
        (Moore57.permMatrix_toLin'_pow_eq h.σ j).symm,
      show (permMatrix (h.σ ^ k)).toLin' = (permMatrix h.σ).toLin' ^ k from
        (Moore57.permMatrix_toLin'_pow_eq h.σ k).symm]
  exact Moore57.LinearMap.trace_idempotent_pow_constant_of_pow_eq_one
    11 (permMatrix h.σ).toLin' (permMatrix_toLin'_pow_eleven_eq_one h)
    E.toLin' hE_idem hE_comm hj1 (by linarith) hk1 (by linarith)

/-- **(Phase 2 残務)** `T_k = T_1` for k = 1..10.

自然言語証明 §2 の rationality 引数: A の各有理固有空間 (E_57, E_7, E_{-8})
は σ-不変な Q[C_11]-加群. C_11 の有理既約表現は trivial 1 と 10 次元 Φ のみ,
Φ の character 値は非自明元上で常に -1. よって `tr(A σ^k)` は k = 1..10 で一定. -/
theorem Tk_constant {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 10) :
    h.Tk k = h.Tk 1 := by
  suffices h_q : ((h.Tk k : ℕ) : ℚ) = ((h.Tk 1 : ℕ) : ℚ) by exact_mod_cast h_q
  -- Tk n は adjacentMovedCount Γ (h.σ ^ n) と定義的等価. ℚ-trace bridge を使う.
  have hTk_trace : ∀ n : ℕ, ((h.Tk n : ℕ) : ℚ) =
      Matrix.trace (Γ.adjMatrix ℚ * permMatrix (h.σ ^ n)) := by
    intro n
    rw [Moore57.trace_adjMatrix_mul_permMatrix_eq_adjacentMovedCount Γ (h.σ ^ n)]
    rfl
  rw [hTk_trace k, hTk_trace 1]
  -- Spectral decomp
  rw [Moore57.adjMatrix_eq_spectral_decomp h.isMoore]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul,
             Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul]
  have h57 : Matrix.trace ((E57Matrix V : Matrix V V ℚ) * permMatrix (h.σ ^ k)) =
             Matrix.trace ((E57Matrix V : Matrix V V ℚ) * permMatrix (h.σ ^ 1)) := by
    rw [Moore57.trace_E57Matrix_mul_permMatrix h.isMoore,
        Moore57.trace_E57Matrix_mul_permMatrix h.isMoore]
  have h7 : Matrix.trace (E7Matrix Γ * permMatrix (h.σ ^ k)) =
            Matrix.trace (E7Matrix Γ * permMatrix (h.σ ^ 1)) :=
    h.trace_E_perm_pow_constant (E7Matrix Γ)
      (Moore57.E7Matrix_toLin'_isIdempotentElem' h.isMoore)
      (Moore57.toLin'_commute_of_mul_eq
        (E7Matrix_mul_permMatrix_eq_permMatrix_mul_E7Matrix Γ h.σ h.σ_aut))
      hk1 hk2 (by norm_num) (by norm_num)
  have hm8 : Matrix.trace (EMinus8Matrix Γ * permMatrix (h.σ ^ k)) =
             Matrix.trace (EMinus8Matrix Γ * permMatrix (h.σ ^ 1)) :=
    h.trace_E_perm_pow_constant (EMinus8Matrix Γ)
      (Moore57.EMinus8Matrix_toLin'_isIdempotentElem' h.isMoore)
      (Moore57.EMinus8Matrix_toLin'_commute_permMatrix_toLin' h.σ h.σ_aut)
      hk1 hk2 (by norm_num) (by norm_num)
  rw [h57, h7, hm8]

/-- k = 1 の特別ケース (sorry-free, `eleven_dvd_Tk` のみに依存). -/
theorem Tk_one_eq_eleven_mul_traceNumber : h.Tk 1 = 11 * h.traceNumber := by
  rw [h.traceNumber_eq_Tk_one_div_eleven]
  have hdvd : 11 ∣ h.Tk 1 := h.eleven_dvd_Tk (by decide)
  omega

/-- 結論 (Phase 3-4 で利用): `T_k = 11 n` for k = 1..10.

`Tk_constant` と `traceNumber` の定義から従う.
k = 1 では `Tk_one_eq_eleven_mul_traceNumber` で sorry なしに導出可. -/
theorem Tk_eq_eleven_mul_traceNumber {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 10) :
    h.Tk k = 11 * h.traceNumber := by
  rw [h.Tk_constant hk1 hk2]
  exact h.Tk_one_eq_eleven_mul_traceNumber

end Order22ActsOnMoore57

end Moore57
