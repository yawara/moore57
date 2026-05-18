# Roadmap: discharge `srg_k_sq_plus_one_degree_classification`

最後の axiom:

```lean
axiom srg_k_sq_plus_one_degree_classification
    {W : Type*} [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (k : ℕ)
    (_hsrg : G.IsSRGWith (k * k + 1) k 0 1) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57
```

これは古典的な **Hoffman-Singleton 限界** (girth-5 Moore graphs / SRG(k²+1, k, 0, 1))
の Lean 化. Mathlib に既存形式化なし (本タスクは fresh).

## 1. 数学的証明 (古典版)

### 1.1 Setup

`A := G.adjMatrix ℝ` (もしくは ℚ) — 隣接行列.
`IsSRGWith.matrix_eq` から: `A² = k·I + 0·A + 1·(J - I - A)` ⟹
```
A² + A − (k − 1)·I = J
```
ここで `J` は all-ones 行列.

A は k-正則: `A·𝟙 = k·𝟙` (where `𝟙` is all-ones vector).

### 1.2 Spectrum

スペクトル分解:
- **Perron 固有値** `k` (multiplicity 1, 固有ベクトル `𝟙`).
- 残り (n − 1 = k² 次元の `𝟙⊥` 上で): `p(X) := X² + X − (k − 1) = 0`.
- 判別式 `D := 4k − 3`.
- 2 つの非自明固有値: `λ_± := (−1 ± √D) / 2`.
- 多重度 `m_+, m_- ≥ 0`.

### 1.3 制約

```
m_+ + m_- = k²          (dim J⊥)
m_+ λ_+ + m_- λ_- = -k  (trace A = 0 引いて Perron)
```

### 1.4 場合分け

**Case A: D not perfect square (irrational case)**

`√D` 無理数. `λ_+ = (-1+√D)/2 ∈ ℝ\ℚ`.

`m_+ λ_+ + m_- λ_- = -((m_+ + m_-)/2) + (m_+ - m_-)·√D/2 = -k²/2 + (m_+ - m_-)·√D/2`.

`= -k` から:
```
(m_+ - m_-) · √D = k² - 2k = k(k - 2)
```

LHS 無理数 × 整数 = 有理数 RHS ⟹
`m_+ = m_- ∧ k(k - 2) = 0` ⟹ `k ∈ {0, 2}`.

**Case B: D = (2u+1)² (perfect square)**

`k = u² + u + 1`, `λ_+ = u`, `λ_- = -(u+1)`.

`m_+(2u+1) = k(k(u+1) - 1) = (u²+u+1) · u · (u² + 2u + 2)`.

`(2u+1)` 奇数, `gcd(64, 2u+1) = 1`. Modular arithmetic:
- `4u ≡ -2 (mod 2u+1)`.
- `4u² ≡ 1`.
- `4(u²+u+1) ≡ 3`.
- `4(u²+2u+2) ≡ 5`.
- `64 · u(u²+u+1)(u²+2u+2) ≡ (-2)·3·5 = -30 (mod 2u+1)`.

`m_+ ∈ ℤ` ⟺ `(2u+1) | u(u²+u+1)(u²+2u+2)` ⟺ `(2u+1) | 30`.

奇正除数 of 30: `{1, 3, 5, 15}` ⟹ `2u+1 ∈ {1, 3, 5, 15}` ⟹ `u ∈ {0, 1, 2, 7}`
⟹ `k ∈ {1, 3, 7, 57}`.

### 1.5 結論

`k ∈ {0, 1, 2, 3, 7, 57}` (Case A ∪ Case B).

## 2. Lean 形式化方針

### 2.1 既存 Mathlib infrastructure (調査済み)

**SRG core** (`Mathlib/Combinatorics/SimpleGraph/StronglyRegular.lean`):
- `IsSRGWith.matrix_eq`: `A² = k•I + ℓ•A + μ•Cᵃᵈʲ`. (本ケースで `J - I` 形.)
- `IsSRGWith.param_eq`: `k(k-ℓ-1) = (n-k-1)μ`.

**Adjacency matrix**:
- `Matrix.trace_adjMatrix = 0`.
- `Matrix.isSymm_adjMatrix`, `isHermitian` (over ℝ).

**Spectral theory** (`Mathlib/Analysis/Matrix/Spectrum.lean`):
- `Matrix.IsHermitian.eigenvalues : n → ℝ`.
- `IsHermitian.spectral_theorem` (eigenbasis exists).
- `IsHermitian.trace_eq_sum_eigenvalues`. ★ 重要.

**Charpoly / minpoly** (`Mathlib/LinearAlgebra/Matrix/Charpoly/Eigs.lean`):
- `mem_spectrum_iff_isRoot_charpoly`.

**Irrationality** (`Mathlib/NumberTheory/Real/Irrational.lean`):
- `irrational_sqrt_intCast_iff_of_nonneg : Irrational √z ↔ ¬IsSquare z` (for `z : ℤ`, `z ≥ 0`).

### 2.2 既存ローカル infrastructure (再利用候補)

- `Moore57/Moore57Graph/E7Matrix/Idempotent.lean`:
  - `allOnesMatrix V` (J 行列の定義).
  - `adjMatrix_mul_allOnesMatrix_of_regular`: A·J = k·J.
  - `allOnesMatrix_mul_adjMatrix_of_regular`: J·A = k·J.
  - これらは regular graph で成り立つ汎用補題. SRG(k²+1, k, 0, 1) でも使える.
- `Moore57/Moore57Graph/E7Matrix/SpectralDecomposition.lean`:
  - k = 57 専用の E_57, E_7, E_{-8} 構築 + idempotency + orthogonality.
  - 一般 SRG(k²+1, k, 0, 1) 用に generalize できる骨格.

### 2.3 戦略選択: ℝ-Hermitian (Approach A)

Mathlib に存在する Hermitian spectral theorem を活用.

**Pros**:
- `Matrix.IsHermitian.eigenvalues` が `n → ℝ` を提供.
- `trace_eq_sum_eigenvalues` が trace 公式を直接与える.
- 既知 Mathlib 道.

**Cons**:
- 多重度を `Fintype.card {i | eigenvalues i = λ}` 形で扱う.
- 全固有値が `{k, λ_+, λ_-}` であることを示す必要 (case analysis on eigenvector).
- 実数演算 (√).

**代替: ℚ 完全 (Approach B)** — `ℚ[X]/p`-module 構造を活用.
- Pros: 実数解析不要.
- Cons: `AdjoinRoot` 系列 + Quotient module 操作で重い.

**選択**: Approach A (Hermitian) を採用. Mathlib 既存 lemma の活用率が高い.

## 3. ステージ分解

### Stage S0: Setup (~100 行)

ファイル候補: `Moore57/Foundations/GraphTheory/HoffmanSingleton.lean` (新規).

```lean
namespace Moore57

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (G : SimpleGraph W) [DecidableRel G.Adj]
variable {k : ℕ} (hsrg : G.IsSRGWith (k * k + 1) k 0 1)

/-- Discriminant of the eigenvalue equation. -/
noncomputable def srgDiscriminant : ℤ := 4 * k - 3
```

- `k = 0` corner case を直接処理 (output `Or.inl rfl`).

### Stage S1: Adjacency matrix identity (~150 行)

```lean
theorem srg_kk_plus_one_matrix_eq (hsrg : ...) :
    let A := G.adjMatrix ℝ;
    A * A + A - (k - 1 : ℝ) • 1 = allOnesMatrix W - 1
```

`IsSRGWith.matrix_eq` から導出. (`Cᵃᵈʲ = J - I - A` を展開.)

### Stage S2: A·𝟙 = k·𝟙, A·J = k·J (~100 行)

`allOnesMatrix` 形での補題. E7Matrix/Idempotent.lean の generalize.

### Stage S3: Eigenvalue enumeration (~300 行)

- A is Hermitian (real symmetric).
- Every eigenvalue μ of A satisfies either μ = k (with eigenvector 𝟙) or μ² + μ - (k-1) = 0.
- ker(A - k·I) = ℝ·𝟙 (1-dim).
  - 証明: A·v = k·v ∧ ⟨v, 𝟙⟩ = 0 ⟹ J·v = 0, でも (A² + A - (k-1)I)·v = J·v = 0, つまり
    (k² + k - k + 1)·v = 0 ⟹ (k² + 1)·v = 0 ⟹ v = 0.

### Stage S4: Multiplicities m_+, m_- as ℕ-counts (~250 行)

```lean
noncomputable def srgMultPlus : ℕ := 
  Fintype.card {i : W | hHerm.eigenvalues i = srgLambdaPlus k}
noncomputable def srgMultMinus : ℕ := ...
```

- `m_+ + m_- = k²` (Fintype.card_eq_sum_ones + bijection with {i | eigenvalues i ≠ k}).
- `m_+ λ_+ + m_- λ_- = -k` (`trace_eq_sum_eigenvalues` + trace_adjMatrix = 0).

### Stage S5: Case A (irrational discriminant) (~250 行)

```lean
theorem srg_kk_plus_one_irrational_case (hsrg : ...)
    (hD : ¬ IsSquare ((4 * k - 3 : ℤ))) (hk : 1 ≤ k) :
    k = 2
```

- `irrational_sqrt_intCast_iff_of_nonneg` (need 4k - 3 ≥ 0, i.e., k ≥ 1 — 0 case excluded).
- `√D` irrational ⟹ `m_+ - m_- = 0` ∧ `k(k-2) = 0` ⟹ `k = 2` (under `k ≥ 1`).

### Stage S6: Case B (square discriminant) (~400 行)

```lean
theorem srg_kk_plus_one_square_case (hsrg : ...) (u : ℕ)
    (hD : (4 * k - 3 : ℤ) = (2 * u + 1)^2) :
    k = 1 ∨ k = 3 ∨ k = 7 ∨ k = 57
```

- `k = u² + u + 1` from D equation.
- m_+ formula: `m_+(2u+1) = k(k(u+1) - 1)`.
- Modular: `64 · m_+(2u+1) ≡ -30 (mod (2u+1))`.
- `m_+ ∈ ℕ` ⟹ `(2u+1) | 30`.
- `2u+1 ∈ {1, 3, 5, 15}` via `Nat.divisors 30 |>.filter Odd` or interval_cases.
- `decide` で `u ∈ {0, 1, 2, 7}` から `k`.

### Stage S7: Main theorem assembly (~80 行)

```lean
theorem srg_kk_plus_one_degree_classification' {W : Type*} [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (k : ℕ)
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by
  by_cases hk0 : k = 0
  · exact Or.inl hk0
  by_cases hsq : IsSquare ((4 * k - 3 : ℤ))
  · -- Case B
    obtain ⟨u, hu⟩ := ...
    rcases srg_kk_plus_one_square_case G hsrg u hu with ...
    -- output k = 1 ∨ k = 3 ∨ k = 7 ∨ k = 57
  · -- Case A
    have hk2 := srg_kk_plus_one_irrational_case G hsrg hsq (by omega : 1 ≤ k)
    exact Or.inr (Or.inr (Or.inl hk2))
```

### 合計見積もり

| Stage | 内容 | 行数 | 難易度 |
|-------|------|-----|--------|
| S0 | Setup, k=0 case | 100 | 易 |
| S1 | matrix_eq 展開 | 150 | 易 |
| S2 | A·J = k·J | 100 | 易 (既存補題) |
| S3 | 固有値列挙 + m_k = 1 | 300 | 中 |
| S4 | m_+, m_- 多重度 | 250 | **難** (Hermitian count) |
| S5 | Case A (irrational) | 250 | 中 |
| S6 | Case B (mod arith) | 400 | 中 (omega + decide) |
| S7 | Assembly | 80 | 易 |
| **計** | | **1630** | |

## 4. 実装上の懸念とハマりどころ

### 4.1 ℝ-Hermitian の多重度カウント

`IsHermitian.eigenvalues : Fin n → ℝ` は eigenbasis 上の eigenvalue assignment.
複数の `i` が同じ eigenvalue を持つ場合 (重複度 > 1) もある.

`m_+ := Fintype.card {i | hHerm.eigenvalues i = λ_+}` は `ℕ`.
SRG 性から `m_k + m_+ + m_- = n` (全 i がいずれかに属する).

これを Lean で出すには `Fintype.card` の分割 (3-way) と eigenvalue exhaustiveness.

### 4.2 整数 mod arithmetic in Case B

`(2u+1) | 30` を `omega` で扱えるか? 一般 u では omega 直接は無理だが,
`64 · 30 = 1920` の divisibility を `decide` で潰せる. 帰着方法:

```lean
have h64 : (2*u + 1) ∣ 64 * (u * (u^2+u+1) * (u^2+2*u+2)) := ...
have h30 : (2*u + 1) ∣ 30 := by
  have := Nat.Coprime.dvd_of_dvd_mul_left ...  -- gcd(2u+1, 64) = 1
  ...
```

### 4.3 場合分け `2u+1 ∈ {1, 3, 5, 15}`

`Nat.divisors 30` の `filter Odd` で `{1, 3, 5, 15}` (or `{15, 5, 3, 1}`).
Alternatively `interval_cases (2*u+1)` after bounding.

### 4.4 既存 E7Matrix 系の参考

`Moore57/Moore57Graph/E7Matrix/SpectralDecomposition.lean` は具体的 k=57 で
E_57, E_7, E_{-8} の idempotency, orthogonality, sum=I を ~2-300 行で証明.

一般化版を `Foundations/GraphTheory/HoffmanSingleton.lean` に書けば,
既存 D_19 / Order22 で使う `E7Matrix` も後で refactor 候補 (本タスク外).

## 5. 進め方の提案

### Phase 1: Foundation (S0-S2, ~300 行)

- 新規ファイル `Moore57/Foundations/GraphTheory/HoffmanSingleton.lean`.
- `allOnesMatrix` の general regular graph 版を整備.
- SRG(k²+1, k, 0, 1) の matrix identity をクリーン化.

### Phase 2: Spectral analysis (S3-S4, ~550 行)

- ℝ-Hermitian で固有値分解.
- 多重度 m_k = 1, m_+, m_- を定義 + 制約導出.

### Phase 3: Case analysis (S5-S7, ~730 行)

- Case A: irrationality argument.
- Case B: modular arithmetic + 4-divisor case split.
- Assembly.

## 6. 期待される完了状態

- `srg_k_sq_plus_one_degree_classification` axiom 削除.
- `no_Order22_acts_on_Moore57` の axiom set:
  - `propext, Classical.choice, Quot.sound` (Lean core).
  - `Fin5_cycle_involution_classify._native.native_decide.ax_1_1` (1 native_decide).

これにより, Order22 主結果は **完全 unconditional** となり,
D_19 主結果 (既存 unconditional) と同等の axiom 純度に到達.

## 7. 参考文献

- A.J. Hoffman, R.R. Singleton, "On Moore graphs with diameters 2 and 3",
  IBM J. Res. Develop. 4 (1960), 497-504.
- A.E. Brouwer, A.M. Cohen, A. Neumaier, "Distance-Regular Graphs",
  Springer 1989. Ch.1 (SRG basics).
- P.J. Cameron, J.H. van Lint, "Designs, Graphs, Codes and Their Links",
  LMS Student Texts 22, Ch.3 (Strongly regular graphs).
- C. Dalfó, "A survey on the missing Moore graph",
  Linear Algebra and its Applications 569 (2019) 1–14. (Modern survey.)
