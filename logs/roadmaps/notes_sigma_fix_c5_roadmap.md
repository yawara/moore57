# Roadmap: σ_fix elimination (Fix(σ) ≅ C_5 for σ of order 11)

`Order22ActsOnMoore57` 構造体に残る最後の conditional 入力
`σ_fix : C5FixedData Γ σ` を, raw 作用 (`σ^11 = 1`, `σ ≠ 1`, `σ_aut`) から
derive することを目指す.

最終 derive 形:

```lean
noncomputable def σ_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (σ_aut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (σ_pow_eleven : σ ^ 11 = 1) (σ_ne_one : σ ≠ 1) :
    C5FixedData Γ σ
```

## 1. 文献整理

### Macaj-Siran 2010 (`tmp/pdfs/j.laa.2009.07.018.txt`)
- **Lemma 1** (Aschbacher 1971): X ≤ Aut(Γ) のとき, Fix(X) は次のいずれか:
  empty, isolated vertex, pentagon (C_5), Petersen graph, Hoffman-Singleton graph, star K_{1,n}.
- **Lemma 4**: X が奇素数 p 位数のとき, p の各場合の divisibility 制約.
  - (1) Fix empty: |X| | 13·5.
  - (2) Fix singleton: |X| | 3·19.
  - (3) Fix star (|Fix| = 2+7l): |X| | 7.
  - (4) Fix pentagon: |X| | 11·5. ← **p=11 はこのケースのみ**
  - (5) Fix Petersen: |X| | 3.
  - (6) Fix HS: |X| | 5.
- **Lemma 12**: p=11, a_0(x) = 5 の場合, a_1(x) ∈ {55, 220, 385} (n ∈ {5, 20, 35}).

### Makhnev-Paduchikh (`tmp/pdfs/involution-fixed-star.txt`)
- **Lemma 3** (line 120-): Macaj-Siran Lemma 4 と同等のステートメント, 証明 sketch あり.
  - Fix が Moore graph of valence k ⟹ X が a ∈ Fix(X) の N(a)\Fix(X) (57-k 頂点) 上で
    fpf に作用 ⟹ |X| | (57-k).
  - k=2 ⟹ |X| | 55.
  - k=3 ⟹ |X| | 54 → 27 (奇素数).
  - k=7 ⟹ |X| | 50 → 25.
  - Star case: |[b] - Fix(X)| = 56 ⟹ |X| | 56 → 7.

## 2. 数学的アプローチ (我々のためのカスタム版)

Full Aschbacher 分類を回避し, p=11 特化で済ませる route を選ぶ.

### 主補題: σ の固定部分グラフ H は SRG(k²+1, k, 0, 1) で k=2

**(A) Fix(σ) の濃度 mod 11 (Cauchy)**:
σ^11 = 1, |V| = 3250 = 11·295 + 5 ⟹ |Fix(σ)| ≡ 5 (mod 11).
特に |Fix(σ)| ≥ 5.

**(B) 任意の v ∈ Fix(σ) について, fix-近傍数 ≡ 2 (mod 11)**:
σ は N(v) 上に作用. σ-fix な近傍は H 内の v の隣接頂点, 残りは 11-orbit.
|N(v)| = 57 = 11·5 + 2 ⟹ (fix-近傍数) ≡ 2 (mod 11).

**(C) 星 case 排除**:
H が center c の star ⟹ leaf u は H 内 degree 1.
1 ≢ 2 (mod 11), (B) と矛盾. 従って H は正則.

**(D) 正則 case の SRG 化**:
既存 `autFixedInducedGraph_isSRGWith_of_regular` で
H is SRG(|Fix(σ)|, k, 0, 1).
SRG パラメータ式 `k(k-λ-1) = (v-k-1)μ` で λ=0, μ=1 から
**|Fix(σ)| = k² + 1**.

**(E) k ≡ 2 (mod 11)** + k² + 1 ≡ 5 (mod 11) 同等 ((B) より).
解は k ∈ {2, 13, 24, 35, 46, 57}.

**(F) Hoffman-Singleton 局所版**:
SRG(k²+1, k, 0, 1) が存在するための整数性: multiplicity formula
- m_+ + m_- = k².
- λ_+ m_+ + λ_- m_- = -k.

両方非負整数になる k の集合 = {1, 2, 3, 7, 57} (= Hoffman-Singleton bound).

具体的に:
- k=2: 半整数 case, m_+ = m_- = 2, λ_± = (-1±√5)/2 irrational. OK.
- k=3: λ_+ = 1, λ_- = -2, m_+ = 5, m_- = 4. Petersen.
- k=7: λ_+ = 2, λ_- = -3, m_+ = 28, m_- = 21. HS.
- k=13: λ_+ = 3, λ_- = -4, m_+ - m_- = 13·11/7 = 143/7 (NOT integer). 排除.
- k=24: D = 93, not perfect square. m_+ = m_- 強制 + k=24 ≠ 2 矛盾. 排除.
- k=35, 46: 同様, D not perfect square + k ≠ 2 排除.
- k=57: D = 225, m_+ = 1729, m_- = 1520. OK だが (G) で σ=1 排除.

従って **k ∈ {2, 57}**.

**(G) k=57 排除**:
k=57 ⟹ ∀v ∈ Fix(σ), ∀w ∈ N(v) は v に隣接 ∧ Fix(σ). しかし
Moore57 graph は connected (diameter 2), さらに H 自身が Moore57 構造を持つ
⟹ |Fix(σ)| = 3250 = |V| ⟹ σ = 1. 矛盾.

**(H) 結論: k=2**.
SRG(5, 2, 0, 1) は C_5 (5-cycle) unique. v = h.σ_fix.v は C_5 の頂点を
循環順に取って構成.

### Bound on k via Cauchy interlacing (代替案)

H is induced subgraph of Γ. By Cauchy interlacing:
- H の eigenvalue ≤ Γ の eigenvalue (sorted desc).
- H_max eigenvalue = k.
- Γ の eigenvalues: 57 ≥ 7 ≥ -8.
- ⟹ k ≤ 57.

そして H_min eigenvalue = λ_- ≥ -8.

これで上界 k ≤ 57 を取ることで k ∈ {2, 13, 24, 35, 46, 57} と有限化できる.

## 3. Lean 形式化プラン

### Stage 1: 一般化版 modEq 補題 (Tier-2)

**ファイル候補**: `Moore57/Moore57Graph/Aut/FixedCountPrime.lean` (新規).

既存の `aut_fixedVertexCount_modEq_one_of_pow_nineteen` (p=19 専用) を
一般素数 p に generalize.

```lean
theorem aut_fixedVertexCount_modEq_card_of_pow_prime
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (pow_p : σ ^ p = 1) :
    fixedVertexCount σ ≡ Fintype.card V [MOD p]
```

p=11 specialize 系:

```lean
theorem aut_fixedVertexCount_modEq_five_of_pow_eleven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (pow_eleven : σ ^ 11 = 1) :
    fixedVertexCount σ ≡ 5 [MOD 11]
```

同様に `aut_card_fixedNeighborFinset_modEq_two_of_pow_eleven` も追加.

**見積もり**: ~100-200 行 (既存 p=19 のミラー).

### Stage 2: 星 case 排除 (p=11)

```lean
theorem aut_fixedInducedGraph_not_star_of_pow_eleven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1) (hne : σ ≠ 1)
    (hfixpos : 2 ≤ fixedVertexCount σ) :
    ¬ ∃ c, IsStarWithCenter (autFixedInducedGraph Γ σ) c
```

leaf vertex の fix-近傍数 = 1 ≢ 2 (mod 11) 矛盾.

**見積もり**: ~150 行.

### Stage 3: 正則 case の SRG パラメータ + k 制約

既存 `autFixedInducedGraph_isSRGWith_of_regular` を活用. 続けて:

```lean
theorem aut_fixedInducedGraph_regular_degree_modEq_two_of_pow_eleven
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1)
    (k : ℕ) (hreg : ∀ x, (autFixedInducedGraph Γ σ).degree x = k) :
    k ≡ 2 [MOD 11]
```

SRG 性から |Fix(σ)| = k² + 1.

**見積もり**: ~200 行 (`InvolutionCandidates.lean` の regular 部分を参考).

### Stage 4: SRG(k²+1, k, 0, 1) の k ∈ {0, 1, 2, 3, 7, 57}

ローカル版 Hoffman-Singleton. eigenvalue/multiplicity 整数性条件.

```lean
theorem srg_kk_plus_one_degree_classification
    (k : ℕ) (m_plus m_minus : ℕ)
    (hm_sum : m_plus + m_minus = k * k)
    (htrace : ∃ (λp λm : ℝ), λp + λm = -1 ∧ λp * λm = -(↑k - 1) ∧
      (↑m_plus * λp + ↑m_minus * λm : ℝ) = -↑k) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57
```

または直接 `interval_cases k`:
- k ≤ 57 (from Cauchy interlacing / |Fix| ≤ |V|).
- k ≡ 2 (mod 11) (Stage 3).
- ⟹ k ∈ {2, 13, 24, 35, 46, 57}.
- 各 case: multiplicity formula で整数性 check, k=13, 24, 35, 46 排除.

具体的補題:
- `srg_2_5_existence`: SRG(5, 2, 0, 1) exists, isomorphic to C_5.
- `srg_170_13_nonexistence`: SRG(170, 13, 0, 1) does not exist (m_+ = 663/7).
- `srg_kk_half_case_forces_k_two`: D not perfect square ⟹ k = 2.

**見積もり**: ~400-800 行 (eigenvalue 整数性論証, Mathlib `SRG` infrastructure 活用).

### Stage 5: k=57 排除

```lean
theorem aut_fixedInducedGraph_regular_degree_lt_57_of_ne_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (k : ℕ) (hreg : ∀ x, (autFixedInducedGraph Γ σ).degree x = k)
    (hne : σ ≠ 1) :
    k < 57
```

k=57 ⟹ Fix(σ) ⊆ V でかつ ∀v ∈ Fix(σ), N(v) ⊆ Fix(σ). Moore graph diameter 2
+ connected ⟹ V = Fix(σ) ⟹ σ = 1. 矛盾.

**見積もり**: ~150 行.

### Stage 6: |Fix(σ)| = 5 を確定

Stage 2 + 3 + 4 + 5 を組み合わせ:

```lean
theorem aut_order_eleven_fixedVertexCount_eq_five
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1) (hne : σ ≠ 1) :
    fixedVertexCount σ = 5
```

**見積もり**: ~50 行 (wire-up).

### Stage 7: 5 頂点を循環順に並べる + C5FixedData 構成

```lean
noncomputable def aut_order_eleven_C5FixedData
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1) (hne : σ ≠ 1) :
    C5FixedData Γ σ
```

5 頂点を取り出し, 隣接関係から循環順を構築. SRG(5, 2, 0, 1) は C_5 unique
(同型を除く) なので, traversal で v_0, v_1, ..., v_4 を順に取得.

各フィールド (`v_injective`, `v_fixed`, `span`, `cycle_adj`, `cycle_only`)
を Stage 2-6 の結果から組み立て.

**見積もり**: ~300-500 行 (構造体構築 + 各フィールドの証明).

### Stage 8: Order22 構造体への組込

`Order22ActsOnMoore57` から `σ_fix` フィールド削除し,
`Order22ActsOnMoore57.σ_fix` を derived def に置換:

```lean
noncomputable def σ_fix : C5FixedData Γ h.σ :=
  Moore57.aut_order_eleven_C5FixedData h.isMoore h.σ h.σ_aut h.σ_pow_eleven h.σ_ne_one
```

dot notation 互換性は維持.

**見積もり**: ~50 行 (mostly Action.lean の修正 + import 整理).

## 4. 工数とリスク見積もり

| Stage | 内容 | 行数見積 | 難易度 |
|---|---|---|---|
| 1 | mod p 補題 generalize | 100-200 | 易 |
| 2 | 星 case 排除 | 150 | 中 |
| 3 | 正則 case k ≡ 2 mod 11 | 200 | 中 |
| 4 | **SRG k 分類 (local HS)** | 400-800 | **難** |
| 5 | k=57 排除 | 150 | 中 |
| 6 | wire-up to a_0=5 | 50 | 易 |
| 7 | C5FixedData 構築 | 300-500 | 中 |
| 8 | Order22 統合 | 50 | 易 |
| **計** |   | **1400-2100** |   |

**最大リスク**: Stage 4 (Hoffman-Singleton bound). Mathlib に SRG eigenvalue
multiplicity 関連の infrastructure があるか未確認. 自前構築が必要なら
+500 行覚悟.

**代替**: Stage 4 を spectral 直接計算 (我々の Phase 3 で使った
`E7Matrix` 化 + character 論証) で k=2 を導けば, Mathlib 依存を減らせる.
ただし induced 部分グラフへの eigenvalue 解析は別途整備が必要.

## 5. 既存 infrastructure 再利用ポイント

- `Moore57/Moore57Graph/Aut/`: 既存の Tier-2 abstract API. 大部分活用可.
  - `FixedCount.lean`: p=19 mod 補題群 (テンプレ).
  - `NeighborMod.lean`: σ-fix 近傍 mod p.
  - `InducedSubgraph.lean`: induced subgraph SRG 化.
  - `InvolutionCandidates.lean`: regular/star dichotomy.
- `Moore57/D19OnMoore57/Involution/HigmanCountArithmetic.lean`:
  Higman 算術 helpers (一般 σ で使用可).
- `Moore57/Order22OnMoore57/Phase3RepTheory.lean`: 既存の σ=11 trace 解析
  (ただし現状は σ_fix 依存; Stage 6 後に逆向き活用候補).
- `Moore57/Foundations/GraphTheory/StrongZeroOne.lean`:
  StrongZeroOne dichotomy.

## 6. 進め方の提案

1. **Stage 1**: ミラー作業として最初に着手. テンプレ既存で safe.
2. **Stage 2 → 3**: 並行可能. 共通の "ラージ" インフラに依存.
3. **Stage 4**: 単独で取り組み. Mathlib SRG infra 調査が前提.
4. **Stage 5, 6, 7, 8**: Stage 1-4 完了後に直線的に進行.

各 Stage 完了時に commit. Stage 7 完了時に Order22 全体の axiom check.

## 7. 期待される完了状態

- `Order22ActsOnMoore57` 構造体から全 conditional 入力削除.
- 主結果 `no_Order22_acts_on_Moore57` が **完全 unconditional**.
- `Order22ActsOnMoore57` 構造体の入力は raw 作用データのみ:
  - `isMoore : IsMoore57 Γ`
  - `σ : Equiv.Perm V`, `σ_aut`, `σ_pow_eleven`, `σ_ne_one`
  - `τ : Equiv.Perm V`, `τ_aut`, `τ_pow_two`, `τ_ne_one`
  - `στ_relation : σ * τ = τ * σ ∨ τ * σ * τ = σ⁻¹`

これにより, D19, C38, Order22 すべての主結果が同一の "raw action only" 入力で
記述され, Moore57 自己同型群の order 11/19/38/22 の不存在が完全形式化される.
