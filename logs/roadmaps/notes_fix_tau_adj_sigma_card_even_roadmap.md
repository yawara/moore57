# Order22: `fix_τ_adj_σ_card_even` 解消のための形式化方針

最終更新: 2026-05-17

## 目的

`Moore57/Order22OnMoore57/Action.lean` の `Order22ActsOnMoore57` 構造体フィールド

```lean
fix_τ_adj_σ_card_even : 2 ∣ (Finset.univ.filter
    (fun x : V => τ x = x ∧ Γ.Adj x (σ x))).card
```

を raw action (= σ_aut, τ_aut, σ_pow_eleven, τ_pow_two, στ_relation, σ_fix, τ_fix) から
導出可能にし、構造体フィールドから削除する。

`τ_fix : K155FixedData` は `aut_involution_nonempty_K155FixedData`
([InvolutionFixIsK155.lean:348](Moore57/Moore57Graph/Aut/InvolutionFixIsK155.lean#L348))
で raw から構成可能なので、この issue では一旦 `τ_fix` フィールドはそのまま
利用してよい (別タスクで τ_fix も廃止)。

## 自然言語証明 §5.2 の核と parity への簡略化

§5.2 完全版 (`|Fix(π_d) ∩ L| = 2` を slope d ごとに) は重い。**parity だけで充分**
であることを利用し、以下の論証で済ます (~150 行短縮):

```
ρ_1 := θ ∘ π_1 : F_0 → F_0  -- involution (Step 14)
|F_0| = 56 (even)
|Fix(ρ_1)| ≡ |F_0| ≡ 0 (mod 2)  -- 一般 involution parity
Fix(ρ_1) ⊂ L                    -- p, q ∉ Fix(ρ_1) (no-4-cycle)
Fix(ρ_1) = Fix(π_1) ∩ L         -- L 上 θ = id
Fix(π_1) ∩ L = L ∩ S            -- matching characterization
|Fix(τ) ∩ S| = |L ∩ S|          -- x_0, u_τ ∉ S
```

### Cyclic case

既に sorry-free (`cyclic_no_τ_fixed_adj_σ` で 0 を直接示す、
[Parity.lean:85-107](Moore57/Order22OnMoore57/Parity.lean#L85-L107))。
今回の作業は **dihedral case 専用**。

## 既存インフラ (再利用可)

| 部品 | 場所 |
|------|------|
| `branchFiber`, `branchFiber_card = 56` | `Moore57Graph/Moore57Definition.lean:91, 103` |
| `branchFiberMatchingEquiv` | `Moore57Graph/BranchFiber/Matching.lean:56` |
| `no_triangle`, `no_four_cycle` | `Moore57Graph/Moore57Definition.lean:38, 56` |
| `existsUnique_branch_of_not_adj_center` | `Moore57Graph/Moore57Definition.lean:130` |
| `of_not_adj` (μ = 1) | Moore57Definition |
| `two_dvd_support_card_of_involutive` | `Foundations/GroupAction/InvolutionParity.lean:20` |
| `Equiv.Perm.card_compl_support_modEq` | Mathlib |
| `τ_preserves_σ_fix` | `Order22OnMoore57/BasicStructure.lean:242` |
| `dihedral_τσ_eq_σinv_τ_apply` | `Order22OnMoore57/BasicStructure.lean:131` |
| `dihedral_τ_σ_pow` | `Order22OnMoore57/BasicStructure.lean:148` |

D_19 の `Reflection.lean` 系は 19-cycle reflection-copy 議論に特化し直接再利用は薄い。

## 詳細ステップ

以下の **15 ステップ**を 6 つの新規ファイルに振り分ける。

### Step 1. τ\|Fix(σ) は反射 (1 fixed point)
- `τ_preserves_σ_fix` から τ は Fix(σ) を保つ。
- τ は involution、Fix(σ) は 5 元 ⟹ |Fix(τ\|Fix(σ))| は奇数 (parity)、∈ {1, 3, 5}。
- **case 5 排除**: Fix(σ) ⊂ Fix(τ) ⟹ 5-cycle が K_{1,55} 内 ⟹ 矛盾 (K_{1,55}
  は cycle を含まない)。
- **case 3 排除**: τ\|C_5 は C_5 の graph aut かつ involution。Aut(C_5) ≅ D_5,
  involutions = 5 reflections (1 fixed each) + identity (5 fixed)。3 fixed は無い。
  - 形式化方法: τ-fixed vertex `u_τ` を 1 つ選ぶ → 隣接 a_τ, d_τ の像が
    {a_τ, d_τ} 内 → 2 cases (両方 fix / 互いに swap) → それぞれ案分.
- 帰結: 一意の τ-fixed vertex `u_τ` が存在し、cycle 隣接 `a_τ = next(u_τ)`,
  `d_τ = prev(u_τ)` は τ で swap、`b_τ = next^2(u_τ)`, `c_τ = prev^2(u_τ)` も swap.

### Step 2. K_{1,55} center は B_0 内 (length-11 σ-orbit)
- u_τ ∈ Fix(τ)、leaf or center?
- **u_τ は leaf 仮定**: x_0 := τ_fix.center, x_0 ≠ u_τ。
- **u_τ が center だと矛盾**: center は 55 leaves と adj。N(u_τ) \ {a_τ, d_τ}
  は 55 vertices in 5 length-11 σ-orbits in N(u_τ)。τ permutes 5 orbits, fix
  数 ∈ {1, 3, 5}。fix された orbit は reflection 作用で 1 fixed point。
  Total τ-fixed neighbors of u_τ = #τ-stable orbits ≤ 5。Center claim は 55、矛盾.
- ⟹ u_τ は K_{1,55} の leaf, x_0 ≠ u_τ.

### Step 3. x_0 ∈ N(u_τ) かつ x_0 ∉ Fix(σ)
- x_0 = center, u_τ = leaf ⟹ x_0 ~ u_τ ⟹ x_0 ∈ N(u_τ).
- Fix(σ) ∩ Fix(τ) ⊂ Fix(σ) ∩ {u_τ ∈ leaves} ∪ {x_0}. x_0 ∈ Fix(σ) なら
  Fix(σ) ∩ Fix(τ) ⊃ {u_τ, x_0}, |∩| ≥ 2, 矛盾 (Step 1 で = 1)。
- ⟹ x_0 ∉ Fix(σ), σ-orbit of x_0 (= B_0) は length 11.

### Step 4. N(u_τ) は σ-stable、B_0 ⊂ N(u_τ)
- σ(u_τ) = u_τ ⟹ ∀ x, x ~ u_τ ↔ σ x ~ u_τ。
- B_0 = {σ^i x_0 : i ∈ ZMod 11} ⊂ N(u_τ).

### Step 5. F_0 := branchFiber Γ u_τ x_0, F_1 := branchFiber Γ u_τ (σ x_0)
- σ x_0 ∈ N(u_τ) ✓、σ x_0 ≠ x_0 (length 11)。
- |F_0| = |F_1| = 56。
- σ(F_0) = F_1: σ(N(x_0) \\ {u_τ}) = N(σ x_0) \\ {u_τ} = F_1. (σ aut + σ u_τ = u_τ).

### Step 6. F_0 は τ-stable
- τ(x_0) = x_0, τ(u_τ) = u_τ ⟹ τ(N(x_0) \ {u_τ}) = N(x_0) \ {u_τ}.

### Step 7. p, q ∈ F_0 の定義と性質
- 定義: p = unique vertex in N(b_τ) ∩ N(x_0), q = unique in N(c_τ) ∩ N(x_0).
- 一意性: b_τ ≠ x_0 (Fix(σ) ∩ Fix(σ)^c)、b_τ ≁ x_0 (証明: 
  b_τ ~ x_0 + b_τ ~ u_τ false ⟹ {a_τ} = N(b_τ) ∩ N(u_τ) に x_0 が入る ⟹
  x_0 = a_τ ∈ Fix(σ) 矛盾)。よって Moore57 μ=1 で
  `existsUnique_branch_of_not_adj_center` 適用可。同様 c_τ.
- p, q ∈ N(x_0) かつ p ≠ u_τ (なぜなら p ∈ N(b_τ) かつ u_τ ∉ N(b_τ))、
  同様 q ≠ u_τ ⟹ p, q ∈ F_0.
- p ≠ q: p ∈ N(b_τ) ∖ N(c_τ) (since b_τ ≠ c_τ and Moore57 μ=1 unique).

### Step 8. τ(p) = q, τ(q) = p
- τ(N(b_τ) ∩ N(x_0)) = N(τ b_τ) ∩ N(τ x_0) = N(c_τ) ∩ N(x_0) = q.

### Step 9. Fix(τ\|F_0) = L := F_0 \ {p, q}, |L| = 54
- Fix(τ\|F_0) ⊆ F_0 ∩ Fix(τ) = F_0 ∩ ({x_0, u_τ} ∪ leaves).
  - x_0 ∉ F_0 (irreflexivity).
  - u_τ ∉ F_0.
  - leaves: 55 elements, all in N(x_0). 1 of them = u_τ ∉ F_0. 残り 54.
- ⟹ Fix(τ\|F_0) ⊆ {54 leaves}. p, q ∉ Fix(τ\|F_0) (Step 8: τ swaps).
- {54 leaves} ⊆ Fix(τ\|F_0): each leaf is τ-fixed and in F_0.
- ⟹ Fix(τ\|F_0) = 54 leaves, |L| = 54, |F_0 \ L| = 2 = |{p, q}|.

### Step 10. m_1 : F_0 ≃ F_1 (matching)
- `branchFiberMatchingEquiv hΓ (σ x_0 ∈ N(u_τ)) (x_0 ∈ N(u_τ)) hne_swap`.
- subtype-valued: `{y // y ∈ F_0} ≃ {y // y ∈ F_1}`.

### Step 11. π_1 : F_0 → F_0 とその性質
- `π_1(y) := σ^{-1}(m_1(y).val)` as element of V, then show ∈ F_0.
- subtype 上の関数として `π_1 : {y // y ∈ F_0} → {y // y ∈ F_0}` を定義。
- **核心特性**: y ∈ F_0 で `π_1(y) = y ↔ y ~ σ(y)`.
  - π_1(y) = y ↔ σ^{-1}(m_1(y).val) = y ↔ m_1(y).val = σ(y) ↔ y ~ σ(y)
    (σ y ∈ F_1 + matching の adjacency).

### Step 12. τ ∘ π_1 = π_{-1} ∘ τ on F_0
- Dihedral: τσ^{-1} = στ (from τστ = σ^{-1}).
- For y ∈ F_0:
  τ(π_1(y)) = τ(σ^{-1} m_1(y)) = σ(τ(m_1(y))) = σ(m_{-1}(τ(y))) = π_{-1}(τ(y)).
  - τ(m_1(y)): m_1(y) ∈ F_1, τ(m_1(y)) ∈ τ(F_1) = F_{-1}. matching of τ(y) ∈ F_0
    in F_{-1} = m_{-1}(τ(y)).

### Step 13. π_{-1} = π_1^{-1}
- For y ∈ F_0: π_1^{-1}(y) = z s.t. m_1(z) = σ(y), z = m_1^{-1}(σ y).
- π_{-1}(y) = σ(m_{-1}(y)).
- m_1^{-1}(σ y) = σ(m_{-1}(y)) by σ-equivariance of matching: m_{-1}(y) ~ y
  ⟹ σ(m_{-1}(y)) ~ σ(y), with σ(m_{-1}(y)) ∈ F_0, σ(y) ∈ F_1, so matched.

### Step 14. ρ_1 := θ ∘ π_1 is involution on F_0
- ρ_1 = τ\|F_0 ∘ π_1.
- ρ_1² = τ π_1 τ π_1 = π_{-1} τ τ π_1 = π_{-1} π_1 = π_1^{-1} π_1 = id.

### Step 15. p, q ∉ Fix(ρ_1) ⟹ Fix(ρ_1) ⊂ L
- p ∈ Fix(ρ_1) ↔ ρ_1(p) = p ↔ τ(π_1(p)) = p ↔ π_1(p) = τ(p) = q.
- π_1(p) = q ⟹ m_1(p) = σ(q) ⟹ p ~ σ(q).
- σ(q) ∈ N(σ c_τ) ∩ N(σ x_0) = N(c_τ) ∩ N(x_1) (σ fixes c_τ).
- **4-cycle**: b_τ ~ p ~ σ(q) ~ c_τ ~ b_τ. 4 頂点相異:
  - b_τ ≠ p (irrefl), p ≠ σ(q) (irrefl), σ(q) ≠ c_τ (irrefl), c_τ ≠ b_τ (5-cycle).
  - b_τ ≠ σ(q): σ(q) ∈ N(x_1). b_τ ∈ N(x_1) を仮定すると x_1 ∈ N(b_τ) ∩ N(u_τ) = {a_τ}
    ⟹ x_1 = a_τ ∈ Fix(σ), 矛盾.
  - c_τ ≠ p: 対称的に c_τ ~ x_0 を仮定すると x_0 ∈ N(c_τ) ∩ N(u_τ) = {d_τ}
    ⟹ x_0 = d_τ ∈ Fix(σ), 矛盾. よって c_τ ∉ N(x_0), p ∈ N(x_0) で c_τ ≠ p.
- `no_four_cycle` で矛盾. ⟹ p ∉ Fix(ρ_1).
- q ∉ Fix(ρ_1): 対称的 (b_τ ↔ c_τ, p ↔ q swap で同じ証明).

### 結論合成

```
|Fix(ρ_1)| ≡ |F_0| = 56 ≡ 0 (mod 2)           -- Step 14 + involution parity
Fix(ρ_1) ⊂ L                                    -- Step 15
Fix(ρ_1) ∩ L = Fix(π_1) ∩ L                     -- L 上 θ = id
                = L ∩ S (≡ {y ∈ L : y ~ σ y})   -- Step 11
⟹ |L ∩ S| ≡ 0 (mod 2)
|Fix(τ) ∩ S| = |L ∩ S| + |{x_0, u_τ} ∩ S|
            = |L ∩ S|                            -- x_0, u_τ ∉ S (下記)
            ≡ 0 (mod 2)
```

**x_0 ∉ S**: x_0 ∈ B_0 ⊂ N(u_τ), σ(x_0) ∈ N(u_τ), no edges in N(u_τ)
(triangle prohibition).

**u_τ ∉ S**: σ(u_τ) = u_τ, no loops.

## ファイル分割 (新規作成)

`Moore57/Order22OnMoore57/Dihedral/` サブディレクトリ案 (または平置き):

| # | ファイル | Step | 行数 |
|---|----------|------|------|
| 1 | `DihedralC5Reflection.lean` | 1 | ~150 |
| 2 | `DihedralCenterInNeighborhood.lean` | 2, 3, 4 | ~150 |
| 3 | `DihedralF0Structure.lean` | 5, 6, 7, 8 | ~200 |
| 4 | `DihedralLDefinition.lean` | 9 | ~80 |
| 5 | `DihedralPiOneInvolution.lean` | 10, 11, 12, 13, 14 | ~250 |
| 6 | `DihedralParity.lean` | 15 + 結論合成 | ~150 |

合計 ~980 行 (overestimate; 実装中に整理で減るはず).

最後に:
- `Parity.lean` の `traceNumber_even_of_dihedral` 内の
  `h.fix_τ_adj_σ_card_even` 参照を新しい
  `dihedral_fix_τ_adj_σ_card_even` 補題への参照に置き換え.
- `Action.lean` から `fix_τ_adj_σ_card_even` フィールドを削除.
- Cyclic case の `cyclic_no_τ_fixed_adj_σ` も同じ補題スタイル
  `cyclic_fix_τ_adj_σ_card_even` に展開 (parity = 0 だけを expose).

## 技術的注意点

### A. C5FixedData の Fin 5 再ラベリング

`h.σ_fix.v : Fin 5 → V` で `h.u = v 0` 等が決まっているが、τ-fixed
vertex は別の `v i_τ` かもしれない。`u_τ`, `a_τ`, `b_τ`, `c_τ`, `d_τ` は
`v (i_τ + k)` 形で定義. cyclic Fin 5 演算 `+ 1`, `- 1`, `+ 2`, `- 2`
(= `+ 3`) を活用.

### B. Subtype coercion

`branchFiber Γ u b : Finset V` の要素は `{y // y ∈ branchFiber Γ u b}` で扱う.
`branchFiberMatchingEquiv` も subtype 型. `π_1` を subtype 上の関数
`{y // y ∈ F_0} → {y // y ∈ F_0}` として定義し、必要時に `.val` で V に降ろす.

### C. Fix(τ) ∩ F_0 = 54 leaves の数え上げ

`h.τ_fix.leaf : Fin 55 → V` を使い、`Fin 55` のうち leaf u_τ に対応する
index `j_τ` を取り出し (一意性は `K155FixedData.center_ne_leaf` +
`leaf_injective`), L = image of `Fin 55 \ {j_τ}` で構成.

または abstract に `Fix(τ\|F_0).card = (K_{1,55} leaves).card - 1 = 54`
を組み上げる.

### D. matching m_1 の σ-equivariance

Step 13 で `m_1^{-1}(σ y) = σ(m_{-1}(y))` を使う。これは
"matching が σ-action と可換" を意味し、Moore57 SRG の対称性 (μ=1 で
matching が unique) から従う. `branchFiberMate_eq_of_adj` で
characterize.

### E. Action.lean フィールド削除時の cyclic case 整合

`cyclic_no_τ_fixed_adj_σ` から `cyclic_fix_τ_adj_σ_card_even`
(parity = 0 で even) を組み立て、dihedral 版と同じ shape で
`dihedral_fix_τ_adj_σ_card_even` を提供. Parity.lean 内で
`rcases h.στ_relation with hcomm | hdihe` で case 分岐済みなので
そのまま差し替え可.

## 工数見積もり

- 詰めの議論はほぼ完了 (この roadmap 参照)。
- 純粋な Lean 実装作業として ~1000 行、10-20 セッション程度.
- D_19 関連 D_19 ファイルとの構造比較が比較的近い (involution parity +
  4-cycle 排除) ので、コーディング技法は流用可能.

## 進め方の選択肢 (再掲)

1. **6 ファイル一気に scaffolding (sorry で型のみ供給) → 1 つずつ閉じる**
   全体像が早く見える。後で順序を組み替えやすい。

2. **1 ファイルずつ sorry-free に完成させてから次へ**
   確実だが時間がかかる。早期に技術的ブロックがあると後手。

3. **exact 2 まで証明**
   parity だけで充分なので over-engineering. 別途やる価値はあるが
   今回は parity 経路推奨.

推奨: **(1) scaffolding 先行**. Step 1 (DihedralC5Reflection) と
Step 10-14 (DihedralPiOneInvolution) が技術的に最も重いので、
これらを先に skeleton 化して感触をつかむと良い.
