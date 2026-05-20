# Moore57 Papers/ 実装プラン (2026-05-21 深夜 起点)

`Moore57/Papers/` に **paper-faithful unconditional な実証明** を入れていく
段階の実装プラン。 B4.3 Step 4 full + Tier C 全閉 + Tier D 全閉が同日
完了し、大きな building block は揃った状態が出発点。

このドキュメントは proofs/moore57_roadmap_post_easy_wins.md を補完する
**実装フェーズ用 task list**。 ロードマップが「何が残っているか」を網羅する
のに対し、こちらは「これから何を順に作るか」を順序立てて記述。

---

## 0. 現状認識 (2026-05-21 深夜)

* `Moore57/Papers/` 全 86 files、60 files に `True := by trivial` skeleton 残存。
* **中身は組み上がっている**: arithmetic core / conditional dispatch /
  Section-level conditional はすべて proven。
* **ギャップ**: paper-faithful "全体" statement (例 `aut_card_le_375
  (hΓ : IsMoore57 Γ) : True := by trivial`) の unconditional 化。

  ⟹ "IsMoore57 Γ から各 Prop の入力仮定を生成する bridge" のみが残作業。

## 0.1 使える building block (大きな部品)

| Tier | 提供物 | 用途 |
|---|---|---|
| B4.1 | `aut_pow_prime_E7_trace_int` | prime-order σ の trace ∈ ℤ |
| B4.2 | Lem 12 p=3/7 starred unstub済 | starred row dispatch pattern 確立 |
| B4.3 Step 4 | `trace_int_of_pow_eq_one` (composite) | 任意 n で trace ∈ ℤ。 Step 5-6 で wire-up |
| B-final | `XConclusion : Prop` def 群 | hypothesis として使える Prop encode |
| C3.0-C3.6 | FixedData (Petersen, HS, C5, K155, Empty, Singleton) | Lem 17/18 fix shape 入力 |
| C3.4 | `orderOf_dvd_card_of_semiRegular` + wrappers | semi-regular ⟹ order divides |
| D2.x-D3.x | rank-3 perm group framework (Lem 1-7) | Higman 1964 §1 paper-faithful |
| D4.x | Aschbacher 1.4 combined Cor | involution dichotomy + (k, f) classification |
| E1-E5 | Sylow + Schur-Zassenhaus bridge | 各 Prop 6/7/8 の Sylow analysis |

---

## 1. Path B (推薦): Lem 21 + Lem 17/18 真の unconditional 化 ~ 3-4 commits

C3.4 で残した "semi-regular 自体" hypothesis を消す catalyst。 Paper
MS 2010 §6 Lem 21 (`Fix(σ^l) = Fix(σ)`)。

### 1.1 Mathlib 調査: `Fix(σ^l) = Fix(σ)` 周辺
- [x] `MulAction.fixedPoints` の `σ^l` 形と `σ` の関係を Mathlib で確認
- [x] `Equiv.Perm.support_pow_coprime` (既存使用) が l, orderOf σ coprime case
- [x] composite l (= 自明でない divisor) の paper-faithful form を要確認
- 入力: existing `Foundations/GroupAction/FixedPoints.lean` の `fixedVertexSet_subset_pow`
  (commit 既存) があるので、これと逆向き bridge が必要かを精査
- **結論**: 一般 `l` で `Fix(σ^l) = Fix(σ)` は **真でない** (`Fix(σ^l) ⊇ Fix(σ)`
  のみ)。 coprime case は Mathlib に存在、composite case は Lem 17 自体が必要
  になり循環。 → Phase 1.4/1.5 で別アプローチ要。 詳細は blogs/20260521.md。

### 1.2 Lem 21 (1): `Fix(σ^l) = Fix(σ)` for σ aut + l small
- [x] `Moore57/Papers/MacajSiran2010/Section07_Theorem4Proof/Lemma21_3GroupSingleFix.lean`
  (現在 True-stub) を proper-signature 化 — **`lem21_part1_subgroup_paper`,
  `lem21_part2_subgroup_paper` 追加** (Mathlib `Subgroup.index_mul_card` 経由)
- [~] 主形: σ^p^k = 1 + Fix(σ) singleton ⟹ Fix(σ^l) も singleton (l | p^k)
  → cyclic specialization は degenerate (cyclic group では任意 divisor で
  unique subgroup) のため、subgroup 形が paper-faithful。
- [x] Paper-faithful な 2 cases (paper §6, p=3): Lem 21 (1), (2)
- [x] backward-compat True-stub も保持

### 1.3 Semi-regular hypothesis generator
- [ ] Lem 21 を入力に、Lem 17/18 wrapper の `h_semi_regular : orderOf σ ∣ 54`
  を **生成** する形の補題:
  ```
  theorem semiRegular_orderOf_dvd_complement
      (h : <Lem 21 hypotheses>) : orderOf σ ∣ |N(a) \ Fix(σ)|
  ```
- [ ] `Moore57Graph/Aut/SemiRegularComplement.lean` (既存、C3.4) を拡張

### 1.4 Lem 17 case (1) 真の unconditional wrapper
- [ ] `Moore57/Papers/MacajSiran2010/Section06_PGroupsOverview/Lemma17_3Group.lean`:
  既存 `lem17_case1_orderOf_dvd_27_with_petersenFixedData_semiRegular` を
  「Lem 21 + PetersenFixedData だけから直接 `orderOf σ ∣ 27`」に upgrade
- [ ] Case (1), case (2)/(3) 同様の整理

### 1.5 Lem 18 case (1) 真の unconditional wrapper
- [ ] `Lemma18_5Group.lean` で同じ作業
- [ ] HS fix data + Lem 21 ⟹ `orderOf σ ∣ 25`

**完了条件**: Lem 17/18 の `_semiRegular` 接尾辞 wrapper が `(hΓ, σ, σ^pk=1)`
のみから入力を生成する形に。 上流 Prop 6/7/8 が unconditional 化可能に。

---

## 2. Path A: B4.3 Step 5-6 Moore57 wire-up ~ 2 commits

直前作業の自然な継続。 Lem 13 p=5 starred order-25 row を unstub。

### 2.1 σ ∈ Aut(Γ) → ℚ-linear endomorphism bridge
- [x] `Moore57Graph/Aut/TraceIntegrality.lean` 拡張:
  - 既存 `aut_pow_prime_E7_trace_int` (B4.1, p prime) と同様の structure で
  - **`aut_pow_E7_trace_int_composite`**: `σ^n = 1` (任意 n > 0) ⟹
    `Matrix.trace (E7Matrix Γ * permMatrix σ) ∈ ℤ` **追加完了**
- [x] B4.3 `trace_int_of_pow_eq_one` を applied:
  - `f := (E7Matrix.toLin').restrict (E7Range)`
  - σ^n = 1 ⟹ f^n = 1 on the range (既存 prime version の真の一般化)
  - `restrict_pow_apply` + `Matrix.toLin'_pow` パターン再利用

### 2.2 Lem 13 p=5 starred rows unstub
- [x] `Moore57/Papers/MacajSiran2010/Section05_Tables/Lemma13_PrimeSquared.lean`:
  - `lem13_starred_row_5_0_5_no_integer_trace` (現状 Tr hypothesis のまま, 既存 done)
  - `lem13_starred_row_5_5_5_no_integer_trace` (同上, 既存 done)
  - **`lem13_starred_row_5_0_5_no_aut_conditional`** 追加: graph-aut 入力
    `(hΓ, σ, hAut, σ^25 = 1)` + Prop 2 arithmetic 派生条件
  - **`lem13_starred_row_5_5_5_no_aut_conditional`** 同様 追加
  - `aut_pow_E7_trace_int_composite` を internal で利用 (trace ∈ ℤ 自動)
- [~] Lem 13 p=5 (0, 5), (5, 5) row が **conditional unconditional** に
  (Prop 2 deferred は明示)
- 完全 unconditional 化は Prop 2 (paper §4 character system) の Lean 化必要。
  Prop 2 自体は `prop2_character_system : True := trivial` (deferred-heavy)。

**完了条件**: Lem 13 starred row のうち p=5 order-25 σ 関連が unstub、
Lem 13 全 row が unconditional に近づく (残るは composite-order の他 row)。

---

## 3. Path D: True-stub audit harvest ~ 1-2 commits

直前の B4.3 / C3.4 / D3.x / D4.x で建てた building block を使って
即一発で proof-position 化できる True-stub を harvesting。

### 3.1 候補 grep + 内容確認
- [ ] `grep -rn "True := by trivial\|True := trivial" Moore57/Papers/` の 60 件を
  3 category に分類:
  - (a) Lem 21 待ち (Path B 完了で消える) - 推定 8-12 件
  - (b) 既存 building block で即 unstub 可能 - 推定 5-10 件 (要 audit)
  - (c) Tier A 待ち (見送り) - 推定 4-6 件 (SG(81,9), SG(625,12) 関連)
  - (d) Prop 2 / Theorem 3 全形待ち (deferred-heavy) - 残り

### 3.2 候補先行調査 (即 unstub 可能か)
- [ ] `Section02_StateOfTheArt/Lemma1_*` (Aschbacher D4.x の application)
- [ ] `Section03_EquitablePartitions/Lemma6_OrbitTrace.lean` (Tier D Lem 5/6/7 経由)
- [ ] `Higman1964/MainTheorem.lean` (D3.6 Theorem 1 full bridge 経由)
- [ ] `Aschbacher1971/MainTheorem.lean` (D4.1 combined Cor 経由)
- [ ] `CameronCh3/Section07_Automorphisms.lean` (既に substantive proof あり、True-stub 周辺だけ)

**完了条件**: 5-10 件の True-stub が 1-2 commits で unstub。 状態 cleanup
効果。

---

## 4. Path C: Cor 3 climbing (planning only) ~ planning document

Cor 3 (= `|Aut(Γ)| ≤ 375`) から逆算する。 これは Tier A 投資を見送る前提で、
「achievable subgoal」を identify する planning 作業 (Lean コード変更なし)。

### 4.1 Thm 6 (odd) 経路の dependency tree
- [ ] `cor3_bound_from_props_and_oddpart` (proven) → `Odd n` 仮定で
  Props 6/7/8 dispatch 必要
- [ ] Prop 6 (3, 5) unconditional 化に必要な True-stub の最小集合
- [ ] Prop 7 (3, q≥7) 各 q
- [ ] Prop 8 (5, q≥7) 各 q
- [ ] Lem 26 (p ≤ 5 or q ≤ 5) — Sylow + Mathlib

### 4.2 Thm 7 (even) 経路の dependency tree
- [ ] Thm 7 dispatch unconditional 化
- [ ] |G| = 110 = 2·5·11 case (E4.0 proven、unconditional 化 path 確認)
- [ ] |G| = 50, 54, 14, 22, 38 各 case

### 4.3 Thm 4 / Thm 5 経路 (Tier A 経由)
- [ ] Thm 4 = 3-group bound: Cor 2 (SG(81,9)) 必須 → Tier A 投資非推奨
- [ ] Thm 5 = 5-group bound: Lem 22 (SG(625,12)) 必須 → 同上
- [ ] 代替経路があるか調査 (Path B (Lem 21) で部分的に bypass 可能か?)

### 4.4 最小 achievable subgoal の特定
- [ ] Tier A 経由抜きで Cor 3 unconditional 化が無理なら、achievable な
  subgoal (例: `|Aut(Γ)| ≤ 375 conditional on no_3group_order_81 ∧ no_5group_order_625`)
  の paper-faithful な statement を整理
- [ ] このとき hypothesis として何を Prop def に encode するかを決定

**完了条件**: `proofs/moore57_cor3_path_analysis.md` (新規) として保存。
Lean コード変更ゼロ。

---

## 5. 投資非推奨 (Tier A) の取り扱い

`A1.2` (SG(81,9) uniqueness, 15 群構築), `A3` (SG(625,12) uniqueness, 10 群構築),
`A4` (Prop 4 paper arithmetic) は downstream consumer 無しで投資非推奨。

* 関連 True-stub は backward-compat shell として残置
* 将来 Mathlib に `IsPGroup` p⁴ classification が追加される or hand-roll が
  ROI 確保される時まで放置

---

## 推薦実行順序

1. **Path B** (Lem 21 + Lem 17/18 真の unconditional) — catalyst 効果大、
   ~3-4 commits
2. **Path A** (B4.3 Step 5-6 wire-up) — B4.3 完結、~2 commits
3. **Path D** (True-stub audit harvest) — Path B/A 完了後の cleanup、~1-2 commits
4. **Path C** (Cor 3 climbing planning) — Path B 完了後に状態を見て判断

合計見積もり: 6-9 commits で Papers/ の主要不足分が片付く見込み。
Tier A 投資を見送る限り Cor 3 unconditional は依然遠いが、Thm 6 経路の
unconditional 化は手の届く範囲。

---

## 関連ドキュメント

* `proofs/moore57_roadmap_post_easy_wins.md` — Tier A-F 別の細粒度
  ロードマップ (canonical living document)
* `proofs/moore57_d19_lean_aware_proof.md` — 自然言語証明 (原典)
* `tmp/pdfs/j.laa.2009.07.018.txt` — Mačaj–Širáň 2010 原文 (paper-faithful の
  根拠)
