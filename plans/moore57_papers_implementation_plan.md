# Moore57 Papers/ 実装プラン (2026-05-21 深夜 起点)

`Moore57/Papers/` に **paper-faithful unconditional な実証明** を入れていく
段階の実装プラン。 B4.3 Step 4 full + Tier C 全閉 + Tier D 全閉が同日
完了し、大きな building block は揃った状態が出発点。

このドキュメントは plans/moore57_roadmap_post_easy_wins.md を補完する
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
- [x] **prime case 完了 (Path B)**: `Foundations/GroupAction/SemiRegularPrimeOrder.lean`
  新規 + `SemiRegularComplement.lean` 拡張:
  - `semiRegular_at_movedPoint_of_prime_orderOf`: σ^p = 1 (p prime)
    + σ w ≠ w ⟹ σ^k w = w → orderOf σ ∣ k. Mathlib
    `Equiv.Perm.support_pow_coprime` 経由で hand-roll。
  - `aut_semiRegular_at_movedNeighbor_of_prime`: graph-aut bridge
    on `autMovedNeighborFinset`。
  - `orderOf_dvd_card_movedNeighbour_of_prime`: combined bridge
    (σ^p = 1 + fixed `a` ⟹ orderOf σ ∣ |N(a) \ Fix(σ)|, no hsemi)。
- [x] Lem 17 (case 1, 2) + Lem 18 (case 1, 2, 3) の各 `_prime_via_semiRegular_unconditional`
  wrapper: σ^p = 1 + FixedData + smul_adj のみから paper bound を導出
  (hsemi は internal で自動生成)。
- [ ] **composite case (k ≥ 2) は依然 deferred**: σ^p が σ より多くを固定し得る
  ため、paper Lem 21 + Cor 2 / Prop 3 / Lem 22 / Prop 4 が必要 (deferred-heavy)。

### 1.4 Lem 17 case (1) 真の unconditional wrapper
- [x] `Moore57/Papers/MacajSiran2010/Section06_PGroupsOverview/Lemma17_3Group.lean`:
  既存 `lem17_case1_orderOf_dvd_27_with_petersenFixedData_semiRegular` の
  unstub。 paper-stated bound 範囲を unconditional 化:
- [x] **Prime case (k=1)**:
  `lem17_case1_orderOf_dvd_27_with_petersenFixedData_prime_unconditional`
  (Petersen) + `lem17_case2_orderOf_dvd_3_with_singletonFixedData_prime_unconditional`
  (Singleton, C3.4 sharper bound)
- [x] **k ≤ 3 (case 1)**:
  `lem17_case1_orderOf_dvd_27_with_petersenFixedData_k_le_3_unconditional` —
  σ ∈ orderOf ∈ {1, 3, 9, 27} 全て unconditional ∣ 27
- [x] **k ≤ 4 (case 2 paper-stated ∣ 81)**:
  `lem17_case2_orderOf_dvd_81_with_singletonFixedData_k_le_4_unconditional` —
  σ ∈ orderOf ∈ {1, 3, 9, 27, 81} 全て unconditional ∣ 81
- 残り: **k ≥ 4 (case 1), k ≥ 5 (case 2)**: orderOf σ がそれぞれ
  case bound (27, 81) を超えるので、 これは paper Lem 21 + Cor 2 (SG(81, 9))
  exclusion 必要 (deferred-heavy)。

### 1.5 Lem 18 case (1) 真の unconditional wrapper
- [x] `Lemma18_5Group.lean` で同じ作業
- [x] **Prime case (k=1)**: 3 cases (HS / pentagon / empty)
  全て `lem18_case*_orderOf_dvd_*_with_*FixedData_prime_unconditional` 追加 —
  `orderOf σ ∣ 5 ∣ {25, 5, 125}` 自明
- [x] **k ≤ 2 (case 1 ∣ 25)**:
  `lem18_case1_orderOf_dvd_25_with_HSFixedData_k_le_2_unconditional` —
  σ ∈ orderOf ∈ {1, 5, 25} 全て unconditional ∣ 25
- [x] **k ≤ 3 (case 3 ∣ 125)**:
  `lem18_case3_orderOf_dvd_125_with_emptyFixedData_k_le_3_unconditional` —
  σ ∈ orderOf ∈ {1, 5, 25, 125} 全て unconditional ∣ 125
- 残り: **case 1 k ≥ 3, case 2 k ≥ 2, case 3 k ≥ 4**: orderOf σ が
  case bound を超えるので、 paper Prop 3 (HS exclusion ≥ 125), Lem 22 + Prop 4
  (Empty exclusion = 625) 必要 (deferred-heavy)。

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
- [x] `grep -rn "True := by trivial\|True := trivial" Moore57/Papers/` で 94 件
- [x] 3 category に分類:
  - (a) Lem 21 待ち (Path B 完了で消える) - 推定 8-12 件
  - (b) 既存 building block で即 unstub 可能 - 推定 5-10 件 (今回 4-5 件 unstub)
  - (c) Tier A 待ち (見送り) - 推定 4-6 件 (SG(81,9), SG(625,12) 関連)
  - (d) Prop 2 / Theorem 3 全形待ち (deferred-heavy) - 残り

### 3.2 候補先行調査 (即 unstub 可能か) — done

このセッションで proper-signature 化した True-stub 群 (各々 backward-compat
True-stub も保持):

- [x] **`Higman1964/Lemma01_PairedOrbits.lean`**: `lem1_paired_orbit_iff_even_of_faithful`
  追加 (Cauchy + 既存 directions の合成、faithfulness 入力条件付き)
- [x] **`Section03_EquitablePartitions/Lemma8_TraceMod15.lean`**:
  `lem8_trace_mod_fifteen_paper` 追加 (spectrum 入力 + 既存 zmod arithmetic)
- [x] **`Section03_EquitablePartitions/Lemma6_OrbitTrace.lean`**:
  `lem6_inducedTrace_sq_lt_card_dispatch` 追加
  (|O| ∈ {1,2,3,4} or ≥ 64 dispatch)
- [x] **`Section05_Tables/Lemma14_SemiRegularCongruence.lean`**:
  `lem14_semi_regular_congruence_paper` 追加 (congruence + decomp 合成)
- 加えて Phase 1.2 で `Lemma21_3GroupSingleFix.lean` の 2 件 (part 1 / part 2)
  + Phase 2.2 で `Lemma13_PrimeSquared.lean` の 2 件 (starred row aut conditional)
  = **合計 8 件** proper-signature 化。

**完了条件**: 5-10 件の True-stub が 1-2 commits で unstub。 **大幅超過達成 (合計 25+ 件)**。

### 3.3 このセッション中の True-stub harvest 累計

Higman 1964:
- Lem 1 `_of_faithful` (iff with faithfulness)
- Lem 2 `_paper` (intersection number identity)
- Lem 3 `_paper` (k = l under odd order)
- Lem 4 `_paper_contrapositive` (imprimitivity)
- Lem 4 Cor `_moore57_primitive_arith` + `_odd_n_kplus1_dvd_k_even`
- Lem 5 `_paper` (SRG `μ(n-k-1) = k(k-λ-1)`), Cor 2 `_arithmetic`, Cor 3 `_arithmetic`
- Lem 6 `_paper` (eigenvalue characterization)
- Lem 7 `_paper` (Moore parameter divisibility)
- Theorem 1 `_paper` (Case I/II disjunction)

Mačaj-Širáň 2010:
- Lem 21 part 1/2 `_subgroup_paper`
- Lem 16 `_pgroup_fix_shape_paper` (5-case N(a) dispatch)
- Lem 17 case 1/2 `_prime_unconditional`, case 1 `_k_le_3`, case 2 `_k_le_4`
- Lem 18 case 1/2/3 `_prime_unconditional`, case 1 `_k_le_2`, case 3 `_k_le_3`
- Lem 19 `_large_prime_pgroup_paper` (4-case dispatch)
- Lem 13 starred row 5_0_5, 5_5_5 `_no_aut_conditional`
- Lem 8 `_paper` (spectrum→mod 15)
- Lem 6 dispatch (size 1-4 ∨ ≥64)
- Lem 14 `_paper` (semi-regular congruence)
- Lem 15 starred row pq=35 `_paper` (trace contradiction)
- Lem 23 `_paper` (stabilizer order)
- Lem 24 `_paper` (j ≥ 2)
- Lem 25 `_paper_normal_sylow_action` (Q-action on Fix(P))
- Lem 26 `_paper` (p ≤ 5 ∨ q ≤ 5)
- Prop 3 `_prime_unconditional`
- Prop 5 `_paper` (three-case dispatch)
- Prop 6/7/8 `_paper` (mixing primes dispatch)
- Thm 4 + Thm 5 `_paper` (Section 6 group bounds)
- Thm 4 Final + Thm 5 Final `_paper` (Section 7/8 wrappers)
- Thm 6/7 `_paper` (odd/even order dispatch)
- Cor 3 `_paper` (375 bound dispatch)
- Main `aut_card_le_375_paper` (top-level headline)

Makhnev-Paduchikh 2001:
- Lem 3 `_paper` (global Fix dispatch)
- Main `_decomposition_paper` (|Y| ≤ 57 dispatch)

Section 04 (Characters, conditional re-exports):
- Thm 3 `_rational_classes_paper` (`Theorem3RationalClasses` hypothesis 経由)
- Prop 2 `_character_system_paper` (`Proposition2CharacterSystem` hypothesis 経由)

Section 05 (Tables, abstract Conclusion instances):
- Lem 12 `_prime_table_paper` (`Lemma12PrimeTableConclusion` instance)
- Lem 13 `_prime_squared_table_paper` (`Lemma13PrimeSquaredConclusion` instance)

加えて B4.3 composite trace + Moore57 wire-up (Phase 2.1) と
`aut_pow_E7_trace_int_composite` の追加で **paper §5 Lem 13 starred
row が conditional unstub に到達**。

---

## 4. Path C: Cor 3 climbing — dependency tree concrete-ization

Cor 3 (= `|Aut(Γ)| ≤ 375`) から逆算した **具体的 dependency tree**。
Tier A (SG(81,9) / SG(625,12) uniqueness, 25 群 enumeration) を見送る前提で
"achievable subgoal" を identify する planning 作業 (Lean コード変更なし)。

### 4.0 Top-level chain (already proven, conditional)

```
cor3_375_bound (hΓ : IsMoore57 Γ) : True
  ← cor3_bound_from_props_and_oddpart                   [proven, conditional]
       (Section09/Corollary3_375Bound.lean:132)
        ← thm6_bound_375_from_props                     [proven, conditional]
            (Section09/Theorem6_OddOrder.lean:72)
        ← thm7_bound_110_from_odd_part                  [proven, conditional]
            (Section09/Theorem7_EvenOrder.lean:66)
```

**鍵となる事実**: arithmetic backbone は全て proven。 残る True-stub は
"`hΓ : IsMoore57 Γ` から hypothesis dispatch を引き出す bridge" のみ。
具体的に必要なのは:

- **odd branch**: `Odd (Nat.card (autSubgroup Γ)) → Props 6/7/8 dispatch`
- **even branch**: `Even (Nat.card (autSubgroup Γ)) → ∃ m, ... ∧ Thm-7 odd-part dispatch`

### 4.1 §4.1 Thm 6 (odd) 経路の dependency tree

**Top True-stub**: `S9.thm6_odd_order (hΓ : IsMoore57 Γ) : True`
(Section09/Theorem6_OddOrder.lean:150)

**必要 dispatch hypothesis (consumed by `thm6_bound_375_from_props`)**:
```
n = Nat.card (autSubgroup Γ), n odd ⟹
   (n ∣ 135 ∨ n ∣ 375)                            -- Prop 6 (3, 5) 経由
 ∨ (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171)                   -- Prop 7 (3, q∈{7,13,19}) 経由
 ∨ (n ∣ 35 ∨ n ∣ 275)                             -- Prop 8 (5, q∈{7,11}) 経由
```

**Single-prime fallback** (Lems 16-19; ≤ |G| ≤ 27,125,49,11,13,19 各 p^k):
`thm6_dvd_one_of_seven_from_props_and_one_prime` (proven)
が 1-prime branch を absorb 済 — 個別 p の divisibility は all-cases-covered。

#### 4.1.A Minimum True-stub 集合 (Prop 6 unconditional 化)

**File**: `Section09_MixingPrimes/Proposition6_3and5.lean`
**Top True-stub**: `prop6_3_and_5 : True := by trivial` (line 241)

**Necessary True-stub chain (Prop 6, p=3, q=5 dispatch)**:

| Stub name                                          | File                                                | Status         | Required infra                                                |
|----------------------------------------------------|-----------------------------------------------------|----------------|---------------------------------------------------------------|
| `prop6_3_and_5` (top)                              | Section09/Proposition6_3and5.lean:241                | True-stub      | dispatch (a, b) extraction from `hΓ`                          |
| `lem17_3group_fix` (Fix shape)                     | Section06/Lemma17_3Group.lean:415                   | True-stub      | Path B Lem 21 (composite-order), Tier A Cor 2                 |
| `lem18_5group_fix` (Fix shape)                     | Section06/Lemma18_5Group.lean:`*_5group_fix`        | True-stub      | Path B Lem 21 (composite-order), Tier A Lem 22                |
| `cor2_smallGroup_81_9` (Cor 2)                     | Section07/Corollary2_SmallGroup81_9.lean:46         | True-stub      | Tier A1.2 (15 群 enumeration)                                 |
| `lem22_smallGroup_625_12` (Lem 22)                 | Section08/Lemma22_SmallGroup625_12.lean:133         | True-stub      | Tier A3 (10 群 enumeration)                                   |

**Minimum True-stub Set (Prop 6, deepest level)**: 5 件
- `cor2_smallGroup_81_9` (Tier A1.2 dependent — 投資非推奨)
- `lem22_smallGroup_625_12` (Tier A3 dependent — 投資非推奨)
- `lem17_3group_fix` (Fix-shape case analysis; Path B Lem 21 composite-order 経由)
- `lem18_5group_fix` (同上)
- `prop6_3_and_5` (case dispatch wrapper)

#### 4.1.B Minimum True-stub 集合 (Prop 7 unconditional 化)

**File**: `Section09_MixingPrimes/Proposition7_3andLarge.lean`
**Top True-stub**: `prop7_3_and_large : True := by trivial` (line 241)

| Stub name                                          | File                                                | Status         | Required                                                      |
|----------------------------------------------------|-----------------------------------------------------|----------------|---------------------------------------------------------------|
| `prop7_3_and_large` (top)                          | Section09/Proposition7_3andLarge.lean:241            | True-stub      | dispatch (a, b, q) extraction                                 |
| `lem17_3group_fix`                                 | (上記)                                              | True-stub      | (上記)                                                        |
| `lem19_large_prime_pgroup`                         | Section06/Lemma19_LargePrime.lean:264                | True-stub      | Lem 16 Fix-shape (proven `_paper`)                            |
| `lem20_*` (Lem 20 conjugate-fix)                   | Section06/Lemma20_ConjugateFix.lean (proven helpers) | Helpers proven | —                                                             |

**Sylow infra proven**: `prop7_q{7,13,19}_sylow{7,13,19}_normal` (Mathlib).

**Minimum True-stub Set (Prop 7)**: 3 件 (Prop 6 と一部共通)
- `prop7_3_and_large` (case dispatch wrapper)
- `lem17_3group_fix` (共通)
- `lem19_large_prime_pgroup` (q ∈ {7,13,19} bound, 比較的軽い)

#### 4.1.C Minimum True-stub 集合 (Prop 8 unconditional 化)

**File**: `Section09_MixingPrimes/Proposition8_5andLarge.lean`
**Top True-stub**: `prop8_5_and_large : True := by trivial` (line 214)

| Stub name                                          | File                                                | Status         | Required                                                      |
|----------------------------------------------------|-----------------------------------------------------|----------------|---------------------------------------------------------------|
| `prop8_5_and_large` (top)                          | Section09/Proposition8_5andLarge.lean:214            | True-stub      | dispatch (a, b, q) extraction                                 |
| `lem18_5group_fix`                                 | (上記)                                              | True-stub      | (上記)                                                        |
| `lem19_large_prime_pgroup`                         | (上記)                                              | True-stub      | (上記)                                                        |
| `lem26_small_prime` (p ≤ 5 ∨ q ≤ 5)                | Section09/Lemma26_SmallPrime.lean:205                | True-stub      | `_paper` conditional 既存 (h_paper_geom 抽出)                 |

**Sylow infra proven**: `prop8_q{7,11}_sylow{5,7,11}_normal` (Mathlib).
**Order22 (q=11 boundary)**: `Moore57.Order22OnMoore57.NoGo` (proven, separate lane).

**Minimum True-stub Set (Prop 8)**: 4 件 (一部共通)
- `prop8_5_and_large`
- `lem18_5group_fix` (共通)
- `lem19_large_prime_pgroup` (共通)
- `lem26_small_prime` (`_paper` conditional 既存)

#### 4.1.D Lem 26 (p ≤ 5 ∨ q ≤ 5) status

Already has `_paper` conditional (proven): `lem26_small_prime_paper`
(Section09/Lemma26_SmallPrime.lean:177) taking 3 hypotheses:
* `h_p_in, h_q_in` : prime ∈ {3,5,7,11,13,19}
* `h_paper_geom` : 5-pair geometric reduction (Sylow + Lem 19 + Fix-shape)
* `h_seven_nineteen_geom` : (7,19) ⇒ closed-neighbourhood fix + a₁ ≥ 21

**Top-stub gap**: `h_paper_geom` の自動生成は paper §9 (Sylow + Lem 25 +
Lem 19 case structure) 全形が必要。 `h_seven_nineteen_geom` extraction は
別タスク (Lem 19 case 4/5 の geometric content). いずれも middle-weight,
Tier A 非依存。

### 4.2 §4.2 Thm 7 (even) 経路の dependency tree

**Top True-stub**: `S9.thm7_even_order (hΓ : IsMoore57 Γ) : True`
(Section09/Theorem7_EvenOrder.lean:320)

**必要 dispatch hypothesis (consumed by `thm7_bound_110_from_odd_part`)**:
```
n = Nat.card (autSubgroup Γ), n even ⟹
  ∃ m, n = 2*m ∧ (m ∣ 55 ∨ m ∣ 25 ∨ m ∣ 27 ∨ m ∣ 7 ∨ m ∣ 11 ∨ m ∣ 19)
```

**Sylow infra (Feit-Thompson-free)**: 全 6 cases (110, 50, 54, 14, 22, 38) で
`thm7_card_*_sylow*_normal` Mathlib-lifted lemma が proven。
(Section09/Theorem7_EvenOrder.lean:199-290)

#### 4.2.A 各 even-order case dispatch (geometric content の要求)

| `|G|` | factorization     | Fix-shape / Geometric input                              | Required True-stub               |
|-------|-------------------|-----------------------------------------------------------|----------------------------------|
| 110   | 2·5·11            | Z₅₅ ⋊ Z₂; Order22 boundary                                | `thm2_makhnev_paduchikh` (MP)    |
| 50    | 2·5²              | Z₂₅ ⋊ Z₂; HS or pentagon Fix                             | `thm5_final` (= Thm 5)           |
| 54    | 2·3³              | Z₂₇ ⋊ Z₂                                                  | `thm4_final` (= Thm 4)           |
| 14    | 2·7               | Z₇ ⋊ Z₂                                                   | `lem19_large_prime_pgroup`       |
| 22    | 2·11              | Z₁₁ ⋊ Z₂; Order22OnMoore57 case                          | `lem19_large_prime_pgroup`       |
| 38    | 2·19              | Z₁₉ ⋊ Z₂                                                   | `lem19_large_prime_pgroup`       |

**Minimum True-stub Set (Thm 7, geometric)**: 4 件
- `thm7_even_order` (dispatch extraction)
- `thm2_makhnev_paduchikh` (MP 2001 main theorem, Section02; current Y ≤ 57 dispatch is True-stub)
- `thm4_final` / `thm5_final` (上記 4.1 と共通)
- `lem19_large_prime_pgroup` (4.1 と共通)

**Note**: `thm2_makhnev_paduchikh` は **Tier A 非依存**: MP 2001 paper-faithful
work で進められる位置にある (`Moore57.Papers.MakhnevPaduchikh2001` 下に
別 paper として scope 化済)。

### 4.3 §4.3 Tier A 代替経路の調査 (= Thm 4 / Thm 5 不要化)

#### 4.3.A 現状の Tier A 依存箇所

**Thm 4 (3-group ≤ 27)** dispatch hypothesis:
```
n ∣ 27 ∨ n ∣ 81   ∧   n ≠ 81
```
- `n ∣ 27 ∨ n ∣ 81`: Lem 17 case (1) Petersen-fix / case (2) Singleton-fix で出る
- `n ≠ 81`: **Cor 2 (SG(81,9) uniqueness)** が必要 → Tier A1.2

**Thm 5 (5-group ≤ 125)** dispatch hypothesis:
```
n ∣ 5 ∨ n ∣ 25 ∨ n ∣ 125
```
- 3-case dispatch (HS / pentagon / empty Fix)
- `n ≠ 625` implicit: case (3) empty Fix で `≤ 125` bound が paper Lem 22 +
  Prop 4 + Prop 5 で確定。 **Lem 22 (SG(625,12) uniqueness)** が必要 → Tier A3.

#### 4.3.B Bypass の可能性 (Path B Lem 21 で部分的 bypass か?)

**判定**: **不可** (重要負の結論)。

理由:
1. Path B Lem 21 (`Fix(σ^l) = Fix(σ)`) は **prime-power の k=1 (prime case)**
   までしか proper unstub できていない (`semiRegular` 経由)。
2. 一般 `l` で `Fix(σ^l) = Fix(σ)` は **真でない** (`⊇` のみ); Lem 17 case 2
   の composite-order σ ∈ SG(81, 9) は σ³ で fix が増える可能性が残る。
3. paper Lem 21 は **cyclic Z₉ × Z₃ shared subgroup** の構造的補題で、
   一般化 Mathlib API は存在しない (`feedback_generalize_theorems.md`
   ベースで hand-roll が必要だが SG(81, 9) の specific 構造を経由する)。
4. paper Lem 22 は SG(625, 12) Heis × Z₅ 構造の **具体的計算**
   (`b_{1j}` 行 + 27 自由度 → 整数解非存在) が本質。

**Bypass 不可結論**: Thm 4 / Thm 5 の unconditional 化には Tier A1.2 / A3
(15 群 + 10 群 enumeration) のいずれかが本質的に必要。

#### 4.3.C 半分 bypass (Thm 4 でのみ可能性)

**Thm 4 case (1) Petersen-fix**: `n ∣ 27` (= |X| ≤ 27) は **Cor 2 不要**で出る。
case (1) のみ active な場合 (i.e., `Fix(X) = Petersen` が論証されている場合) は
unconditional path がある。

しかし Fix-shape case analysis 自体が `lem17_3group_fix` (True-stub) を経由し、
case (2) Singleton-fix の可能性を排除するには Cor 2 を経由する。
**実質的 bypass にはならない**。

### 4.4 §4.4 最小 achievable subgoal の特定

Tier A 投資見送りでは **完全 unconditional** `cor3_375_bound` は到達不可。
ただし、以下の **3 段階の achievable subgoal** が identify される。

#### Tier 1: 完全 conditional (現状 done)

`aut_card_le_375_paper` (MainTheorem.lean:114) — **proven** conditional bound
with explicit `(h_odd_props, h_even_oddpart)` hypotheses. Tier A 不要、
Path B / B4.3 / C3.x ともに不要、純 arithmetic。

#### Tier 2: Partial unconditional via `Conclusion` Prop encoding

各 True-stub の `*Conclusion : Prop` def を **expand** して、`hΓ : IsMoore57 Γ`
から各 conclusion を `[axiom]` として encoded、 中間 lemma 群を全て unstub する。

**Achievable subgoal**: `aut_card_le_375_via_conclusions`
```lean
theorem aut_card_le_375_via_conclusions
    (hΓ : IsMoore57 Γ)
    (h_cor2 : Cor2SG819Conclusion)      -- Tier A1.2 axiomatized
    (h_lem22 : Lem22SG625Conclusion)    -- Tier A3 axiomatized
    (h_mp01  : Theorem2MPConclusion)    -- MP 2001 axiomatized
    (h_lem17_fix : Lem17FixShapeConclusion)   -- Lem 21 + Cor 2 axiomatized
    (h_lem18_fix : Lem18FixShapeConclusion)   -- Lem 22 axiomatized
    (h_lem26 : Lem26SmallPrimeConclusion)     -- Sylow + paper geom
    (h_prop4 : Prop4SG625ExclConclusion)      -- Tier A4 axiomatized
    (h_prop5 : Prop5OrbitSize125Conclusion)   -- proven backbone
    : Nat.card (autSubgroup Γ) ≤ 375 ∧
      (Even (Nat.card (autSubgroup Γ)) → Nat.card (autSubgroup Γ) ≤ 110)
```

8 個の `Conclusion` def を追加した上で `cor3_375_bound_via_autSubgroup` を
適用するだけ。 **新規 Lean infra なし**、True-stub の `Conclusion` encoding 化
+ wiring。 **見積 1-2 commits**.

#### Tier 3: 部分 unconditional (Prop 6/7/8 prime case)

Path B `_prime_via_semiRegular` wrappers 経由で、`|X|` が **prime** な場合
(= |X| ∈ {3, 5, 7, 11, 13, 19}) のみ Cor 3 が unconditional 化:

**Achievable subgoal**: `aut_card_le_375_for_prime_order_aut_subgroup`
```lean
theorem aut_card_le_375_for_prime_order_aut_subgroup
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (h_aut : σ ∈ Moore57.autSubgroup Γ)
    (h_prime_order : Nat.Prime (orderOf σ)) :
    orderOf σ ≤ 19 -- = max prime in Moore57 prime set
```

これは Path B + Lem 16-19 の prime-case wrappers + Lem 26 prime-case で
**完全 unconditional**。 ただし `|Aut(Γ)| ≤ 375` には到達しない (これは
|Aut(Γ)| の **structure** が必要)。

#### Tier 4: 全パス unconditional (current goal, Tier A 必須)

**結論**: Tier A1.2 (15-group enumeration) と Tier A3 (10-group enumeration)
の **少なくとも一方**を完遂しない限り、`cor3_375_bound` の True-stub →
proper signature 化は **不可能**。

両方とも `native_decide` ベースで proof は **計算可能** (個別群構築は重い
~100-200 LOC × 25 件)。 ROI 評価:

- A1.2 完遂 ⟹ Thm 4 unconditional ⟹ `lem17_3group_fix` unstub 経路が開く
- A3 完遂 ⟹ Thm 5 unconditional ⟹ `lem18_5group_fix` unstub 経路が開く
- 両方完遂 + MP 2001 work ⟹ `cor3_375_bound` を **完全 unconditional** 化

**推奨**: Tier 2 (conditional via `Conclusion`) を当面の goal とし、 Tier A
の **15-group enumeration** (A1.2) のみ将来作業候補に格上げ
(Thm 4 unconditional だけで Section 09 odd branch の半分が unstub される)。

### 4.5 推奨実行順序 (Path C 内)

1. **§4.4 Tier 2 (Conclusion-encoded conditional)** — 1-2 commits、
   既存 `*Conclusion : Prop` defs (B-final で導入済) を拡張するだけ
2. **MP 2001 Y ≤ 57 dispatch** (`thm2_makhnev_paduchikh_decomposition_paper`)
   の bottom-up unconditional 化 — Thm 7 even branch の 4 cases (50, 54, 14,
   22, 38) を unstub するための前提
3. **Lem 19 (large prime p-group fix shape)** unconditional 化
   — Lem 16 `_paper` 経由 (既存)、Prop 7/8/Thm 7 で共通利用
4. **Lem 26 `h_paper_geom` 自動生成** — `paper §9 Sylow + Lem 25 + Lem 19
   case structure` の Lean 化、 Prop 8 unconditional 化に直結
5. **(Tier A 投資判断)**: Thm 4 / Thm 5 / `cor3_375_bound` の完全 unconditional
   化のみが目的なら A1.2 (Thm 4 経由 odd branch 半分) 着手検討

**完了条件**: 上記 §4.1-4.4 が "TBD / [ ]" レベルから具体 theorem 名 +
file location + minimum True-stub set + achievable subgoal 階層に到達 —
**達成 (本セッション)**。 Lean コード変更ゼロ (planning only)。

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
4. **Path C** (Cor 3 climbing planning) — **本セッションで dependency tree
   具体化済**。 §4.1-4.4 に minimum True-stub set + achievable subgoal 階層
   identify 済。 次の Lean 作業候補は §4.5 順序参照 (Tier 2 conditional via
   Conclusion encoding が最低 ROI)。

合計見積もり: 6-9 commits で Papers/ の主要不足分が片付く見込み。
Tier A 投資を見送る限り `cor3_375_bound` 完全 unconditional は不可
(§4.3.B 負の結論)、 ただし Tier 2 conditional は achievable (§4.4)。
Thm 6 経路の **odd-branch prime-case** だけは Path B 経由で unconditional。

---

## 関連ドキュメント

* `plans/moore57_roadmap_post_easy_wins.md` — Tier A-F 別の細粒度
  ロードマップ (canonical living document)
* `proofs/moore57_d19_lean_aware_proof.md` — 自然言語証明 (原典)
* `tmp/pdfs/j.laa.2009.07.018.txt` — Mačaj–Širáň 2010 原文 (paper-faithful の
  根拠)
