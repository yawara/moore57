# Moore57 Roadmap — Easy-wins 後の残務整理 (2026-05-20)

このドキュメントは Moore57/Papers/ scaffold (commit `42e1662` 起点) で
「簡単に潰せるもの」を一通り処理した時点 (commit `4805b0f` まで) での残務
を **粒度の細かいタスク** に分解したものです。

## 0. 現状の確定スコア

* `lake build` clean (4037 jobs), CI ratchet sorry-free.
* True-stub の数: 約 80 (うち 30 程度は意図的な backwards-compat shell;
  paper-faithful side theorem はその後ろに proven 版がある).
* 主要な依存外部 (Lean 未移植) 定理:
  1. **Feit–Thompson 奇数位数定理** — Mathlib 未移植。**実は Moore57 では不要**
     (詳細は §5 で議論)。
  2. **Philip Hall (可解群の Hall π-部分群存在)** — Mathlib 未移植。**Moore57 では不要**。
  3. **Burnside `p^a q^b` 可解性** — Mathlib 未移植。**Moore57 では不要**。
  4. **GAP SmallGroup library** — Lean に同等品なし。SG(81,9) は手構築済 (`SmallGroup819.lean`)、
     SG(625,12) は未着手。
* 既に proven な arithmetic / SRG-spectral core が大量にあり、上に置けば
  unconditional version になる「橋」が幾つも待っている状態。

---

## 1. Tier A — GAP SmallGroup 依存

3 個の `[GAP]` タグ付きファイル:

### A1. `SG(81, 9)` 構築 (済) と uniqueness (未)

* **[A1.0] (done)** `Foundations/GroupTheory/SmallGroup819.lean`:
  `SG819 = (Z₉ × Z₃) ⋊ Z₃` (Eisenstein 型作用), GAP-quoted 不変量を
  `native_decide` で検証済 (`card_eq`, `card_orderEq_three`, etc.)
* **[A1.1] (未)** 位数 81 の群が **15 個** ある事実。
  方針候補:
  - (a) 直接構築 (15 個の struct + group instance) — 重い
  - (b) Mathlib `IsPGroup` の分類定理で済むか調査 (`Mathlib.GroupTheory.PGroup`)
  - (c) 圏論的 / cohomological な特徴づけ (`Group.exists_classification`?) — 見込み低
* **[A1.2] (未)** 15 個のうち SG(81, 9) が「2つの size-9 共役類」を満たす唯一を示す。
  入力: `SG819.two_classes_size_9 : 2 ≤ ...` (done)。
  方針: 残り 14 群のそれぞれで共役類サイズを計算して反例とする。

### A2. `SG(625, 12)` 構築

* **[A2.0] (未)** struct + group instance for `SG(625, 12)`.
  - 4-generator polycyclic presentation `⟨f₁, f₂, f₃, f₄⟩`.
  - 全元位数 5、中心 `⟨f₃, f₄⟩` (位数 25), Frattini `⟨f₄⟩` (位数 5)。
  - 構築方法: SG819 を踏襲し、struct `{a b c d : ZMod 5}` + Eisenstein 型作用。
  - 性能懸念: `mul_assoc` は 625³ ≈ 2.4 × 10⁸ ケース。`native_decide` で borderline。
    分割 `decide` で逃げる方針を準備。
* **[A2.1] (未)** GAP-quoted 不変量の検証 (`native_decide`):
  - `card_eq : |SG625_12| = 625`
  - `card_orderEq_five : 624` (全非単位元)
  - `card_center : 25`
  - `card_frattini : 5`
  - `card_classes_25_non_normal : 30` (非正規位数25部分群の共役類数)
* **[A2.2] (未)** 代表系 `U × V` 構造の検証 (Lem 22 の主要前提)。

### A3. SG(625, 12) uniqueness — 位数 625 群分類

* **[A3.0] (未)** 位数 625 の非可換群が 10 個ある事実。SmallGroup index 3, 4, 6, 7, 8, 9, 10, 12, 13, 14。
* **[A3.1] (未)** 各群の手構築 (10 群)。
  優先順: paper の段階的 filter 順 = group 6, 14 → 3, 4, 9, 10 → 7, 8 → 12 (target)。
* **[A3.2] (未)** 各群を排除する性質を `native_decide` で確認:
  - 6, 14: 全位数25部分群が正規 → 矛盾
  - 3, 4, 9, 10 + 12 + 14: 非正規部分群の core size = 5
  - core 数の 5 倍数性: 3, 12 のみ生き残る
  - 3: core 共役類分布が不均等
  - 7, 8: `50 = 25a + 10b` の自然数解非存在

### A4. SG(625, 12) 作用排除 (Prop 4)

* **[A4.0] (未)** SG(625, 12) の `b_{1j}` 行構造の計算 (A2 完成後)。
* **[A4.1] (未)** `Σ b_{1j} = 57 ∧ Σ b_{1j}·b_{j1} + b_{11} − 56 = 125` の整数解非存在
  (omega / native_decide で具体的行列入力に対し)。

---

## 2. Tier B — 文字理論 (Macaj–Širáň §4)

Theorem 3 (rational characters 不変) と Proposition 2 (character system) が
ボトルネック。これらに依存する: Lem 11 (a₁, a₂ rational class 不変),
Lem 13 fullテーブル, Lem 14 paper-faithful 形, Lem 18 一般。

### B1. Mathlib `Mathlib.RepresentationTheory` の整備状況確認

* **[B1.0] (調査)** Mathlib に有限群の既約表現 / 指標表の何があるか正確に把握。
  - `Mathlib.RepresentationTheory.Character` (基礎指標)
  - `Mathlib.RepresentationTheory.Maschke` (Maschke)
  - 有理指標 (rational class) 定式化があるか?

### B2. Permutation representation character の Lean 化

* **[B2.0] (未)** `Moore57.permutationRepresentation σ : Representation ℚ G V` の定義
  (既存の `permMatrix σ` をベースに)。
* **[B2.1] (未)** χ(σ) = `trace (permMatrix σ)` = `fixedVertexCount σ` の bridge。

### B3. Moore57 spectral decomposition の character 接続

* **[B3.0] (部分済)** `E57Matrix, E7Matrix, EMinus8Matrix` のスペクトル分解
  + `Higman trace identity` は既に proven (`thm1_chi1_formula`).
* **[B3.1] (未)** これらの projection を character として再解釈
  (`χ₀(σ) = trace(E_57 · P_σ)` 等)。

### B4. Lem 3 + Thm 1 ⟹ a₁, a₂ の rational coefficient 表示

* **[B4.0] (未)** `a₁(σ) = α₁·χ₀ + α₂·χ₁ + α₃·χ₂` の係数導出。
* **[B4.1] (未)** Theorem 3 (有理指標は rational class 上で定数) を仮定として
  Lem 11 a₁/a₂ を導出 (`lem11_ai_constant_on_rational_classes` の True-stub を埋める)。

### B5. Lem 13, Lem 14 paper-faithful 形

* **[B5.0] (未)** Lem 13 full 6-row table (starred row 含む) を char-theoretic に。
* **[B5.1] (未)** Lem 14 `a₁(x) ≡ b₁(x) (mod |X|)` の semi-regular 軌道分解 + 文字版。

---

## 3. Tier C — Petersen / Hoffman–Singleton 構造

§6 Lem 17, 18 の geometric 部分; §8 Prop 3 の HS 固定型.

### C1. Petersen graph の Lean 化

* **[C1.0] (未)** `Moore57.PetersenGraph : SimpleGraph (Fin 10)` 定義。
* **[C1.1] (未)** `IsSRGWith 10 3 0 1` の証明 (decide で済む見込み)。
* **[C1.2] (未)** `Aut(Petersen) ≅ S₅` (or |Aut| = 120) を `native_decide` で。
* **[C1.3] (未)** Subgraph embedding: `Petersen ↪ Moore57` の condition 定式化
  (これは `IsMoore57 Γ` の subgraph として induce する形)。

### C2. Hoffman–Singleton graph の Lean 化

* **[C2.0] (調査)** Mathlib に Hoffman–Singleton はあるか? (見込み: なし)。
* **[C2.1] (未)** 50 頂点 SRG `IsSRGWith 50 7 0 1` の explicit construction
  (e.g., via Kneser graph K(5, 2) 派生、Lev 構成 etc.)。
* **[C2.2] (未)** Aut(HS) = 252,000 or similar `native_decide` 性能要検証
  (50! は overflow するので分解必須)。
* **[C2.3] (未)** Subgraph embedding into Moore57.

### C3. Lem 17, 18 geometric 部分の接続

* **[C3.0] (未)** Lem 17: `Fix(X)` が 3-group の場合 → Petersen ∨ singleton。
  入力: `lem17_neighbor_fix_mod_three` (done), `lem17_case1_arithmetic_*` (done)。
  追加: Fix(X) の induced subgraph が SRG な事実 + Petersen identification。
* **[C3.1] (未)** Lem 18: `Fix(X)` が 5-group → HS ∨ pentagon ∨ ∅。
  類似構造。
* **[C3.2] (未)** §8 Prop 3: `Fix(X) = HS ⟹ |X| ≤ 5`。
  入力: `prop3_arithmetic_core_no_partition_of_7_with_sq_31` (done) + HS の adjacency 構造。

---

## 4. Tier D — Rank-3 perm group framework (Higman 1964)

§§1-2 of Higman 1964 全体 (Lems 1-7 抽象版)。Aschbacher Lem 1.4 一般版もここ。

### D1. Mathlib `MulAction` 拡張

* **[D1.0] (調査)** `Mathlib.GroupTheory.GroupAction` に **rank** 概念はあるか?
  - `MulAction.orbit`, `MulAction.stabilizer` はある。
  - `rank G Ω := |G \\ (Ω × Ω)|` (orbital 数) — 自前定義必要。

### D2. Orbital structure infrastructure

* **[D2.0] (未)** `MulAction.orbital G Ω` (Ω × Ω の G-軌道) 定義。
* **[D2.1] (未)** Paired orbit `Δ'(a) = {a^g : a^{g⁻¹} ∈ Δ(a)}` 定義。
* **[D2.2] (未)** Self-paired orbit 定義 + 「偶位数 ⇔ 自己paired」(Lem 1, 3)。

### D3. Higman 1964 Lems 1-7 抽象版

* **[D3.0] (未)** Lem 1: paired orbit ⇔ even order。Cauchy + pairing。
* **[D3.1] (未)** Lem 2: intersection numbers λ, μ, λ₁, μ₁ の定数性 (rank-3 仮定下)。
* **[D3.2] (未)** Lem 3: odd order rank-3 ⟹ k = l, n = 2k+1, λ = μ。
* **[D3.3] (未)** Lem 4: 不可約性 ⇔ G_a ≠ G_{Γ(a)} ⇔ Γ(a) = Γ(b) for some a ≠ b。
* **[D3.4] (未)** Lem 5: μl = k(k − λ − 1) (rank-3 perm group 形)。Moore57 SRG 形は既に proven。
* **[D3.5] (未)** Lem 6, 7: incidence matrix の eigenvalue 解析。
* **[D3.6] (未)** Thm 1 full: n = k² + 1 ⟹ k ∈ {2, 3, 7, 57}。算術 core は既に proven。

### D4. Aschbacher 1.4 一般版

* **[D4.0] (未)** `f = k ± 1` 二者択一 (involution 不動点星型分類)。
  既存: Moore57 instance (`f = 56 = k − 1`) は proven。
* **[D4.1] (未)** SRG eigenvalue + multiplicity → integer 制約 → 二者択一 (Cor 形)。

---

## 5. Tier E — Feit–Thompson 代替 (重要発見)

### 5.0 整理: 何が必要か

§9 Thm 6, 7 で paper は次を主張:
1. **「`G` is solvable」** (Feit–Thompson, |G| odd の場合)
2. **「`G` has Hall π-subgroup for every prime set π」** (Philip Hall, G solvable)
3. これらを用いて Prop 6, 7, 8 で 2-prime cases を dispatch。

### 5.1 Moore57 の場合 Feit–Thompson は不要(!)

**鍵となる観察**:

> "with the exception of 110, all possible orders have at most two distinct prime factors."
> — Mačaj–Širáň 2010, §9

つまり Moore57 で可能な |G| ≤ 375 の値は:
- 1-prime: `p^k` (Lems 17-19 で処理、Sylow + Mathlib のみで OK)
- 2-prime: `p^a · q^b` (Prop 6, 7, 8 の dispatch)
- 3-prime (奇数): 該当なし(Lem 26 で排除)
- 3-prime (偶数): `110 = 2·5·11` のみ(これは Thm 7 で別途処理)

#### Hall 部分群代替

**2-prime |G| = p^a q^b の場合**: Hall {p}-部分群 = Sylow p-部分群、Hall {q}-部分群 = Sylow q-部分群。
**Mathlib `Sylow` だけで十分**。Hall's theorem は不要。

**3-prime |G| = 110 = 2·5·11 の場合**: 
- n₁₁ ∣ 10 ∧ n₁₁ ≡ 1 (mod 11) ⟹ n₁₁ = 1 (Sylow 11 正規)
- Sylow 11 正規 + Sylow 5 ⟹ PQ は Hall {5, 11}-部分群(位数 55)
- ここは Sylow analysis のみで Hall 部分群を取得可能。
**Mathlib `Sylow` + `Schur-Zassenhaus` で十分**。

#### Solvable 代替

Paper の「`G` is solvable」の使い方を再点検すると、実は **Hall 部分群を取り出すため** だけに使われていて、その目的のためには Sylow + Schur–Zassenhaus で十分(上記)。

つまり **Moore57 の文脈では Feit–Thompson も Philip Hall も不要**。

### 5.2 詳細プラン: §9 を Mathlib-only で証明

* **[E1.0]** Prop 6 dispatch (p=3, q=5): |X| = 3^a · 5^b。
  - **[E1.1]** Sylow 5 部分群の数 n_5 ∣ 3^a + ≡ 1 (mod 5) — 候補は 1 or 6 or 21 or ... 1 のみ (small a)。
  - **[E1.2]** Q (Sylow 5) 正規 ⟹ Schur–Zassenhaus で `X = Q ⋊ P`。
  - **[E1.3]** 既存の `prop6_card_dvd_135_or_375` (proven arithmetic) と接続。

* **[E2.0]** Prop 7 dispatch (p=3, q ∈ {7, 11, 13, 19}): 各 q について類似。
* **[E3.0]** Prop 8 dispatch (p=5, q ∈ {7, 11}): 同。
* **[E4.0]** Thm 7 dispatch (|G| even, including |G| = 110):
  - 110 = 2·5·11 の 3-prime case を Sylow 11 正規 + Sylow 5 normalizes → PQ Hall 部分群で処理。
  - 既存の `thm7_dvd_one_of_six_from_odd_part` (proven arithmetic) と接続。

* **[E5.0]** Cor 3 = Thm 6 + Thm 7 の combined ≤ 375 bound:
  - 既存 `cor3_unified_arithmetic_bound` (proven) と接続。
  - 残るのは **「Aut(Γ) ↔ Subgroup (Equiv.Perm V)」bridge** + Sylow analysis。

### 5.3 Burnside `p^a q^b` 可解性

これも **必要なし**。理由: 我々は具体的に小さい order の case を Sylow + 算術で処理するため、抽象的に「solvable」を経由する必要がない。

---

## 6. Tier F — Lem 6 (4) corner cases `|O| ∈ [5, 63]`

既存: `|O| ∈ {1, 2, 3, 4}` (4-vertex case は 64 boolean 全列挙 + 4 triangle + 3 C₄ exclusions) と `|O| ≥ 64` (Mohar bound).

### F1. 単純な拡張(難しい)

* **[F1.0]** `|O| = 5`: 2^10 = 1024 cases。Pentagon のみ 5 edges 達成。要工夫。
* **[F1.1]** `|O| = 6, 7, ..., 63`: 各サイズで cases 数が指数的に増大。

### F2. 構造的アプローチ(現実的)

* **[F2.0]** Girth-5 graph on n vertices の edge bound (Moore-type bound):
  - `n = 5`: ≤ 5
  - `n = 6, 7, 8, 9`: 個別計算
  - `n = 10`: ≤ 15 (Petersen)
  - 一般 n: Moore bound `n ≥ 1 + k(k - λ - 1)`?
* **[F2.1]** 各頂点の induced degree ≤ d を Moore57 構造から導出
  (μ = 1 ⟹ 任意 2 頂点の共通近傍数 ≤ 1)。
* **[F2.2]** これらから degree sum ≤ 2 · edges 経由で Tr(O)² < |O| を一般 |O| ∈ [5, 63] で導出。

優先度: 低 (Mohar bound `|O| ≥ 64` で実用上は足りている可能性)。

---

## 7. 推奨実行順序

### 7.1 短期 (1 commit 単位、各 < 200 LOC)

1. **[E1.1]** Prop 6 Sylow analysis (3-prime + 5-prime ⟹ Q normal) — Sylow + omega。
2. **[E4.0]** Thm 7 Sylow analysis (110 = 2·5·11 dispatch) — 類似。
3. **[E5.0]** Aut(Γ) ↔ Subgroup bridge in `Cor 3`。
4. **[A2.0]** SG(625, 12) struct + group instance (Eisenstein 型相当)。
5. **[A2.1]** SG625 GAP-quoted invariants via `native_decide`。

### 7.2 中期 (multi-commit、各 200-1000 LOC)

6. **[A1.1] + [A1.2]** SG(81, 9) uniqueness (15-group enumeration + filter)。
7. **[E2.0] + [E3.0]** Prop 7, 8 Sylow analyses。
8. **[B2.0] + [B3.0]** Permutation representation + Moore57 character bridge。

### 7.3 長期 (substantive new infrastructure)

9. **[C1, C2]** Petersen + Hoffman–Singleton explicit graphs。
10. **[B4, B5]** Character-dependent Lemmas 11 (a₁/a₂), 13, 14 paper-faithful。
11. **[D1-D4]** Rank-3 perm group framework + Higman 1964 全体。
12. **[A3, A4]** Order-625 group classification (Lem 22, Prop 4)。

### 7.4 見送り推奨

13. **[F1, F2]** Lem 6 (4) corner cases (|O| ∈ [5, 63])。
    Mohar bound (|O| ≥ 64) があれば実用上問題なし。

---

## 8. ボトルネック識別 ── 「不要な依存」リスト

paper を素直に読むと必要に見えるが、Moore57 specific には不要な定理:

| 定理 | 当初推測 | 実状 |
|---|---|---|
| Feit–Thompson (奇数位数定理) | §9 Thm 6 で必須 | **不要**: |G| ≤ 375 odd は ≤ 2 distinct primes ⟹ Sylow + Schur-Zassenhaus で十分 |
| Philip Hall (Hall π-部分群存在) | §9 Thm 6/7 で必須 | **不要**: 2-prime case は Sylow = Hall, 3-prime case 110 は Sylow 11 normal で取れる |
| Burnside p^a q^b 可解性 | §9 で必要かと推測 | **不要**: 解能性経由せず Sylow 直接で処理可 |
| 一般 SRG 分類 (k ∈ {2, 3, 7, 57}) | Aschbacher Lem 1.3 で必須 | **不要 (Moore57 instance level)**: Higman 1964 算術 core (`theorem1_arithmetic_core`) 経由で Moore57 k=57 は Cameron 3.13 で済む |

paper-level の本当のボトルネックは:
- **GAP SmallGroup library**: Lean 等価物が無いため手構築必須 (Tier A)。
- **Character theory** (Mathlib にあるが Moore57 spectral との bridge 必要)。
- **Petersen / HS explicit graphs**: 小サイズだが手作業が必要。

---

## 9. 関連メモリ

* [[project-papers-scaffold]] — Papers/ scaffold 全体状態
* [[reference-moore57-papers]] — paper 出典 + Lean 進捗
* [[project-moore57-state]] — implementation 側 D19 + Order22 + HS の済み状態
