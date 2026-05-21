# Moore57 数学的障害 — 研究メモ (2026-05-21)

このドキュメントは、Lean 化作業の「数学的に難しい部分」(roadmap §8
ボトルネック) について、原典 + ネット上のリファレンスを当たって調査した
結果のまとめ。 各障害について、論文上の証明構造 / 何が必要 / 代替策があるか
を整理する。

非 Lean な研究ノート — 実装には別途取り掛かる。

---

## 0. 重要前提: Moore57 非存在は **依然 open**

(2026-05-21 web search で確認)

* Makhnev 2020 ([arxiv 2010.13443](https://arxiv.org/abs/2010.13443)) は
  `{55,54,2;1,1,54}` 不存在を主張、 これにより Moore57 非存在を導く。
* Faber-Keegan 2023 ([arxiv 2210.09577](https://arxiv.org/abs/2210.09577))
  は Makhnev の **証明の誤り** を指摘:
  > "The system of equations has a coefficient matrix which decomposes
  >  into independent blocks of reasonable size, all of which have
  >  non-negative integer solutions."
* 結論: **2026 年現在も Moore (3250, 57, 0, 1) の存在は open**。
  Mačaj-Širáň 2010 の `|Aut(Γ)| ≤ 375` が canonical な structural 制約。

したがって私たちの Lean 化フレームワークの目標は **Aut(Γ) ≤ 375
(odd case) + Aut(Γ) ≤ 110 (even case 110)** の unconditional 化のまま。
Makhnev 経路は dead-end なので避ける。

---

## 1. Lem 21 (Mačaj-Širáň 2010 §7)

**Paper statement**: σ ∈ X (3-group of automorphisms with Fix(X) = {a}).
(1) X に N(a) 上 size-3 orbit が ≥ 2 個 ⟹ |X| = 9
(2) X に N(a) 上 size-9 orbit ⟹ |X| ≤ 27

**Paper proof outline** (§7, p. 2391):

### Case (1)
- Let O₁, O₂ be two size-3 orbits on N(a), pick representatives o₁ ∈ O₁,
  o₂ ∈ O₂.
- Let Xᵢ = Stab_X(oᵢ). Since |Oᵢ| = 3 (orbit-stabilizer), [X : Xᵢ] = 3.
- Each Xᵢ ◁ X (index 3 in p-group is normal).
- X₁ ∩ X₂ has index 9 in X.
- **Key claim**: every element x ∈ X₁ ∩ X₂ fixes ≥ 6 points in N(a)
  (the 3 points of O₁ fixed pointwise by X₁, plus 3 of O₂ fixed by X₂).
- By Lem 17, Fix(x) ∈ {Petersen graph, singleton {a}}.
  - Singleton: |Fix(x) ∩ N(a)| = 0 < 6 ✗
  - Petersen: at fixed vertex a, Petersen is 3-regular, so
    |Fix(x) ∩ N(a)| = 3 < 6 ✗
- Hence x = 1, so |X₁ ∩ X₂| = 1, |X| = 9 · 1 = 9.

### Case (2)
- Similar: orbit-stabilizer chain X ⊇ X_o ⊇ X_{oo'}
- |Xoo| = 1 (by similar fix-collapse argument)
- |X| = [X : X_oo] = |O| · |o'^Xo| = 9 · 3 = 27.

**Lean 化に必要なもの**:

1. **Lem 17** (`lem17_3group_fix : True := trivial` を真の statement に):
   3-group X with vertex a fixed ⟹ Fix(X) ∈ {Petersen, singleton}.
   - これには Lem 16 (Fix shape ∈ 6 cases) と、 specific shape に
     narrow するための **fixed subgraph induction** 必要 (paper §6
     Lem 17 proof は省略されている、 paper は "techniques are repetitious"
     と書いて Lem 18 のみ詳述)。
2. **PetersenFixedData.induced_degree_three** — 既に done。
3. **`lem21_part1_subgroup_paper`** — 既に done (arithmetic core)。
4. **Bridge**: `x ∈ X₁ ∩ X₂ ⟹ |Fix(x) ∩ N(a)| ≥ 6` — group action + orbit
   pointwise fix の合成。 Subgroup-Fixed memory も参照
   ([[mathlib-subgroup-fixed-knowhow]])。

**実装難度**: Lem 17 真の unstub が hardest。 Lem 16 dispatch (proper-
signature `lem16_pgroup_fix_shape_paper` 既存) + Fix shape →
"induced graph is Petersen" 推論 (Moore graph 制約から SRG パラメータ
強制) が必要。 paper-level では §6 の "Lemma 17 follows from Lemma 16
and a case analysis" だが、Lean 化には structural shape 強制が要追加。

**評価**: Mid-tier difficulty。 Lem 16 が proper-signature 化済なので、
Lem 17 を unstub する道筋は見えている。 1 commit (~300-500 LOC) で可能か。

---

## 2. Cor 2 / Lem 22 (SmallGroup uniqueness)

**Cor 2**: |X| = 81 ⟹ X ≅ SmallGroup(81, 9) (Eisenstein 群)。
**Lem 22**: |X| = 625, smallest orbit size 25 ⟹ X ≅ SmallGroup(625, 12)
(Heisenberg × Z₅)。

**Paper proof**: GAP の SmallGroup ライブラリで分類を確認 (paper §7 p. 2391)。
> "Examining the lattices of subgroups of groups of order 81 with the
> help of GAP one can check that X = SmallGroup(81,9) is the only group
> with at least two such conjugacy classes."

**Lean 化に必要なもの**:
- 位数 81 の 15 個の同型類すべてを Lean で構築 + invariant (共役類サイズ
  ベクトル)を計算 → uniqueness。
- 位数 625 についても同様 (10 個の非可換群)。

**Mathlib の状況** (2026-05-21 web search):
- "Classifying the groups of order pq in Lean" (Harper-Wu 2025
  [arxiv 2501.09769](https://arxiv.org/abs/2501.09769)) — 位数 pq の場合
  のみ。
- 位数 p² (← 既存 in Mathlib via `commutative_of_card_eq_prime_sq`)。
- **位数 p⁴ の分類は Lean に無い**。 古典結果 (1933+) だが Mathlib には未移植。

**代替策の検討**:
- (a) 15 群 / 10 群を手構築 + native_decide ベース invariant 検査
  (~3000-5000 LOC 推定)
- (b) Moufang loop classification (位数 81: 5 loop も存在) は paper には
  不要、無視可
- (c) [arxiv 0705.0194](https://arxiv.org/abs/0705.0194)
  ("Symmetric (81,16,3) design") は順序 81 群分類を使うが、
  Moore57 fixed-vertex structure に直接対応する instance ではない。

**評価**: 投資 vs ROI が悪い。 roadmap §1 で「Tier A 投資非推奨」が結論。
SG 構築自体は終わっている (`SmallGroup819`, `SmallGroup625_12` 既存)、
**uniqueness** だけが残るが downstream consumer が無い。

---

## 3. Prop 2 (paper §4 rational character system)

**Paper statement** (p. 2386): 任意の有限群 H, rational class
代表 x₁, ..., xᵤ, 既約 ℚ-表現 R₁, ..., Rᵤ で characters r₁, ..., rᵤ。
任意の rational 表現 R with character χ について、 行列
```
[ r_j(x_i) | χ(x_i) ]_{i,j}
```
が **非負整数解** をもつ。

**Paper proof**: R = ∑ nᵢ Rᵢ (decomposition into rational irreducibles)
で nᵢ ≥ 0 整数。

**何が難しいか**:
- ℚ 上の rational character theory が **Mathlib に未整備**。
  `RepresentationTheory.Character` は complex/general field の枠組み。
  rational character の Schur index = 1 と integrality は古典結果 (Brauer,
  Curtis-Reiner) だが Lean には来ていない。
- Paper の用途は **小さな Diophantine system の非負整数解非存在を示す**。
  例: Lem 12 で `[1, p-1 | 1729; 1, -1 | χ₁(x)]` の解析、Lem 13 で 3x3
  行列の解析。

**代替策**:
- (a) Mathlib に rational character theory を追加 (大仕事)
- (b) **各 Diophantine system を case-bash で個別に処理** —
  既に B-final で `Proposition2CharacterSystem : Prop` def を encode 済。
  下流 lemma は hypothesis として取れるので、Prop 2 自体を Lean 化せず
  各使用箇所で `omega` / `decide` ベース case-bash で代替可能。

**評価**: Prop 2 を一般形で Lean 化するのは超大仕事。 各 Diophantine
を個別に処理する方が現実的。 これは "Lem 12/13/14 starred row" の
unconditional 化に必要だが、 既に B4.1 / B4.2 で prime-order の場合は
cyclotomic 経由で bypass 済 (Theorem 3 を使わない)。 composite-order
の場合は B4.3 `trace_int_of_pow_eq_one` で trace ∈ ℤ も取れる。
あと必要なのは「整数解非存在 (Lem 13 starred row の具体的解析)」だけ。

---

## 4. Prop 3 Diophantine (paper §8, eq (7) と (8))

**Paper statement**: σ ∈ X, |X| = 25, Fix(X) = HS。
- ∑_{i=151}^{177} b_{178, i} = 7 (eq 7, degree sum)
- ∑_{i=151}^{177} b_{178, i}² = 31 (eq 8, B² + B - 56I の対角 entry)
- これらに非負整数解は無い。

**ハンド計算で検証** (本ノート作成時に行った):

27 個の非負整数 b_i (∑=7, ∑²=31) を探す。
- ∑b(b-1) = ∑b² - ∑b = 31 - 7 = 24
- ∑ C(b, 2) = 12

非ゼロ entry が k 個と仮定 (k ≤ 27):
- k=1: (7) → C(7,2)=21. ≠ 12
- k=2: (a, 7-a) → C(a,2) + C(7-a, 2). 全 8 通り探索:
  (1,6) → 0+15=15, (2,5) → 1+10=11, (3,4) → 3+6=9. ≠ 12
- k=3: (a,b,c) 全パターン: (1,2,4)→0+1+6=7, (1,3,3)→0+3+3=6,
  (2,2,3)→1+1+3=5, (1,1,5)→0+0+10=10. ≠ 12
- k≥4: max(b) ≤ 7, ∑b=7 強い制約。 (1,1,1,4)→6, (1,1,2,3)→0+0+1+3=4,
  (2,2,2,1)→3, (1,1,1,1,3)→3, (1,2,2,2)→3. ≠ 12

⟹ **No non-negative integer solution** ✓ (paper 主張正しい)。

**Lean 化**:
- 概念的に simple: `decide` で済む (有界探索)。
- 具体形:
  ```lean
  theorem prop3_no_solution (b : Fin 27 → ℕ)
      (h_le : ∀ i, b i ≤ 7)
      (h_sum : ∑ i, b i = 7) (h_sum_sq : ∑ i, (b i)^2 = 31) :
      False
  ```
- `b i ≤ 7` 制約 (degree ≤ 7 = HS regularity)、 8^27 = 2^81 cases だが
  `∑ = 7` で実質有限解空間。
- 直接 `decide` は時間内に通らない可能性大。 代わりに:
  - "non-zero entries の数 ≤ 7 (since ∑ = 7 with non-neg ints)" を経由
  - case split on number of non-zero entries (1, 2, 3, 4 のみ可能性ある)
  - 各 case で `interval_cases` + `omega`

**評価**: 中規模、 ~50-100 LOC で可能。 paper §8 Step 5 の核心、
高 ROI (Prop 3 全形 unstub への大きな前進)。

---

## 5. Lem 17 (3-group fix shape 強制)

**Paper statement** (§6): |X| = 3^k ⟹ Fix(X) is Petersen graph or singleton。

**Paper proof**: paper p. 2390 "proof techniques are repetitious we only
include a proof for Lemma 18". 即ち paper は Lem 17 の証明を **省略**。
Lem 18 proof (5-group) は与えられている。 Lem 17 はそのアナログ:

### Lem 18 proof (paper §6, p. 2390):
- (1) a ∈ Fix(X). 仮定 N(a) \ Fix(X) に |O| < |X| の orbit O 存在。
  Then Stab_X(o) (for o ∈ O) は X の proper subgroup with |Fix(Stab)| > |Fix(X)|.
- 「|Fix(Stab)| > |Fix(X)| = 50」は **Lem 16 で Fix shape ∈ {pentagon (5),
  HS (50), empty, ...}** だが Fix(Stab) ⊋ Fix(X) (≥ 51 vertices) は
  Lem 16 の許容形と矛盾。
- ⟹ X は semi-regular on N(a) \ Fix(X) ⟹ |X| ∣ 50.

### Lem 17 用 analog (推定):
- (1) Fix(X) = Petersen (10 vertices). a ∈ Fix(X). N(a) ∩ Fix(X) = 3
  (Petersen 3-reg)。 N(a) \ Fix(X) = 54.
- 仮定: |O| < |X| orbit ⟹ Stab(o) X の proper subgroup with
  |Fix(Stab)| > 10. Lem 16 case (5) Petersen ⟹ next case up は Hoffman-
  Singleton (50 vertices)? No, Lem 16 for p=3 only has Petersen + singleton.
  ⟹ |Fix(Stab)| = 1 (singleton, contradiction since ≥ 10) or > 10
  (no Lem 16 case allows). 矛盾, semi-regular.
- (2) Fix(X) = singleton {a}. N(a) \ Fix(X) = 57. Stab(o) Fix ⊋ {a} ⟹
  Lem 16 で Fix shape ∈ {pentagon (5), Petersen (10)}. But Stab(o)
  も 3-group, so Lem 16 case (2) singleton or case (5) Petersen, both
  contain a as fixed. (5) gives Petersen, but Petersen 3-reg at a means
  3 specific neighbours fixed, while N(a) \ Fix(X) = 57 includes o
  not in those 3. Contradiction or constraint...

実際は paper §6 Lem 18 proof のアナロジー: X acts semi-regularly on
N(a) \ Fix(X), |X| ∣ |N(a) \ Fix(X)| = 54 (Petersen case) or 57
(singleton case). Combined with |X| 3-group → ∣ 27 (gcd(54, 3^k)) or
∣ 3 (gcd(57, 3^k))。 これは **C3.4 で完了済の semi-regular 推論と同じ
構造**。

**実は Lem 17 の core は C3.4 と同じ**: semi-regular ⟹ orderOf ∣ |moved|.
ただし paper では fix shape が specific (Petersen vs singleton) で
specified されており、C3.4 では FixedData parameter として外から
渡される構造。

**Lem 17 unstub の真の課題**:
1. 「Lem 16 で許される Fix shape のうち、3-group では (1, 10) のみ」を
   narrow down → 既存 `lem16_case2_3group_fix_singleton_if_small` +
   modular constraints で部分的に可能 (size ≤ 3 では 1 のみ)。
   size 4-9 で 1, size 10 で Petersen (要 shape 検証), size 11+ で
   矛盾 (modular bound)。
2. **size = 10 ⟹ Fix is Petersen graph** という structural 強制が
   特殊。 これは Moore graph 内に SRG(10, 3, 0, 1) を induce する
   10-vertex set が Petersen (up to graph iso) であることを必要とする
   — Petersen の SRG(10,3,0,1) uniqueness ([C1.2b] skip 済) を経由する
   必要がある。
   - 実は uniqueness は不要: `IsPetersenLike G ↔ IsSRGWith 10 3 0 1` を
     predicate にしているので、structurally satisfied なら OK。
   - 問題は Moore57 graph 内の 10 fixed vertices が **SRG(10, 3, 0, 1)
     parameters を induce する** ことを示すこと。 これは Fix shape
     constraint で paper では implicit。

**評価**: Lem 17 真の unstub は **可能** だが substantive (~500-1000 LOC)。
size narrowing は modular で済むが、 size=10 ⟹ Petersen-induced は
**Moore graph 内 SRG sub-classification** が必要。 Tier C で skip 済の
"Petersen uniqueness" を bypass する形 (SRG parameter satisfied で
十分) なら可能。

---

## 6. Implementation 優先順位 (research 結論)

(roadmap §7 + 本ノートの統合)

### Tier 1: 着手推奨 (mid-effort, high-impact)
1. **Prop 3 Diophantine `decide` 化** (§4 上記)。
   ~50-100 LOC。 `prop3_step5_conclusion_holds` の `True := trivial` を
   実 statement に。 Path B の延長として自然。

2. **Lem 17 size narrowing + Petersen induction** (§5 上記)。
   ~500 LOC 推定。 既存 `lem16_pgroup_fix_shape_paper` + Lem 16 size
   narrowing + SRG-induced 検証で `lem17_3group_fix_paper`
   proper-signature 化。 大型だが Lem 21 unstub への直接の鍵。

### Tier 2: 着手見送り推奨 (low ROI)
3. **Lem 22 + Prop 4** (Tier A): SG(625, 12) uniqueness。 paper 全形
   unstub に必要だが downstream で別経路 (Thm 6 odd / Thm 7 even) が
   bypass 可能。 投資非推奨 (roadmap §1)。

4. **Prop 2 一般形**: Mathlib rational character integrity 整備が前提。
   ROI が悪い。 各 Diophantine を個別 case-bash で代替推奨。

### Tier 3: 待ち (依存解消後)
5. **Cor 3 unconditional** (`|Aut(Γ)| ≤ 375` 全形): Tier 1 完了後に
   evaluate。 Tier 2 を avoid する achievable subgoal を Path C
   (planning) で確定。

---

## 7. 関連リファレンス

* [Macaj-Siran 2010 (LAA 432)](https://www.sciencedirect.com/science/article/pii/S0024379509003735) — `tmp/pdfs/j.laa.2009.07.018.txt`
* [Makhnev 2020 (arxiv 2010.13443)](https://arxiv.org/abs/2010.13443) — **refuted by Faber-Keegan**
* [Faber-Keegan 2023 (arxiv 2210.09577)](https://arxiv.org/abs/2210.09577) — Makhnev 反論、 Moore57 open
* [Macaj-Siran SGTrio 08 presentation](http://thales.doa.fmph.uniba.sk/macaj/skola/prezentacie/sgtrio08mm.pdf) — paper の short version
* [Dalfó 2019 survey](tmp/pdfs/dalfo_missing_moore_survey_2019.txt) — Moore57 known properties
* [Harper-Wu 2025 (arxiv 2501.09769)](https://arxiv.org/abs/2501.09769) — pq group classification in Lean (位数 p⁴ は未だなし)
* [Groupprops: Groups of order 81](https://groupprops.subwiki.org/wiki/Groups_of_order_81) — 15 群の詳細
* [Cameron Ch3 (local)](tmp/pdfs/cameron_ch3_coherent_configurations.txt) — Coherent configurations

## 8. memory との関係

更新済:
* [[reference-moore57-papers]] — Faber-Keegan 2023 (Makhnev 反論) を追記。

未更新だが要検討:
* [[papers-scaffold-state]] — 本ノートを `plans/` に記載した旨を追記すべきか。
