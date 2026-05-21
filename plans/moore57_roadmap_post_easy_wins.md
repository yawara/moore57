# Moore57 Roadmap — Easy-wins 後の残務整理 (2026-05-21 更新 (深夜))

このドキュメントは Moore57/Papers/ scaffold (commit `42e1662` 起点) で
「簡単に潰せるもの」を一通り処理した時点での残務を **粒度の細かいタスク** に
分解したものです。

直近の主要進捗 (2026-05-21 同日内 3 並行セッション):

- **Tier C 全体完了** — C1, C2, C3 (含 C3.4 semi-regular orbit + C3.6
  Prop 3) すべて done または scope-skip。 `SemiRegularOrbit.lean` +
  graph-aut bridge + 各 FixedData wrapper + Lem 17/18 unconditional
  wrapper が稼動。
- **Tier D 全体完了** — D2.x, D3.0–D3.6, D4.0–D4.1 すべて done。
  Higman 1964 §§1-2 (Lems 1-7 抽象版) + Aschbacher 1.4 (involution
  dichotomy + combined classification) が paper-faithful に Lean 化。
- **Tier B B4.3 Step 4 full 完了** — `trace_int_of_pow_eq_one`:
  任意の有限位数 ℚ-線形作用素で trace ∈ ℤ。 **B4.1 prime-case の
  composite-order 完全一般化**。 `CyclotomicGenericTrace.lean` + 既存
  `Module.AEval` infrastructure を再利用。 Moore57 specific な
  wire-up (Step 5-6) のみ残。

これで Mathlib に未移植の大物外部定理は **GAP SmallGroup uniqueness 1 件**
にほぼ収束。 ロードマップの認識ではかつて巨大な Theorem 3 composite-order
ボトルネックも本日 hand-roll で取得済 (詳細 §2 [B4.3] / §8.1)。

## 0. 現状の確定スコア (2026-05-21 深夜)

* `lake build` clean (4063 jobs)、CI ratchet sorry-free
  (`grep ":= sorry$\|:= by sorry$\|:= admit$\|by admit$"` で 0 件)。
* True-stub の数: 94 (`grep "True := by trivial\|True := trivial"` 計測)。
  B-final + C3.6 + D3.6 + D4.1 + B4.3 の各段階で `XConclusion : Prop` /
  proper-signature 化された companion def が追加され、結果として
  backward-compat shell の数自体は若干増加。 paper-faithful 側はその
  後ろに proven 版が並ぶ状態。
* 主要な依存外部 (Lean 未移植) 定理 — 2026-05-21 深夜版:
  1. **Feit–Thompson 奇数位数定理** — Mathlib 未移植。**Moore57 では不要**
     (Sylow + Schur-Zassenhaus で代替、§5 参照)。
  2. **Philip Hall (可解群の Hall π-部分群存在)** — Mathlib 未移植。
     **Moore57 では不要**。
  3. **Burnside `p^a q^b` 可解性** — Mathlib 未移植。**Moore57 では不要**。
  4. ~~**Curtis–Reiner Theorem 3 (rational class character integrality)**~~
     — **本日 B4.3 Step 4 (`trace_int_of_pow_eq_one`) で実質的に bypass**。
     任意有限位数で trace ∈ ℤ は cyclotomic + Module.AEval 経由で
     unconditional に取得。 ただし paper §4 Prop 2 の rational class
     一般形 (character system non-neg integer solution) は依然 Lean 化
     必要 (deferred-heavy, 別 Prop として encode 済)。
  5. **GAP SmallGroup library** — Lean に同等品なし。SG(81,9) と
     SG(625,12) は手構築済、uniqueness (15 群 / 10 群 enumeration) は
     downstream consumer 無しで投資非推奨。
* 既に proven な arithmetic / SRG-spectral / cyclotomic-trace /
  **composite-order trace** core が大量にあり、上に置けば
  unconditional version になる「橋」が複数待機:
  - B4.1 `aut_pow_prime_E7_trace_int` — prime-order starred row
    (Lem 12, Lem 13 prime cases)
  - **B4.3 `trace_int_of_pow_eq_one` — composite-order (任意 n)**。
    Moore57 への wire-up (`σ ∈ Aut(Γ) → ℚ-linear endomorphism`) は
    Step 5-6 で実装。

---

## 1. Tier A — GAP SmallGroup 依存

3 個の `[GAP]` タグ付きファイル:

### A1. `SG(81, 9)` 構築 (済) と uniqueness (未)

* **[A1.0] (done)** `Foundations/GroupTheory/SmallGroup819.lean`:
  `SG819 = (Z₉ × Z₃) ⋊ Z₃` (Eisenstein 型作用), GAP-quoted 不変量を
  `native_decide` で検証済 (`card_eq`, `card_orderEq_three`, etc.)
* **[A1.1] (orientation done, 2026-05-21)** 位数 81 の群が **15 個** ある事実。
  **Mathlib 調査結論**: `Mathlib.GroupTheory.PGroup` には IsPGroup の card/orderOf
  特性, Sylow 系, p-group center 非自明性, `card = p²` 群の abelian 性
  (`commutative_of_card_eq_prime_sq`) 等しかなく、**位数 `p⁴` の 15
  isomorphism classes 分類は無い**。
  方針候補:
  - (a) 直接構築 (15 個の struct + group instance) — 重い、各 ~100-200 LOC + uniqueness 用 `native_decide` 検証
  - (b) ~~Mathlib `IsPGroup` の分類定理で済む~~ — **不可** (Mathlib に classification 無し)
  - (c) 圏論的 / cohomological な特徴づけ — 見込み低
* **[A1.2] (未)** 15 個のうち SG(81, 9) が「2つの size-9 共役類」を満たす唯一を示す。
  入力: `SG819.two_classes_size_9 : 2 ≤ ...` (done)。
  方針: 残り 14 群のそれぞれで共役類サイズを計算して反例とする
  (A1.1 直接構築前提)。

### A2. `SG(625, 12)` 構築

* **[A2.0] (done)** `Foundations/GroupTheory/SmallGroup625_12.lean`:
  Heisenberg cocycle 経由 `SG625_12 ≅ Heis(F₅) × Z₅` (struct
  `{a b c d : ZMod 5}`, 全元位数 5)。 `mul_assoc` は ZMod 5 上の
  polynomial identity (`ring`) で軽量に証明済 (native_decide 不要)。
* **[A2.1] (done)** GAP-quoted 不変量検証 (`native_decide` ベース):
  `card_eq = 625`, `card_orderEq_five = 624`, `card_center = 25`,
  `card_frattini = 5`, `frattini_is_commutator_image` まで完了。
* **[A2.2-minimal] (done, 2026-05-21)** Heis × Z₅ 直積構造の Subgroup-level 明示化
  (`SmallGroup625_12.lean` に追加):
  - `heisSubgroup : Subgroup SG625_12` (order 125, kernel of d-projection)
  - `z5DirectFactor : Subgroup SG625_12` (order 5, central direct factor)
  - `heisSubgroup_card = 125`, `z5DirectFactor_card = 5` (`native_decide`)
  - `heisSubgroup_normal`, `z5DirectFactor_le_center`,
    `heisSubgroup_inf_z5DirectFactor_eq_bot` (構造的事実)
* **[A2.2-full] (未, low-priority)** 本格的 paper-faithful U × V 代表系
  (Lem 22 の主要前提)。 paper の「位数 25 の Abel 部分群 U と位数 25 の
  **非 Abel** 部分群 V」は SG625_12 が exponent-5 (位数 25 部分群はすべて
  abelian) と矛盾する形なので、paper の文脈で何を指すか要確認 (cosets?
  representative system?)。 後続 [A4.0] 作業時に再評価。

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

### Tier A 投資判断 (2026-05-21 更新)

**重要観察**: `lem22_smallGroup_625_12`, `prop4_sg625_excluded`,
`cor2_smallGroup_81_9` の True-stubs は **downstream で誰からも consume
されていない** (`grep` で定義箇所のみ hit)。 すなわち:

- これら 3 つを unstub しても、それ自体は上位の `Theorem 4`, `Theorem 5`,
  `cor3_375_bound` (いずれも True-stub) には伝播しない。
- 上位 True-stub を解消するには Tier A 以外 (Tier B paper-faithful, Tier C
  semi-regular, など) のヘビーな work も全て必要。
- 重い A1.2 (15 群構築), A3 (10 群構築), A4 (paper-specific arithmetic)
  は **直接的な ROI 無し** で着手は推奨しない。

**Tier A での残り推奨 work**: なし (現時点)。 重い uniqueness 系は他 Tier の
前進待ち、SG819 / SG625_12 / heisSubgroup / z5DirectFactor の foundation は
将来 paper-faithful work で再利用できる infrastructure として既に整備済。

---

## 2. Tier B — 文字理論 (Macaj–Širáň §4)

**進捗 (2026-05-21 深夜)**: Tier B **B4.3 Step 4 full まで完了**。
[B1], [B2.0], [B2.1], [B3.0], [B3.1] (+ [B3.1+] subrep full bridge),
[B4.0] (+ [B4.0+] Lemma 11 χⱼ conj wrappers), **[B4.1] (prime-order
cyclotomic 経由)**, **[B4.2] (starred p-prime row dispatch)**,
[B5.0]/[B5.1] (arithmetic core + FixedData bridges), **[B-final]**
(全 True-stub の `XConclusion : Prop` def 化 + Lem 11 conditional bridge)、
そして **[B4.3] Steps 1-4 full (composite-order trace integrality, 本日深夜)** 完了。

Tier B 内部のメインボトルネック (Theorem 3 composite-order) は本日
`trace_int_of_pow_eq_one` の hand-roll で **実質的に bypass**。
残り:
- **[B4.3] Step 5-6**: Moore57 wire-up (任意有限位数 σ ∈ Aut(Γ) で
  `tr(E₇·P_σ) ∈ ℤ` の composite 版 + `lem13_starred_row_5_*` unstub)
- [B5.0] full paper-faithful 6-row Lem 13 / 17-row Lem 12 表 (character
  system 全形)
- [B5.1] full semi-regular orbit decomposition for Lem 14

[B5.0]/[B5.1] は Lean-未移植 external (paper §4 Prop 2 + structural
fix-shape classification) 待ちだが、`XConclusion` Prop def 経由で
downstream lemmas は unconditional に進められる状態に整っている。

### B1. Mathlib `Mathlib.RepresentationTheory` の整備状況確認

* **[B1.0] (done)** Mathlib `RepresentationTheory.Character` に
  `Representation.character g := LinearMap.trace k V (ρ g)` あり。
  **rational class 概念は Mathlib になし** (Curtis–Reiner Theorem 3 も
  Mathlib になし)。

### B2. Permutation representation character の Lean 化

* **[B2.0] (done)** `Moore57.permutationRepresentation : Representation ℚ G (X →₀ ℚ)`
  を `Representation.ofMulAction ℚ G X` で wrap 済
  (`Foundations/Representation/PermutationRepresentationCharacter.lean`)。
* **[B2.1] (done)** `character_permutationRepresentation_eq_fixedVertexCount`:
  `(permutationRepresentation).character g = Moore57.fixedVertexCount (toPermHom g)`
  bridge。

### B3. Moore57 spectral decomposition の character 接続

* **[B3.0] (done)** spectral 分解 (`adjMatrix = 57 E_57 + 7 E_7 - 8 E_-8`),
  Higman trace identity (`thm1_chi1_formula`), trace decomp
  (`trace_decomp_via_spectral`) 完了。
* **[B3.1] (done)** `Moore57Graph/Characters.lean` で
  `chi0/chi1/chi2 : Equiv.Perm V → ℚ` 関数定義 + 性質:
  - `chi0_eq_one`: `χ₀(σ) = 1`
  - `chi_sum_eq_fixedVertexCount`: `χ₀+χ₁+χ₂ = a₀`
  - `adjacentMovedCount_eq_chi_combination`: `a₁ = 57χ₀+7χ₁−8χ₂`
  - `chi0_conj`, `chi1_conj`, `chi2_conj`: graph-aut 共役不変性 (trace
    cyclic + projection commutation)
* **[B3.1+] (done, 2026-05-21)** χⱼ を `Representation.character`
  of spectral subrepresentation として正式に identify (E_λ の range が
  subrepresentation, restrict した character)。
  `Foundations/Representation/SpectralSubrepresentation.lean` で
  全 3 character (χ₀, χ₁, χ₂) について以下を実装:
  - `autSubgroupPermRep Γ : Representation ℚ (autSubgroup Γ) (V → ℚ)` を
    `permMatrix.toLin'` で構築 (project-local `moore57_permMatrix_mul/one`
    が true hom を保証)。
  - `chi{0,1,2}Subrep Γ : Representation ℚ (autSubgroup Γ) (range E_λ.toLin')`
    を `Representation.onCommutingRange` (既存
    `D19OnMoore57/E7Projection/ProjectionRepresentationSkeleton.lean`)
    で構築。
  - `chi{0,1,2}_eq_chi{0,1,2}Subrep_character`:
    `chi_j Γ σ.val = chi_jSubrep.character σ` を各 E_λ の trace_restrict
    bridge で証明 (χ₁ は既存 `ProjectionTraceBridge.lean` 再利用、
    χ₀ と χ₂ は本ファイルで `IsIdempotentElem` + commute + trace_restrict
    を新規構築)。

### B4. Lem 3 + Thm 1 ⟹ a₁, a₂ の rational coefficient 表示

* **[B4.0] (done)** Section02_StateOfTheArt/Theorem1_Higman.lean に
  inverse formulas を追加:
  - `thm1_a0_eq_chi_sum`: `a₀ = χ₀ + χ₁ + χ₂`
  - `thm1_a1_eq_chi_combination`: `a₁ = 57χ₀ + 7χ₁ - 8χ₂`
  - `thm1_a2_eq_chi_combination`: `a₂ = 3192χ₀ - 8χ₁ + 7χ₂`
  (matrix `P` の paper 形)。
* **[B4.0+] (done)** Lemma11 に χⱼ conj-invariance wrappers
  (`lem11_chi{0,1,2}_constant_under_graphAut_conjugation`)
  ← `chi_j_conj` from Characters.lean。
* **[B4.1] (done, 2026-05-21 / commits `4b9a6b9`, `be8c0d7`)**
  cyclotomic-based integer trace for prime order p:
  - `Foundations/LinearAlgebra/PowPrimeTrace.lean` 新規:
    `exists_int_trace_of_pow_prime_eq_one (f^p = 1) ⟹ trace(f) ∈ ℤ`。
    戦略: `cyclicProjection f p := (1/p)·(1 + f + ... + f^(p-1))` を冪等
    にして `IsInternal` (W = range ⊕ ker) で trace 分解。 range 上は id
    (trace = dim), ker 上は `aeval f cyclotomic_p = 0` ⟹ 既存
    `trace_package_of_cyclotomic_prime_aeval_eq_zero` で trace = -γ ∈ ℤ。
  - `Moore57Graph/Aut/TraceIntegrality.lean` に `aut_pow_prime_E7_trace_int`
    (`σ^p = 1` ⟹ `tr(E₇·P_σ) ∈ ℤ`) を `Matrix.toLin'_pow` + 新規
    `restrict_pow_apply` 経由で接続。 既存 `aut_involution_E7_trace_int`
    (p=2 特化) を真に一般化。
  - `Lemma12_PrimeOrder.lean` の `lem12_no_p3_a0_one` を **完全 unconditional 化**
    (True-stub → 本物の False 証明):
    `aut_pow_prime_E7_trace_int` (p=3) + `lem3_a1_mod_15` (a₁ ≡ 7a₀+5 mod 15)
    + `lem12_p3_a1_eq_zero` (no-triangle) で `a₀ = 1` のとき
    `0 ≡ 12 (mod 15)` 矛盾。
  - **設計上の意義**: Theorem 3 (Curtis–Reiner) の全 rational class 版は
    依然 Mathlib 未移植だが、**Moore57 の prime-order starred 行は
    cyclotomic 経由で個別に unconditional 化可能** という事が確立した。
    Lem 12 p=7 starred, Lem 13 の p=3/5/7 starred 行などはすべて同じ
    pattern (`aut_pow_prime_E7_trace_int` + 既存 mod-arithmetic) で
    片付くので、Theorem 3 の Lean 移植を待たずに進められる。

* **[B4.2] (done, 2026-05-21)** Starred p-prime row dispatch
  (B4.1 の直接適用):
  - **[B4.2-1] (done)** `lem12_no_p7_a0_58`
    (`Lemma12_PrimeOrder.lean:312`):
    `aut_pow_prime_E7_trace_int` (p=7) + `lem3_a1_mod_15`
    (`a₁ ≡ 7·58+5 = 411 ≡ 6 (mod 15)`) +
    `lem12_a1_zero_of_closed_neighbourhood_fixed` (`a₁ = 0`) で
    `0 ≡ 6 (mod 15)` 矛盾。 True-stub → False 証明に格上げ。
    **発見**: paper の character lower bound `a₁ ∈ {21 + 105k}`
    (Prop 2 依存) は不要 — mod-15 congruence だけで p=3 と同じ
    構造で済む。
  - **[B4.2-2] (done)** `lem13_p3_row_1_1_no`
    (`Lemma13_PrimeSquared.lean`): Lem 13 p=3 starred row `(?, 1)` を
    `lem12_no_p3_a0_one` (B4.1 経由) を `σ³` に適用して False。
    `a₀(σ) ≤ a₀(σ³)` propagation で `(?, 1)` 列全体を排除。
  - **残り (B4.3 待ち)**: Lem 13 p=5 starred rows `5*(0, 5)` と
    `5*(5, 5)` は order-25 σ の Tr(σ) 整数性を要求するため
    composite-order trace (B4.3) 待ち。 既存の
    `lem13_starred_row_5_*_no_integer_trace` は Tr を hypothesis に
    取る arithmetic core 形のまま (Tr 整数性は B4.3 で供給予定)。
  - **Theorem 3 不要**: paper の "by Curtis–Reiner Theorem 3" を持つ
    starred 行のうち、order が **prime** のものは全て B4.1 経由で
    Theorem 3 を bypass できる事を確認。 composite-order や rational
    class identity の一般形は依然 Theorem 3 待ち、[B4.3] として deferred。

* **[B4.3] (partial done, 2026-05-21)** Composite-order / general
  rational-class Theorem 3 移植。 `Foundations/LinearAlgebra/PowCompositeTrace.lean`
  に段階的に build out 中:
  - **Step 1 (done)** `aeval_X_pow_sub_one_eq_zero` / `aeval_prod_cyclotomic_eq_zero`:
    `f^n = 1` ⟹ `aeval f (X^n - 1) = 0` および `aeval f (∏_{d∣n} Φ_d) = 0`。
  - **Step 2 (done)** Kernel sum decomposition:
    - `sup_ker_aeval_cyclotomic_eq_ker_aeval_prod` — 任意 `Finset ℕ` で
      `⨆ d ∈ s, ker(aeval f Φ_d) = ker(aeval f (∏_{d ∈ s} Φ_d))`
      (Finset 帰納法 + `IsCoprime.prod_right` +
      `Polynomial.cyclotomic.isCoprime_rat` +
      `sup_ker_aeval_eq_ker_aeval_mul_of_coprime`)。
    - `sup_ker_aeval_cyclotomic_divisors_eq_top` — `f^n = 1` (n > 0)
      ⟹ `⨆_{d ∣ n} ker(aeval f Φ_d) = ⊤` (kernels span W)。
  - **Step 3 (done)** Pairwise disjointness ⟹ internal direct sum:
    - `disjoint_ker_aeval_cyclotomic_iSup_of_not_mem` — `a ∉ s` ⟹
      `Disjoint (ker(Φ_a)) (⨆ d ∈ s, ker(Φ_d))`
      (Step 2 + Mathlib `disjoint_ker_aeval_of_isCoprime`)。
    - `supIndep_ker_aeval_cyclotomic` — `s.SupIndep (fun d => ker(Φ_d))`
      (`Finset.supIndep_iff_disjoint_erase` 経由)。
    - `iSupIndep_ker_aeval_cyclotomic_divisors` — `iSupIndep` form
      (subtype-indexed by `↑(Nat.divisors n)`, `Finset.SupIndep.independent`
      alias 経由)。
    - `isInternal_ker_aeval_cyclotomic_divisors` — `f^n = 1` (n > 0) ⟹
      `DirectSum.IsInternal` for `(ker(aeval f Φ_d))_{d ∣ n}`
      (`isInternal_submodule_iff_iSupIndep_and_iSup_eq_top` + Step 2 +
      `iSup_subtype`)。 Step 4 (trace 公式) の直接入力。
  - **Step 4 (done)** Trace decomposition + per-block integrality:
    - Step 4 partial (PowCompositeTrace.lean):
      - `aeval_apply_comm_f` — `aeval f p (f v) = f (aeval f p v)`
      - `mapsTo_f_ker_aeval_cyclotomic` — `f` は `ker(aeval f Φ_d)` を保つ
      - `trace_eq_sum_trace_restrict_ker_aeval_cyclotomic_divisors`
        (`[FiniteDimensional ℚ W]`) — `f^n = 1` ⟹
        `trace f = ∑_{d ∣ n} trace(f.restrict ker(Φ_d))`
    - Step 4 full (`Foundations/GroupTheory/CyclotomicGenericTrace.lean` 新規):
      - `nextCoeff_cyclotomic_rat_isInt` — `nextCoeff (cyclotomic d ℚ) ∈ ℤ`
        (map_cyclotomic_int + `Int.cast_injective` 経由)
      - `trace_quotient_cyclotomic_X_isInt` —
        `Algebra.trace ℚ (ℚ[X]/Φ_d) [X] ∈ ℤ` (PowerBasis + nextCoeff 整数性)
      - `trace_int_of_cyclotomic_aeval_eq_zero` — `aeval T (cyclotomic d ℚ) = 0`
        + `0 < d` ⟹ `trace ℚ M T ∈ ℤ` (prime-case の generic 一般化)
    - Step 4 full (PowCompositeTrace.lean に上載せ):
      - `aeval_restrict_apply` — generic aeval-restriction commute
      - `aeval_cyclotomic_f_restrict_eq_zero` — restriction が Φ_d で消える
      - `trace_restrict_ker_aeval_cyclotomic_isInt` — per-block trace ∈ ℤ
      - **`trace_int_of_pow_eq_one`** — `f^n = 1` (n > 0) ⟹
        `trace ℚ W f ∈ ℤ`。 **B4.1 prime version の composite 一般化**。
        per-block 整数性の和は整数、Step 4 partial + Step 4 full per-block 結合。
  - **Step 5-6 (deferred)** 残り:
    - Step 5: specialise to `n = 25` for Lem 13 p=5 starred rows
      (`trace_int_of_pow_eq_one` を `σ^25 = 1` で直接適用、aut wrapping)
    - Step 6: apply via `Moore57Graph/Aut/TraceIntegrality.lean` and close
      `lem13_starred_row_5_*_no_integer_trace`
  - paper §4 Prop 2 の rational-class character integrality 全形は依然遠い。
  - 必要度: paper-faithful proof には欲しいが、Moore57 specific には
    prime-order だけで dispatch 可能な行が多く、優先度は低。

### B5. Lem 13, Lem 14 paper-faithful 形

* **[B5.0] (部分 done)** Lem 13 starred rows は arithmetic core で
  処理済 (commit `f12e30e`)。 さらに 2026-05-20 夜 (commit `b35143b`)
  で fix-set monotonicity (`fixedVertexCount_le_pow`) +
  `graphAut_pow` helper を追加し、Lem 13 の追加 conditional rows:
  - `lem13_p5_a0_zero_of_pow5_zero` (p=5 (0,0) propagation)
  - `lem13_p3_a0_le_one_of_pow3_one` (p=3 (?, 1) constraint)
  - `lem13_p3_row_1_1_pow3_a1_zero` (p=3 (1,1) bridge to Lem 12 p=3 starred)
  さらに (commit `9ab7eca`) FixedData-parameterised row bridges:
  - `lem13_p3_a0_le_10_via_petersenFixedData_pow3` (Petersen σ³ → a₀(σ) ≤ 10)
  - `lem13_p5_a0_{zero, le_50, le_5}_via_{Empty, HS, C5}FixedData_pow5`
  full 6-row table を char-theoretic に ⟶ Theorem 3 / Prop 2 待ち、deferred。
* **[B5.0+] (部分 done)** Lem 11 a₀/a₁ character chain (commit `f17f4df`):
  paper-faithful の `a₀(τστ⁻¹) = a₀(σ)` を `χ₀+χ₁+χ₂ = a₀` + chi_conj 経由
  で再導出 (`lem11_a{0,1}_via_characters`)。
* **[B5.0+] (部分 done)** Lem 12 paper-faithful wrappers (commit `f17f4df`):
  - `lem12_p2_a0_56` / `lem12_p2_a1_112` (involution wrap)
  - `lem12_p5_a0_dispatch` (Empty/C5/HS FixedData dispatch via Nonempty)
  - `lem12_p13_a0_zero_from_emptyFixedData`
  - `lem12_p3_a0_ten_from_petersenFixedData` (Lem 12 p=3 non-starred)
  - `lem12_a0_one_from_singletonFixedData`
* **[B5.0+] (done)** Section 3 True-stub → proper signature unstub
  (commit `79cf986`, `f167ac0`):
  - Cor 1 `cor1_a1_le_500`: True-stub → `adjacentMovedCount_le_500` wrap
  - Lem 6 (3) `lem6_central_trace_le_two`: True-stub → proper-signature wrap
  - Lem 9 (1) `lem9_orbit_trace_formula`: True-stub → orbit count formula wrap
  - Lem 10 `lem10_trace_bounds`: True-stub → Mohar bound wrap
  - Lem 11 `lem11_a2_via_characters` (character chain a₂ conj)
* **[B5.1] (部分 done)** `lem14_arithmetic_decomp` (`a₁ ≡ b₁_P + b₁_Q
  (mod n)` ℤ-arithmetic packaging) 既に done。
  さらに `lem15_no_pq_14_a0_49_conditional` (Lem 15 pq=14 row, commit `b35143b`)
  + Lem 17/18/19 dispatch numeric bounds (commit `51a70a5`).
  full semi-regular 軌道分解は character + Prop 2 依存、deferred-heavy。

* **[B-final] (done, 2026-05-21 晩 / commit `40bb98a`)** Tier B
  True-stub finalization:
  - **`lem11_ai_constant_on_rational_classes`** を True-stub から
    proper conditional bridge に格上げ。 hypothesis として
    "Theorem 3 → 各 χⱼ が rational class 上定数" を取り、Theorem 1
    の inverse formulas (a₀ = χ₀+χ₁+χ₂, a₁ = 57χ₀+7χ₁−8χ₂) 経由で
    a₀, a₁ の rational class invariance を導く形に書き換え。 これで
    Curtis–Reiner Theorem 3 への依存を Lean 型レベルで明示。
  - **`Theorem3RationalClasses : Prop`** def 新設
    (`Section04_Characters/Theorem3_RationalClasses.lean`): 任意の
    `ρ : Representation ℚ G V` で `ρ.character (σ^k) = ρ.character σ`
    (k coprime to orderOf σ) を `Prop` として encode。 下流補題が
    hypothesis として取れる。
  - **`Proposition2CharacterSystem : Prop`** def 新設
    (`Section04_Characters/Proposition2_CharacterSystem.lean`):
    rational character system の non-negative integer 解 statement。
  - 各 Lem 12/13/14/15 stub に **companion `XConclusion : Prop` def**:
    `Lemma12PrimeTableConclusion`, `Lemma13PrimeSquaredConclusion`,
    `Lemma14SemiRegularConclusion`, `Lemma15PQTableConclusion`,
    `Lemma15NoOrder65Conclusion`, `Lemma15NoPQ14A049Conclusion`。
    paper claim を Lean Prop として明示し、True-stub は backwards
    compat 用 placeholder として残す。
  - **設計上の意義**: Tier B の "残務" は Lean-未移植 external
    (Theorem 3 + Prop 2 + semi-regular orbit) 待ちだが、各 external 依存は
    今 proper `Prop` として記述済。 下流の paper-faithful proof は
    `(h_thm3 : Theorem3RationalClasses ρ)` 等を hypothesis に取って
    unconditional に進める形に整った。 これ以上の Tier B 内部進捗は
    上記 external が Mathlib に入る (あるいは別途 hand-roll される)
    のを待つ状態。

---

## 3. Tier C — Petersen / Hoffman–Singleton 構造

§6 Lem 17, 18 の geometric 部分; §8 Prop 3 の HS 固定型.

**進捗 (2026-05-21 夜)**: [C1.0]-[C1.2a+], [C2.0a], [C3.0]-[C3.6]
**すべて完了** (Tier C は scope 内すべて scope 終了状態)。 [C3.4] と
[C3.6] が本日 (2026-05-21 夜) 完了し、Lem 17 (1)/(2), Lem 18 (1)/(2)/(3)
に semi-regular hypothesis を直接受ける unconditional wrapper +
Prop 3 (Fix=HS ⟹ |X|≤5) の proper conditional bridge が追加された。
**スキップ確定**: [C1.2b] Aut(Petersen), [C2.1] HS explicit, [C2.2] Aut(HS),
SRG 一意性 — Moore57 文脈では一切不要(下記 §3.0 で議論)。

### 3.0 不要項目の整理 (2026-05-21 追記)

`PetersenFixedData` / `HSFixedData` は **explicit isomorphism + 誘導次数** の
データだけを持ち、Lem 17/18 もこれだけで通る(`lem17_case1_complement_count_eq_54`
等は誘導次数 → `|N(a)\Fix(σ)|` の数値だけ使用)。`Aut(Petersen)` や `Aut(HS)` の
order は実際の証明チェーンに**一切登場しない**。

加えて `HSFixedData` は `induced_adj_iff` を explicit HS graph 経由でなく
**SRG(50, 7, 0, 1) パラメータ条件** (`Set.ncard` ベース) で規定しているので、
HS の explicit 50 頂点構築すら **不要**。Cameron Ch3 §6 でも:
> "Moore57 non-existence does not depend on the existence
>  of the Hoffman-Singleton graph; only on numerical constraints."
と明記され `[out-of-scope]` タグ済。

**スキップ確定リスト**:
| 項目 | 当初想定 | 実際 |
|---|---|---|
| `Aut(Petersen) ≅ S₅` | C1.2b | ❌ 不要 — Lem 17/18 で order 参照なし |
| SRG(10,3,0,1) ⟹ ≅ Petersen 一意性 | (暗黙) | ❌ 不要 — `induced_adj_iff` で explicit に紐付け済 |
| HS explicit 50頂点構築 | C2.1 | ❌ 不要 — `HSFixedData` は SRG パラメータベース |
| `Aut(HS) = 252,000` | C2.2 | ❌ 不要 — Lem 18 で order 参照なし |
| SRG(50,7,0,1) 一意性 | (暗黙) | ❌ 不要 — 同上 |
| Subgraph embedding `Petersen ↪ Moore57` | C1.3, C2.3 | △ FixedData で σ-依存版は済、抽象 embedding は不要 |

### C1. Petersen graph の Lean 化

* **[C1.0] (done)** `Moore57.petersenGraph : SimpleGraph (Fin 10)` 構築
  (GP(5,2) 形式: 5 outer pentagon + 5 inner pentagram + 5 spokes = 15 edges)。
  `Foundations/GraphTheory/PetersenGraph.lean`.
* **[C1.1] (done)** `petersenGraph_isSRG : petersenGraph.IsSRGWith 10 3 0 1`
  by `decide` (fin_cases + decidable Adj)。
* **[C1.1+] (done)** Petersen 追加性質:
  - `petersenGraph_edgeFinset_card = 15` (handshaking)
  - `petersenGraph_triangleFree` (λ = 0 から)
  - `petersenGraph_no_C4` (girth ≥ 5: case 分けで)
* **[C1.2a] (done)** `IsPetersenLike G ↔ G.IsSRGWith 10 3 0 1` 抽象 predicate。
  `Foundations/GraphTheory/SRGPredicates.lean`.
* **[C1.2a+] (done)** abstract edge count bridges:
  - `isPetersenLike_edgeFinset_card = 15`
  - `isHoffmanSingletonLike_edgeFinset_card = 175`
* **[C1.2b] ~~Aut(Petersen) ≅ S₅~~ — skip** (Moore57 で使用箇所なし)。
* **[C1.3] ~~General `Petersen ↪ Moore57` embedding~~ — skip**
  (`PetersenFixedData` で σ-依存版は提供済。抽象 embedding 命題は使用箇所なし)。

### C2. Hoffman–Singleton graph の Lean 化

* **[C2.0a] (done)** `IsHoffmanSingletonLike G ↔ G.IsSRGWith 50 7 0 1` 抽象 predicate。
  Existing `Foundations/GraphTheory/HoffmanSingleton.lean` は classification 側
  (k² + 1 形 SRG の k ∈ {0,1,2,3,7,57} を導く)。
* **[C2.1] ~~HS explicit 50-vertex construction~~ — skip**
  (`HSFixedData` が SRG パラメータベースで Lem 18 を通す設計のため不要)。
* **[C2.2] ~~Aut(HS) = 252,000~~ — skip** (Lem 18 で order 参照なし)。
* **[C2.3] ~~HS ↪ Moore57 embedding~~ — skip** (`HSFixedData` で σ-依存版で十分)。

### C3. Lem 17, 18 geometric 部分の接続

* **[C3.0] (done)** `Moore57.PetersenFixedData Γ σ` structure
  (`Moore57Graph/Aut/PetersenFixedData.lean`):
  10 固定点 `v : Fin 10 → V` + injectivity + σ-fix + span + induced adj
  iff matches `petersenGraph`. Plus bridges:
  - `induced_degree_three`: 各 v(i) は 9 個の他指標頂点中 3 個に隣接。
  - `autFixedNeighborFinset_card_eq_three`: `|N(a) ∩ Fix(σ)| = 3`。
  - `petersenFixedData_complement_neighbor_count`: `|N(a) \ Fix(σ)| = 54`。

* **[C3.1] (done)** `Moore57.HSFixedData Γ σ` structure
  (`Moore57Graph/Aut/HSFixedData.lean`):
  50 固定点 + injectivity + σ-fix + span + SRG(50, 7, 0, 1) induced
  conditions (`induced_regular`, `induced_lambda`, `induced_mu` via
  `Set.ncard`). Plus bridges:
  - `induced_degree_seven`: 各 v(i) は 49 個の他指標頂点中 7 個に隣接。
  - `autFixedNeighborFinset_card_eq_seven`: `|N(a) ∩ Fix(σ)| = 7`。
  - `hsFixedData_complement_neighbor_count`: `|N(a) \ Fix(σ)| = 50`。

* **[C3.3] (done)** `Lemma17_3Group.lean` / `Lemma18_5Group.lean` に bridge:
  - `lem17_case1_complement_count_eq_54` (Petersen 経由 `|N(a) \ Fix(σ)| = 54`)。
  - `lem17_case1_orderOf_dvd_27_with_petersenFixedData` (conditional bridge:
    PetersenFixedData + `h_semi_regular : orderOf σ ∣ 54` ⟹ `orderOf σ ∣ 27`)。
  - `lem18_case1_complement_count_eq_50` (HS 経由 `|N(a) \ Fix(σ)| = 50`)。
  - `lem18_case1_orderOf_dvd_25_with_HSFixedData` (HS 版)。

* **[C3.4] (done, 2026-05-21)** Semi-regular orbit argument.
  `⟨σ⟩` の `N(a) \ Fix(σ)` 上の作用が semi-regular (= stabilizer trivial)
  であることから `orderOf σ ∣ |N(a) \ Fix(σ)|` を出す Foundations 一般
  helper + graph-aut bridge + 各 FixedData wrapper + Lem 17/18 内側
  unconditional wrapper を全 5 ステップで整備:
  - `Foundations/GroupAction/SemiRegularOrbit.lean` (新規) — 一般
    `Moore57.orderOf_dvd_card_of_semiRegular`. Orbit partition 帰納法。
    補題 `cyclicOrbitFinset.card_eq_orderOf` (semi-regular orbit のサイズ),
    `cyclicOrbitFinset.subset_of_invariant` (σ-invariant Finset への
    orbit 帰属) も同時に。
  - `Moore57Graph/Aut/SemiRegularComplement.lean` (新規) —
    `autMovedNeighborFinset Γ σ v := N(v).filter (σ w ≠ w)` の σ-invariance
    と `orderOf_dvd_card_movedNeighbour_of_semiRegular` bridge。
  - 各 FixedData (`Petersen / HS / C5 / K155 / Singleton / Empty`) に
    `*_orderOf_dvd_N_of_semiRegular` wrapper を追加 (Petersen 54, HS 50,
    C5 55, K155 center 2 / leaf 56, Singleton 57, Empty 3250)。
  - `Lemma17_3Group.lean`, `Lemma18_5Group.lean` に `*_semiRegular`
    接尾辞の wrapper 5 個:
    `lem17_case{1,2}_orderOf_dvd_{27,3}_with_{petersen,singleton}FixedData_semiRegular`,
    `lem18_case{1,2,3}_orderOf_dvd_{25,5,125}_with_{HS,c5,empty}FixedData_semiRegular`。
  - **Lem 17 case (2) sharpening**: paper の `|X| ∣ 81` より厳しい
    `|X| ∣ 3` を C3.4 から直接得る (57 = 3·19 と 3-group の互いに素性)。
  - 既存の conditional 版 (`_with_*FixedData`、`h_semi_regular : orderOf σ ∣ N`
    を hypothesis に取る) は backward-compat で残置。
  - 「semi-regular 自体」は依然 separate な hypothesis として残置
    (MS 2010 §6 では Lem 21 = `Fix(σ^l) = Fix(σ)` で establish,
    paper-faithful Lem 21 整備は別タスク)。

* **[C3.5-pre] (done)** PetersenFixedData / HSFixedData の girth bridges:
  - `induced_triangleFree`, `induced_no_C4` (各 FixedData)
  - `induced_adj_pairs_card_eq_30` (PetersenFixedData の Fin 10 × Fin 10
    ordered edge count, `decide` で Petersen.Adj に reduce)

* **[C3.5] (done)** Lem 17/18/19 case (2-3): pentagon / empty / singleton
  接続。`SingletonFixedData` + `EmptyFixedData` 新規作成
  (`Moore57Graph/Aut/SingletonAndEmptyFixedData.lean`)。 既存 `C5FixedData` /
  `K155FixedData` (`FixedSubgraphData.lean`) に bridge を追加:
  - 各 FixedData に `fixedVertexCount_eq_*` (Petersen 10, HS 50, C5 5,
    K155 56, Singleton 1, Empty 0)
  - 各 FixedData に `autFixedNeighborFinset_card_eq_*` + complement count
    bridge (Petersen 3→54, HS 7→50, C5 2→55, K155 center 55→2, K155
    leaf 1→56, Singleton 0→57, Empty global 3250)
  - **Lem 4 (§2 odd-prime classification)**:
    `lem4_case{1,2,4,5,6}_with_{Empty,Singleton,C5,Petersen,HS}FixedData`
    で各 case を FixedData parameterise。case (3) は star general
    `2 + 7l` で K155 (= 56 ≠ 2 + 7l) と異なるためスキップ。
  - **Lem 17/18/19 wrappers**: 各 case で
    `lem{17,18,19}_case{n}_orderOf_dvd_*_with_*FixedData` conditional
    wrapper を追加。

* **[C3.6] (done, 2026-05-21 夜)** §8 Prop 3: `Fix(X) = HS ⟹ |X| ≤ 5`。
  `Section08_Theorem5Proof/Proposition3_HSFixBound.lean` に proper
  signature 化:
  - `prop3_arithmetic_dvd_25_ne_25_le_5` (arithmetic step: n ∣ 25 ∧ n ≠ 25
    ⟹ n ≤ 5)
  - `prop3_hs_fix_bound_with_hsFixedData` (Lem 18 (1) numeric 入力経由の
    conditional bridge)
  - `prop3_hs_fix_bound_with_hsFixedData_semiRegular` (C3.4 semi-regular
    hypothesis 経由)
  - `Proposition3HSFixConclusion : Prop` abstract conclusion def
  - `Proposition3Step5Conclusion : Prop` + `prop3_step5_conclusion_holds`
    (arithmetic core を Prop-level に packaged)
  既存の True-stub `prop3_hs_fix_bound` は backward-compat で残置。
  残るのは paper §8 step 1-4 の Lean 化 (orbit decomposition + trace
  argument + simultaneous eq derivation) で `h_no_25 : orderOf σ ≠ 25`
  hypothesis を unstub する作業 — substantive で別タスク。

---

## 4. Tier D — Rank-3 perm group framework (Higman 1964)

§§1-2 of Higman 1964 全体 (Lems 1-7 抽象版)。Aschbacher Lem 1.4 一般版もここ。

### D1. Mathlib `MulAction` 拡張

* **[D1.0] (調査)** `Mathlib.GroupTheory.GroupAction` に **rank** 概念はあるか?
  - `MulAction.orbit`, `MulAction.stabilizer` はある。
  - `rank G Ω := |G \\ (Ω × Ω)|` (orbital 数) — 自前定義必要。

### D2. Orbital structure infrastructure

* **[D2.0] (done, 2026-05-21)** `Moore57.orbital G Ω` (Ω × Ω の G-軌道
  quotient) + `permRank G Ω : ℕ` (rank = orbital 数) +
  `SameOrbital` 関係を `Foundations/GroupTheory/RankAndOrbital.lean`
  に追加。 `sameOrbital_iff`: `SameOrbital G Ω a b ↔ ∃ g, g • b = a`。
  Mathlib `Prod.mulAction` (diagonal action on Ω × Ω) を利用。
* **[D2.1] (done, 2026-05-21)** Paired orbital `swapOrbital : orbital G Ω →
  orbital G Ω` を `Prod.swap` (diagonal action と G-equivariant) で induce
  (`Quotient.map'` 経由)。 `swapOrbital_involutive` (involution),
  `swapOrbital_mk` (representative lift) も整備。
* **[D2.2] (done, 2026-05-21)** `IsSelfPaired O := swapOrbital G Ω O = O`
  定義 + `diagonalOrbital a := Quotient.mk'' (a, a)` (対角 orbital) +
  `isSelfPaired_diagonalOrbital` (対角 orbital は常に自己paired)。
  「偶位数 ⇔ 非対角の自己paired orbital が存在」(Lem 1 主形) は Cauchy
  経由で重く、deferred (D3.0 参照)。

### D3. Higman 1964 Lems 1-7 抽象版

* **[D3.0] (done, 2026-05-21)** Lem 1: paired orbit ⇔ even order。
  Cauchy + pairing。 `Lemma01_PairedOrbits.lean` に以下を追加:
  - `lem1_self_paired_iff_swap_fixed`: `IsSelfPaired O ↔ swapOrbital O = O`
    (定義の paper-faithful 言い換え)
  - `lem1_diagonal_self_paired`: 対角 orbital は常に自己paired
  - `lem1_swapOrbital_involutive`: pairing は involution
  - `lem1_self_paired_orbital_of_order_two`: 「order-2 element τ + 動かす
    点 a ⟹ ⟦(a, τ•a)⟧ が non-diagonal self-paired」(⟸ 構成)
  - `lem1_swap_element_of_self_paired`: non-diagonal self-paired ⟹
    swap element g (g•a = b, g•b = a)
  - `lem1_even_card_of_non_diagonal_self_paired`: non-diagonal self-paired
    ⟹ 2 ∣ |G| (⟹ |G|-form; faithfulness 不要)。
    Proof: g² ∈ Stab(a) but g ∉ Stab(a), Nat.mod parity contradiction.
  - `lem1_order_two_of_even_card`: Cauchy at p = 2 wrap
  - 完全 iff packaging (moved-point witness 付きで ⟸,
    unconditional で ⟹) + 対偶
    `lem1_no_non_diagonal_self_paired_of_odd_card`。
* **[D3.1] (done, 2026-05-21)** Lem 2: intersection numbers λ, μ, λ₁, μ₁
  の定数性 (rank-3 仮定下)。 `RankAndOrbital.lean` に以下の構造を追加:
  - `orbitalNeighborhood O a := { c | (a, c) ∈ O }` (orbital が定める
    "近傍" 集合)
  - `quotient_mk_smul`: orbital quotient は G-equivariant
  - `mem_orbitalNeighborhood_smul_left`: membership form の
    G-equivariance bridge
  - `orbitalIntersectionCount O₁ O₂ a b := |N_{O₁}(a) ∩ N_{O₂}(b)|`
    (`Nat.card` 経由)
  - `orbitalIntersectionCount_smul`: G-invariance under diagonal action
    (bijection `c ↦ g⁻¹ • c` 経由)
  - `orbitalIntersectionCount_orbital_invariant`: 同じ orbital に属する
    `(a, b)` / `(a', b')` では count が一致 — paper-faithful な constancy
    主張
  - `IsRank3 G Ω : Prop := permRank G Ω = 3` (rank-3 predicate)
  - `Lemma02_IntersectionNumbers.lean` で
    `lem2_intersection_count_orbital_invariant` として paper-faithful wrap。
* **[D3.2] (done, 2026-05-21)** Lem 3: odd order rank-3 ⟹
  k = l, n = 2k+1, λ = μ。 unconditional main form 完成:
  - Stage A (`lem3_swap_pairs_non_diagonal_orbitals`): rank-3 + odd
    ⟹ swap が 2 つの non-diagonal orbital を pair (Lem 1 対偶を使う)
  - Stage B (`orbitalNeighborhood_card_eq_orbitalReverseNeighborhood_card`):
    transitive + Fintype Ω ⟹ in-deg = out-deg。 Proof: 両 sums
    `∑_x |N_O(x)|`, `∑_x |N⁻_O(x)|` が orbital preimage |O_pairs| と等しい
    (Sigma 双射 `orbitalPreimageFstEquiv`/`orbitalPreimageSndEquiv`)、
    G-invariance + transitivity で summand 定数化、`|Ω|` 約分。
  - 統合 (`lem3_subdegree_eq_of_odd_rank3`): transitive + rank-3 +
    odd |G| ⟹ `|N_{O₁}(a)| = |N_{O₂}(a)|` (= k = l).
  - その他: `lem3_in_deg_eq_out_deg` (Stage B wrap),
    `lem3_non_diagonal_orbitals_paired_of_odd_rank3` (paper-faithful
    paired conclusion)。
* **[D3.3] (done, 2026-05-21)** Lem 4: 不可約性 ⇔ G_a ≠ G_{Γ(a)}。
  Mathlib `MulAction.IsPreprimitive` bridge:
  - `lem4_stabilizer_le_stabilizer_orbitalNeighborhood`: 基本包含
    G_a ≤ G_{N_O(a)} (setwise)。
  - `lem4_isCoatom_stabilizer_iff_preprimitive`: Mathlib
    `isCoatom_stabilizer_iff_preprimitive` の direct wrap (Wielandt).
  - `lem4_not_preprimitive_of_stabilizer_lt`: 厳密包含 G_a <
    G_{N_O(a)} ∧ G_{N_O(a)} ≠ ⊤ ⟹ ¬ preprimitive (対偶)。
  paper の 3-way iff (rank-3 specific block 構造) は deferred-heavy
  維持 (Δ(a) ∪ {a} block 分析が必要)。
* **[D3.4] (done, 2026-05-21)** Lem 5: μl = k(k − λ − 1) 一般化。
  - `lem5_rank3_perm_group_form_int` (ℤ 形): `λk + μl = k(k − 1)` ⟹
    `μl = k(k − λ − 1)`. SRG 形と algebraically 等価だが、SRG packaging
    に依存しない直接 paper-faithful 形。
  - `lem5_rank3_perm_group_form_iff_int` (双方向)。
  - `lem5_rank3_perm_group_form_moore57`: ℤ form の Moore57 instance。
  - `orbitalIntersectionAt`: paper notation alias for D3.1
    intersection number。 `lem5_intersection_number_constant`: constancy
    の wrap。
* **[D3.5] (done, 2026-05-21)** Lem 6, 7: incidence matrix の eigenvalue 解析。
  Lem 7 multiplicity formula を `Lemma07_IntegralityCases.lean` に追加:
  - `lem7_multiplicity_formula`: `(s − t) · f₂ = −k − (n − 1) · t` (ℤ 形)。
    Derived from `f₂ + f₃ = n − 1` + `f₂ s + f₃ t = −k`.
  - `lem7_multiplicity_formula_sym` (f₃ 対称形)。
  - `lem7_case_two_divisibility_f2`/`_f3`: Case II divisibility 帰結。
  - `lem7_moore_e_dvd_k_times_k_minus_2`: Moore 特化 `2 e f₂ = k(k(e+1) − 2)`
    ⟹ `e ∣ k(k − 2)` (Thm 1 への integrality bridge)。
  Lem 6 discriminant 形 (`lem6_secondary_eigenvalues_via_discriminant`) は既存。
* **[D3.6] (done, 2026-05-21)** Thm 1 full: n = k² + 1 ⟹ k ∈ {2, 3, 7, 57}。
  `Theorem1_DegreeKSqPlus1.lean` に bridge を追加:
  - `theorem1_e_dvd_fifteen`: `e ∣ k(k−2) ∧ e² = 4k − 3` ⟹ `e ∣ 15`.
    Proof: `e ∣ 16 · k(k−2) = e⁴ − 2e² − 15` (4k = e² + 3 substitution),
    `e ∣ e⁴ − 2e²` so `e ∣ -15`.
  - `theorem1_e_sq_dvd_225_of_e_dvd_fifteen`: `e ∣ 15 ⟹ e² ∣ 225`.
  - `theorem1_e_sq_dvd_225_of_dvd_and_sq`: 合成 bridge。
  - `theorem1_case_two_full_conditional`: Moore parameter Case II full
    chain (ℕ form) — `e² = 4k − 3 + multiplicity + k ≥ 2 ⟹ k ∈ {3, 7, 57}`。
  既存 `theorem1_arithmetic_core` + 新 bridge で full chain 完成。

### D4. Aschbacher 1.4 一般版

* **[D4.0] (done, 2026-05-21)** `f = k ± 1` 二者択一 (involution 不動点星型分類)。
  `Lemma1_4_InvolutionFix.lean` に algebraic core を追加:
  - `asc1_4_arithmetic_core`: `(f - k - 1)(f - k + 1) = 0 ⟹ f = k ± 1`。
  - `asc1_4_arithmetic_core_sq`: 等価な square form `(f - k)² = 1 ⟹ f = k ± 1`。
  - `asc1_4_arithmetic_core_iff`: 双方向 packaging。
  - `asc1_4_moore57_arithmetic_instance`: Moore57 (k=57, f=56) instance。
  既存: 完全 Moore57 instance (`f = 56 = k − 1`) は既 proven (Phase 1-3)。
* **[D4.1] (done, 2026-05-21)** SRG eigenvalue + multiplicity → integer 制約 →
  二者択一 (Cor 形)。 `Aschbacher1971.MainTheorem.lean` に combined Cor を追加:
  - `asc_cor_combined_classification`: D3.5 + D3.6 (Case II Moore chain) +
    D4.0 (involution dichotomy) を組み合わせて、(k, f) pair classification:
    `k ∈ {3, 7, 57} ∧ f ∈ {k − 1, k + 1}`。
  - `asc_cor_moore57_instance`: (57, 56) instance。

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

**進捗 (2026-05-20 夜)**: [E1.x], [E2.0], [E3.0], [E4.0] は **完了** (commits `e673d3d`, `5595d66`).

* **[E1.0]** Prop 6 dispatch (p=3, q=5): |X| = 3^a · 5^b。**[done]**
  - **[E1.1]** ✅ `prop6_sylow5_count_one_of_3pow_dvd_27`: 純ℕ arithmetic
    (`n5 ∣ 27 ∧ n5 ≡ 1 (mod 5) ⟹ n5 = 1`)。
  - **[E1.2]** ✅ `prop6_sylow5_normal`: Mathlib lift で Sylow 5 が `Normal`
    (`Sylow.normal_of_subsingleton` 経由)。Schur–Zassenhaus 接続は次のステップ。
  - **[E1.3]** ✅ `prop6_card_dvd_135_or_375` (既存) との接続済み。

* **[E2.0]** Prop 7 dispatch (p=3, q ∈ {7, 13, 19}): **[done]**
  - `prop7_q{7,13,19}_sylow{7,13,19}_normal`: 各 q について Mathlib lift 済。
  - q = 11 は Lem 26 で除外済 (この dispatch には登場しない)。

* **[E3.0]** Prop 8 dispatch (p=5, q ∈ {7, 11}): **[done]**
  - `prop8_q{7,11}_sylow{5,7,11}_normal`: 各 q について Mathlib lift 済。
  - q = 7 case では Sylow 5 と Sylow 7 の両方が normal → X ≅ Z₃₅。

* **[E4.0]** Thm 7 dispatch (|G| even): **[done]**
  - `thm7_card_110_sylow11_normal`: **3-prime case 110 = 2·5·11**。
    Sylow 11 が normal (`n₁₁ ∣ 10 ∧ ≡ 1 (mod 11) ⟹ n₁₁ = 1`)。
    Hall {5, 11}-部分群を取り出す前提が整い、Philip Hall 定理は不要に。
  - `thm7_card_{50,54,14,22,38}_sylow{5,3,7,11,19}_normal`: 残り 5 個の
    候補 order についても同様に Sylow normal。

* **[E5.0]** 次のステップ: **Aut(Γ) ↔ `Subgroup (Equiv.Perm V)` bridge + 全体の接続**
  - 既存 `cor3_unified_arithmetic_bound` (proven) と Sylow.Normal lemmas を
    組み合わせて、Cor 3 の `|Aut(Γ)| ≤ 375` の Mathlib-level 形式化。
  - 必要な追加要素:
    - `Aut(Γ)` の order を `Subgroup (Equiv.Perm V)` の `Nat.card` として表現。
    - Mathlib の `Sylow.card_dvd_index` の具体応用 (`Sylow p G index = N/p^k`)。
    - Sylow normal subgroup + Schur–Zassenhaus → semidirect product 構造。
  - ※ 残りは graph-theoretic side (Lem 17/18 geometric, MP 2001 structure)
    に依存するので、ここで [E] は一旦完了とする。

* **[E5.1] (done, 2026-05-21)** Sylow + Schur-Zassenhaus bridge
  (`Foundations/GroupTheory/SylowSchurZassenhaus.lean`):
  `Sylow.exists_complement_of_normal` — 正規 Sylow p-subgroup は必ず
  complement を持つ (Mathlib `Subgroup.exists_right_complement'_of_coprime`
  + `Sylow.card_coprime_index`)。 これで proven `prop6_sylow5_normal` /
  `prop7_q*_sylow*_normal` / `prop8_q*_sylow*_normal` / `thm7_card_*_sylow*_normal`
  の各成果を「semidirect product 構造」に格上げできる generic helper が
  揃った (Mathlib level)。 Feit-Thompson / Philip Hall 経由せず Sylow
  だけで Hall {p}-subgroup を取り出す paper のロジック (§5.1) が Lean で
  支えられる形に。

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

**進捗 (2026-05-21 深夜)**: 旧 1〜16 項目 + 本日 3 並行セッション
([C3.4], [C3.6], [D3.0]–[D3.6], [D4.0], [D4.1], [B4.3 Step 2-4])
すべて **完了**。 これにより Tier C/D の scope 全閉鎖、B4.3 も
Moore57 specific な wire-up (Step 5-6) を残すのみ。

1. ~~**[E1.1]** Prop 6 Sylow analysis~~ — **done** (commit `e673d3d`)。
2. ~~**[E4.0]** Thm 7 Sylow analysis (110 dispatch)~~ — **done**。
3. ~~**[E5.0]** `autSubgroup` + Cor 3 bridge~~ — **done**。
4. ~~**[A2.0]** SG(625, 12) = Heis(F₅) × Z₅ 構築~~ — **done**。
5. ~~**[A2.1]** SG(625, 12) GAP 不変量検証~~ — **done**。
6. ~~**[B4.1]** Cyclotomic integer trace for prime order p~~ — **done**
   (commit `be8c0d7`)。
7. ~~**[B4.2]** Starred p-prime row dispatch using B4.1~~ — **done**:
   - `lem12_no_p7_a0_58` (Lem 12 p=7 starred row): True-stub →
     False 証明に格上げ。
   - `lem13_p3_row_1_1_no` (Lem 13 p=3 (?, 1) starred row): B4.1 経由で
     unconditional False。
8. ~~**[B3.1+]** χⱼ subrep + character identification (全 3 character)~~
   — **done**: `chi{0,1,2}Subrep` + `chi{0,1,2}_eq_chi{j}Subrep_character`
   を `SpectralSubrepresentation.lean` に追加。
9. ~~**[A1.1]** Mathlib IsPGroup 分類調査~~ — **done (orientation, negative)**:
   Mathlib には位数 `p⁴` 群の分類は無い。15 群直接構築が必要 (重い)。
10. ~~**[E5.1]** Sylow + Schur-Zassenhaus bridge~~ — **done**:
    `Sylow.exists_complement_of_normal` を `SylowSchurZassenhaus.lean`
    に追加。
11. ~~**[D2.0]** orbital structure 定義~~ — **done**:
    `orbital G Ω`, `permRank G Ω`, `SameOrbital` を
    `RankAndOrbital.lean` に追加。
12. ~~**[D2.1, D2.2]** Paired orbital + self-paired criterion~~ —
    **done** (commit `67c6e69`): `swapOrbital`, `IsSelfPaired`,
    `isSelfPaired_diagonalOrbital` を `RankAndOrbital.lean` に追加。
13. ~~**[A2.2-minimal]** SG625_12 の Heis × Z₅ subgroup 分解~~ —
    **done**: `heisSubgroup`, `z5DirectFactor` + 順序 / 正規性 / 中心包含
    / 共通根 ⊥ を `SmallGroup625_12.lean` に追加。
    **Tier A 全体の投資判断**: 重い uniqueness work (A1.2, A3, A4) は
    downstream consumer 無し (`grep` 確認済) のため現時点で着手非推奨。
14. ~~**[B-final]** Tier B True-stub finalization~~ — **done**
    (commit `40bb98a`): `lem11_ai_constant_on_rational_classes` を
    proper conditional bridge に + `Theorem3RationalClasses`,
    `Proposition2CharacterSystem`, `Lemma{12,13,14,15...}Conclusion :
    Prop` defs を全 §4–§5 True-stub に追加。 Tier B 内部進捗はこれ以上
    external (Theorem 3 + Prop 2 + semi-regular) 待ち。
15. ~~**[C3.4]** Semi-regular orbit argument~~ — **done (2026-05-21 夜)**:
    Foundations 一般 helper (`SemiRegularOrbit.lean`) + graph-aut bridge
    (`SemiRegularComplement.lean`) + 全 FixedData wrapper + Lem 17/18
    内側 unconditional wrapper (詳細は §3 C3.4)。
16. ~~**[C3.6]** Prop 3 (Fix=HS ⟹ |X|≤5) proper-signature 化~~
    — **done (2026-05-21 夜)**: arithmetic step + Lem 18 (1) 経由
    conditional bridge + C3.4 semi-regular 経由 unconditional bridge +
    `Proposition3HSFixConclusion / Step5Conclusion` abstract Prop defs
    を `Proposition3_HSFixBound.lean` に追加 (詳細は §3 C3.6)。
17. ~~**[B4.3]** Composite-order Galois cyclotomic decomp~~ — **Step 2-4
    full done (2026-05-21 深夜)**: `Foundations/LinearAlgebra/PowCompositeTrace.lean`
    + `Foundations/GroupTheory/CyclotomicGenericTrace.lean` で
    `trace_int_of_pow_eq_one` (任意 n) まで到達。 Step 5-6 (Moore57 wire-up) 残。
18. ~~**[D3.0]–[D3.6] + [D4.0]–[D4.1]**~~ — **done (2026-05-21 夜)**:
    Higman 1964 §§1-2 (Lems 1-7 抽象版) + Aschbacher 1.4
    (involution dichotomy + combined Cor) すべて paper-faithful 化。
19. **[★ 次の短期項目]** 候補:
   - **[B4.3 Step 5]** `trace_int_of_pow_eq_one` を Moore57 wire-up:
     - `σ ∈ Aut(Γ)` の permMatrix 経由で W = E₇.range への ℚ-linear
       endomorphism として認識
     - n = 25 specialize (orderOf σ = 25 case)
     - `aut_pow_E7_trace_int_composite` (`σ^n = 1` ⟹ `tr(E₇·P_σ) ∈ ℤ`)
       を B4.1 prime-order 版の真の一般化として追加
   - **[B4.3 Step 6]** `lem13_starred_row_5_*_no_integer_trace` の
     unstub (B4.3 Step 5 経由)。 これで Lem 13 p=5 starred の
     order-25 row が unconditional False に。
   - **[Lem 21]** `Fix(σ^l) = Fix(σ)` paper-faithful 整備
     (C3.4 で残った "semi-regular 自体" hypothesis を unstub するための
     paper-faithful 前提、MS 2010 §6)。 中規模 (≥ 1 commit)。
   - **[Tier A]** A1.2 / A3 / A4 — downstream consumer 無しで非推奨。
   - **[B5.0 full / B5.1 full]** paper-faithful 6-row Lem 13 / 17-row
     Lem 12 + semi-regular orbit decomposition — Theorem 3 全形 + Prop 2
     依存で deferred-heavy。

### 7.2 中期 (multi-commit、各 200-1000 LOC)

8. **[A1.1] + [A1.2]** SG(81, 9) uniqueness (15-group enumeration + filter)。
9. **[E2.0] + [E3.0] 再整備** Prop 7, 8 の Aut(Γ) ↔ subgroup 接続強化。
10. **[B3.1+]** χⱼ を `Representation.character` of spectral subrep として
    formally identify (現状は trace 関数定義だけ。 subrep 同型までは未)。
11. **[B5.0+] / [B5.1] 拡張** Lem 11/12/13/14 の残る paper-faithful 形 +
    semi-regular 軌道分解 (Prop 2 依存度の高い部分)。

### 7.3 長期 (substantive new infrastructure)

12. ~~**[C3.4]** Semi-regular orbit argument~~ — **done (2026-05-21 夜)**:
    詳細は §3 C3.4 / §7.1 #15。
13. ~~**[B4.3]** Composite-order trace integrality~~ — **本質的に done
    (2026-05-21 深夜, B4.3 Step 4 full)**: `trace_int_of_pow_eq_one`。
    paper §4 Prop 2 の rational-class character system 全形は依然遠い
    が、Moore57 specific には不要。
14. ~~**[D1-D4]**~~ — **done (2026-05-21 夜)**: Rank-3 perm group
    framework + Higman 1964 Lems 1-7 + Aschbacher 1.4 すべて Lean 化。
15. **[A3, A4]** Order-625 group classification (Lem 22, Prop 4) —
    downstream consumer 無しで投資非推奨 (Tier A 投資判断 §1 参照)。
16. **Lem 21**: `Fix(σ^l) = Fix(σ)` paper-faithful 整備 — C3.4 で残った
    "semi-regular 自体" hypothesis を unstub する paper-faithful 前提。
17. **[Theorem 3 全形 / Prop 2]** Lean 化 (composite-order trace integrality
    は B4.3 でカバー済、残るは rational class character system non-neg
    integer solution 等の「分類論」側)。 Mathlib RepresentationTheory
    が将来整備されたら自然に乗る位置。 paper §4 Prop 2 として encode 済。

### 7.4 見送り推奨

16. **[F1, F2]** Lem 6 (4) corner cases (|O| ∈ [5, 63])。
    Mohar bound (|O| ≥ 64) があれば実用上問題なし。
17. **[C1.2b, C1.3, C2.1, C2.2, C2.3]** Petersen/HS の Aut group, explicit
    HS 構築, 一意性, 抽象 embedding ── Moore57 で**使用箇所が存在しない**
    (§3.0 参照)。

---

## 8. ボトルネック識別 ── 「不要な依存」リスト

paper を素直に読むと必要に見えるが、Moore57 specific には不要な定理:

| 定理 | 当初推測 | 実状 (2026-05-21 深夜) |
|---|---|---|
| Feit–Thompson (奇数位数定理) | §9 Thm 6 で必須 | **不要**: |G| ≤ 375 odd は ≤ 2 distinct primes ⟹ Sylow + Schur-Zassenhaus で十分 |
| Philip Hall (Hall π-部分群存在) | §9 Thm 6/7 で必須 | **不要**: 2-prime case は Sylow = Hall, 3-prime case 110 は Sylow 11 normal で取れる |
| Burnside p^a q^b 可解性 | §9 で必要かと推測 | **不要**: 解能性経由せず Sylow 直接で処理可 |
| 一般 SRG 分類 (k ∈ {2, 3, 7, 57}) | Aschbacher Lem 1.3 で必須 | **不要 (Moore57 instance level)**: Higman 1964 算術 core (`theorem1_arithmetic_core`) 経由で Moore57 k=57 は Cameron 3.13 で済む。 加えて Tier D D3.5/D3.6/D4.x 完了で paper-faithful 形 (k ∈ {3, 7, 57}) も Lean 化済 |
| ~~Curtis–Reiner Theorem 3 (trace integrality)~~ | §4 Lem 12/13 starred で必須 | **本日 B4.3 Step 4 で取得**: `trace_int_of_pow_eq_one` (任意 n)。 prime-order は B4.1、composite-order は B4.3 で対応。 paper §4 Prop 2 の rational-class character system 全形のみ deferred |
| ~~Petersen / HS explicit graph~~ | §6 Lem 17/18 で暗黙必須 | **不要**: `PetersenFixedData` / `HSFixedData` の SRG パラメータベース設計で十分 (§3.0)。 |

paper-level の **本当の** ボトルネック (2026-05-21 深夜):
- **GAP SmallGroup library**: Lean 等価物が無いため手構築必須 (Tier A)。
  SG(81,9), SG(625,12) 本体は手構築済、uniqueness (15 群 / 10 群 enumeration)
  が残るが downstream consumer 無しで投資非推奨。
- **Lem 21 paper-faithful** (`Fix(σ^l) = Fix(σ)`): C3.4 で残った
  semi-regular hypothesis 自体を unstub するための前提。 中規模仕事。
- **paper §4 Prop 2** (rational character system non-neg integer
  solution): Theorem 3 系の「分類論」側、まだ Lean 未整備。 ただし
  proper `Prop` def として encode 済 (B-final で)、下流 lemma は
  hypothesis として取れる。

### 8.1 知見の累積による状態変化 (2026-05-21 深夜 / 同日 3 並行セッション完了時点)

過去のロードマップ版 (commit `4805b0f` 起点 → `42e1662` papers scaffold)
と比べての地殻変動:

* **Theorem 3 が "全部" ボトルネック → prime-order だけ bypass 可能 (B4.1)
  → 任意 composite n で取得 (B4.3 Step 4 full)** へ。
  本日 B4.3 完成で `trace_int_of_pow_eq_one` (任意 n) を hand-roll で
  獲得。 既存 `Module.AEval` + cyclotomic.irreducible_rat (Mathlib) を
  活用し、prime-case proof body の generic 化で実現。 Moore57 specific な
  Step 5-6 wire-up で Lem 13 p=5 starred order-25 row も unconditional
  False になる位置に。
* **Tier C は scope 全閉鎖** (本日 C3.4 + C3.6 完了): SRG-parameter
  ベースの FixedData 設計で Aut(Petersen)/Aut(HS)/HS explicit/SRG 一意性
  をすべて bypass。 残る唯一の長期項目は Lem 21 paper-faithful 整備。
* **Tier D は paper §§1-2 + Aschbacher 1.4 全形 done** (本日 D3.0–D3.6,
  D4.0–D4.1 完了): rank-3 perm group framework が orbital quotient +
  swapOrbital + IsRank3 + IsPreprimitive で Lean object 化。
* **Cyclotomic infrastructure** が三層に層化済:
  - `CyclotomicPrimeTrace.lean` (B4.1 入力) — prime-case
  - `CyclotomicGenericTrace.lean` (本日 B4.3) — 任意 d ≥ 1
  - `PowCompositeTrace.lean` — DirectSum.IsInternal + trace decomposition
* **残る "真の" Lean-未移植定理 (2026-05-21 深夜版)**:
  Schur–Zassenhaus (Mathlib)、Sylow (完備)、Cyclotomic (整備済)、
  cyclotomic.irreducible_rat (Mathlib)、trace_eq_sum_trace_restrict
  (Mathlib) ── 必要な intermediate building block はほぼ全て揃った。
  Moore57 に必要な大物外部定理は **GAP SmallGroup uniqueness と paper
  §4 Prop 2 (rational class character system) のみ**、いずれも proper
  Prop def として encode 済で下流の paper-faithful proof を妨げない。
* **Cor 3 (`|Aut(Γ)| ≤ 375`) のすべての構成要素が Lean に揃った**:
  Tier C (Lem 17/18) + Tier D (rank-3 framework) + Tier E (Sylow 経路) +
  Tier B (character bridge + composite-order trace integrality)。
  paper-faithful な統合は別タスクだが、building block 不足ではない。

### 8.2 Path C (Cor 3 climbing) concrete dependency tree (2026-05-21 深夜)

`plans/moore57_papers_implementation_plan.md` §4 で Path C を **planning
skeleton から具体的 dependency tree に展開済**。 主要結論:

* **Cor 3 dispatch hypothesis** は arithmetic core で全て proven
  (`cor3_bound_from_props_and_oddpart`); 残る True-stub は
  `hΓ : IsMoore57 Γ` から dispatch を抽出する bridge のみ。
* **Minimum True-stub set (per Prop)**:
  - Prop 6 (3, 5): 5 件 (うち 2 件は Tier A 依存 — Cor 2 / Lem 22)
  - Prop 7 (3, q∈{7,13,19}): 3 件 (Tier A 非依存; Lem 19 主要)
  - Prop 8 (5, q∈{7,11}): 4 件 (Tier A 非依存; Lem 26 主要)
  - Thm 7 (even): 4 件 (うち 1 件は MP 2001 paper-faithful 化)
* **Tier A 完全 bypass は不可** (§4.3.B): Thm 4 unconditional には
  `cor2_smallGroup_81_9` (A1.2 15 群)、 Thm 5 unconditional には
  `lem22_smallGroup_625_12` (A3 10 群) のいずれかが本質的に必要。
  Path B Lem 21 (prime-case のみ) でも composite-order σ ∈ SG(81,9) には
  到達しない。
* **3 段階 achievable subgoal**:
  - Tier 1: 完全 conditional `aut_card_le_375_paper` — **proven**
  - Tier 2: `Conclusion` Prop encoding 経由 partial unconditional — **1-2 commits**
  - Tier 3: prime-case 限定 (`orderOf σ ≤ 19` for prime-order σ) — Path B 経由
  - Tier 4: 完全 unconditional — Tier A 必須

詳細は `plans/moore57_papers_implementation_plan.md` §4.1-4.5 参照。

---

## 9. 関連メモリ

* [[project-papers-scaffold]] — Papers/ scaffold 全体状態
* [[reference-moore57-papers]] — paper 出典 + Lean 進捗
* [[project-moore57-state]] — implementation 側 D19 + Order22 + HS の済み状態

## 10. 直近の主要 commit (2026-05-21 / 同日 3 並行セッション)

### 本日深夜の進捗

#### Tier B B4.3 (composite-order trace integrality)

* (HEAD) `9524108` proofs+blogs: Tier B B4.3 Step 4 full — composite-order
  trace integrality (`trace_int_of_pow_eq_one`) + `CyclotomicGenericTrace.lean`
* `fd3f3e4` proofs+blogs: Tier B B4.3 Step 4 partial — trace
  decomposition over direct sum (`trace_eq_sum_trace_restrict_...`)
* `1ed9b2f` proofs+blogs: Tier B B4.3 Step 3 full — iSupIndep +
  DirectSum.IsInternal
* `c18ed47` proofs+blogs: Tier B B4.3 Step 3 partial — pairwise-with-rest
  disjoint helper
* `2a94bc2` proofs+blogs: Tier B B4.3 Step 2 done — kernel sum decomp
  over Phi_d kernels

#### Tier D (Higman 1964 + Aschbacher 1.4)

* `7be03dc` proofs: Tier D D3.5/D3.6/D4.0/D4.1 done — roadmap status update
* `4f202dc` papers: Tier D D4.0/D4.1 — Aschbacher 1.4 dichotomy +
  combined Cor classification
* `5239c4d` papers: Tier D D3.5/D3.6 — Lem 7 multiplicity formula +
  Thm 1 full bridge
* `f02572c` proofs: Tier D D3.0/D3.2/D3.3/D3.4 done — roadmap status update
* `f39e594` papers: Tier D D3.4 Lem 5 — rank-3 perm group ℤ form +
  orbital intersection numbers
* (earlier today) D3.0 main + D3.1 + D3.2 + D3.3 (Lem 1-4 backbone)

#### Tier C (Petersen / Hoffman-Singleton / Lem 17-18 + Prop 3)

* `db218a9` proofs+blogs: Tier C C3.6 done — roadmap + blog notes
* `dd3e94d` papers: Tier C C3.6 done — Prop 3 (Fix=HS ⟹ |X|≤5)
  proper-signature 化
* `cc0a554` proofs+blogs: Tier C C3.4 done — roadmap + blog notes
* `0a17bcf` papers: Tier C C3.4 done — semi-regular orbit argument
  (`SemiRegularOrbit.lean` + `SemiRegularComplement.lean` + FixedData
  wrappers + Lem 17/18 unconditional wrappers)
* (prev HEAD) papers+proofs: Tier D D3.2 partial — subdegree G-invariance + reverse-neighborhood ↔ swap bridge (Lem 3 backbone)
* `a75e397` proofs+blogs: Tier D D3.1 done — Lem 2 orbital constancy backbone
* `86f5be0` papers: Tier D D3.1 — orbital intersection count constancy (Lem 2 backbone)
* `40bb98a` papers: Tier B finish — True-stub `Conclusion` defs + Lem 11 conditional
* (prev HEAD) papers+proofs: Tier A A2.2-minimal — heisSubgroup + z5DirectFactor for SG625_12
* `67c6e69` papers+proofs: D2.1/D2.2 paired orbital + D3.0 partial Lem 1 statements
* `1f1e656` proofs+blogs: A1.1 orientation (negative) + E5.1 + D2.0
* `5608b87` papers: E5.1 Sylow-SchurZassenhaus + D2.0 orbital structure
* `c39c87c` proofs+blogs: Tier B B3.1+ done — chi0/chi1/chi2 spectral subreps
* `3557431` papers: Tier B B3.1+ chi0 + chi2 spectral subreps + character identifications
* `713613d` proofs+blogs: Tier B B3.1+ chi1 partial done — spectral subrep + character
* `10632df` papers: Tier B B3.1+ chi1 — spectral subrepresentation + character identification
* `dfd3e1f` proofs+blogs: Tier B B4.2 done — Lem 12 p=7 + Lem 13 p=3 starred unconditional
* `84ce471` papers: Tier B B4.2 — Lem 12 p=7 a₀=58 starred + Lem 13 p=3 (?, 1) unconditional via B4.1
* `be8c0d7` proofs+blogs: Tier B B4.1 cyclotomic integer trace + Lem 12 p=3 unconditional
* `4b9a6b9` papers: Tier B - cyclotomic integer trace for order p + Lem 12 p=3 unstubbed
* `0b0aaf5` proofs+blogs: Tier B Section 3 unstub + Lem 11 a2 char chain
* `f167ac0` papers: Tier B Section 3 unstub - Lem 6 (3) / Lem 9 (1) / Lem 10
* `79cf986` papers: Tier B Cor 1 unstub + Lem 11 a2 conj via characters
* `fa95482` proofs+blogs: Tier B continuation - Lem 11 chain + Lem 12/13 wrappers
* `9ab7eca` papers: Tier B Lem 13 - FixedData-parameterised row bridges
* `f17f4df` papers: Tier B Lem 11 char chain + Lem 12 paper-faithful wrappers
* `4a73602` proofs+blogs: Tier B B5 partial - Lem 13/15/17/18/19 conditional rows
* `51a70a5` papers: Tier B Lem 17/18/19 - dispatch numeric bounds
* `b35143b` papers: Tier B Lem 13/15 - fix-set monotonicity + conditional rows
* `734e884` papers: Tier B - spectral characters χ₀/χ₁/χ₂ + conj invariance + a₁/a₂ inverse formulas

### 主要新規 infrastructure (今期)

* `Foundations/LinearAlgebra/PowPrimeTrace.lean` — cyclicSum + cyclicProjection +
  `exists_int_trace_of_pow_prime_eq_one` (任意 ℚ-線形 `f^p = 1` で
  `trace(f) ∈ ℤ`, p prime)
* `Moore57Graph/Aut/TraceIntegrality.lean` — `aut_pow_prime_E7_trace_int`
  (`σ^p = 1` ⟹ `tr(E₇·P_σ) ∈ ℤ`, 既存 involution 版 p=2 の真の一般化)
* `Moore57Graph/Characters.lean` — `chi0/chi1/chi2 : Equiv.Perm V → ℚ`
  + conjugation invariance (`chi_j_conj`)
* `Foundations/Representation/PermutationRepresentationCharacter.lean` —
  `character_permutationRepresentation_eq_fixedVertexCount` bridge
* `Foundations/GroupAction/FixedPoints.lean` — `fixedVertexSet_subset_pow`,
  `fixedVertexCount_le_pow` (monotonicity under powers)
* `Foundations/GroupAction/SemiRegularOrbit.lean` — **(2026-05-21 夜
  C3.4)** 一般 `orderOf_dvd_card_of_semiRegular` + `cyclicOrbitFinset` 補題。
* `Moore57Graph/Aut/SemiRegularComplement.lean` — **(2026-05-21 夜 C3.4)**
  graph-aut bridge: `autMovedNeighborFinset` + σ-invariance +
  `orderOf_dvd_card_movedNeighbour_of_semiRegular`。
* `Foundations/GroupTheory/RankAndOrbital.lean` — **(2026-05-21 D2-D3)**
  `orbital G Ω`, `swapOrbital`, `IsSelfPaired`, `permRank`, `IsRank3`,
  `orbitalNeighborhood/orbitalReverseNeighborhood`,
  `orbitalIntersectionCount` + constancy。 Higman 1964 §1 backbone。
* `Foundations/LinearAlgebra/PowCompositeTrace.lean` — **(2026-05-21 深夜
  B4.3 Step 2-4)** Steps 1-4 (annihilation + kernel sum decomp +
  iSupIndep + DirectSum.IsInternal + trace decomposition + per-block
  integrality + **`trace_int_of_pow_eq_one`** 最終定理)。
* `Foundations/GroupTheory/CyclotomicGenericTrace.lean` — **(2026-05-21
  深夜 B4.3 Step 4 full)** prime-case の任意 d ≥ 1 への一般化:
  `nextCoeff_cyclotomic_rat_isInt`, `trace_quotient_cyclotomic_X_isInt`,
  **`trace_int_of_cyclotomic_aeval_eq_zero`** (B4.1 generic 版)。
* `Papers/Higman1964/Lemma01_PairedOrbits.lean` ~ `Lemma07_*.lean` —
  **(2026-05-21 夜 D3.0-D3.6)** rank-3 perm group framework
  (paper-faithful Lems 1-7 抽象版)。
* `Papers/Aschbacher1971/Lemma1_4_InvolutionFix.lean`,
  `Papers/Aschbacher1971/MainTheorem.lean` — **(2026-05-21 夜 D4.0/D4.1)**
  involution dichotomy + combined classification Cor。
* `Papers/MacajSiran2010/Section08_Theorem5Proof/Proposition3_HSFixBound.lean` —
  **(2026-05-21 夜 C3.6)** `Fix(X) = HS ⟹ |X| ≤ 5` の arithmetic 段 +
  conditional bridge + abstract Conclusion def。

### Tier B finalization (B-final, 2026-05-21 晩 / commit `40bb98a`) — abstract `Conclusion` defs

各 paper claim を Lean Prop として明示。 True-stub を companion abstract
conclusion + (Lemma 11 は) proper conditional bridge で支える形に整備:
* `Section04_Characters/Theorem3_RationalClasses.lean` — `Theorem3RationalClasses`
  (Curtis–Reiner: `ρ.character (σ^k) = ρ.character σ`, k coprime to orderOf σ)
* `Section04_Characters/Proposition2_CharacterSystem.lean` — `Proposition2CharacterSystem`
  (rational character system の non-negative integer 解 statement)
* `Section04_Characters/Lemma11_AiConstantOnClasses.lean` —
  `lem11_ai_constant_on_rational_classes` を True-stub → proper conditional
  bridge に格上げ (χⱼ 定数性仮説 → aᵢ 定数性結論、Theorem 1 inverse 経由)
* `Section05_Tables/Lemma12_PrimeOrder.lean` — `Lemma12PrimeTableConclusion`
* `Section05_Tables/Lemma13_PrimeSquared.lean` — `Lemma13PrimeSquaredConclusion`
* `Section05_Tables/Lemma14_SemiRegularCongruence.lean` — `Lemma14SemiRegularConclusion`
* `Section05_Tables/Lemma15_OrderPQ.lean` — `Lemma15PQTableConclusion`,
  `Lemma15NoOrder65Conclusion`, `Lemma15NoPQ14A049Conclusion`

これらは external 依存 (Theorem 3 全形 + semi-regular orbit decomposition +
一般 fix-shape classification) が Lean に来るまで、下流 lemmas に
hypothesis として渡されて unconditional な進捗を可能にする。 Tier B 内部
進捗はこの finalization をもって完了状態。
