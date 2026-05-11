# yawara/moore57 形式化方針レビュー

## 結論

現在の Lean 形式化の方向性は、全体として正しいです。特に、次の分解は妥当です。

1. **表現論・trace 側**で、非自明 rotation の adjacent-moved count を有限候補へ落とす。
2. **B/C 側 orbit** では、各 internal difference set が高々一つの符号対しか持てない、すなわち card ≤ 2 を 4-cycle 禁止から証明する。
3. **A-fiber 側**では、固定点・枝・A-fiber residual の寄与を正確に `38` としてパッケージする。
4. 最後に、各非零差に必要な B/C 側 orbit 数の下界と、全 orbit の容量上界を比較して矛盾させる。

ただし、現在の最終入口 `D19FinalInputs` はまだ

```lean
fixed_or_A_contribution : ∀ d ≠ 0, fixedOrAContribution d = 38
```

を要求しているので、この `38` を raw action から完全に作る部分が、現在も最重要の未完成部分です。

---

## 1. downstream の方向性は正しい

`D19FinalInputs`, `D19GeometricInputs`, `D19ReducedHypotheses`, `D19OrbitContributionData`, `D19ActionOrbitConcreteData` の流れは正しいです。

現在の downstream は次の形になっています。

```lean
D19FinalInputs
  → D19GeometricInputs
  → D19ReducedHypotheses
  → D19OrbitContributionData
  → D19ActionOrbitConcreteData
  → contradiction
```

ここで本質的に使っている式は、非零 `d : ZMod 19` に対する

```lean
h.a1 d = 38 + 38 * #{q : Fin 56 | d ∈ D_q}
```

です。

この形になれば、trace arithmetic から

```lean
8 ≤ #{q : Fin 56 | d ∈ D_q}
```

が出て、`D_q.card ≤ 2` と double counting して矛盾できます。

この部分の設計はよいです。ここは触らず、上流から必要 field を作る方針で進めるのがよいです。

---

## 2. 一番重要な境界は `AFiberCardinality38Boundary`

現在の最終 pipeline は `AFiberCardinality38Boundary` を要求します。

```lean
structure AFiberCardinality38Boundary ... where
  card_eq_thirtyEight :
    ∀ d : ZMod 19, d ≠ 0 →
      fixedAFiberAFiberCard h (coords.fiberUnion indices) d = 38
```

数学的には、これは

$$
\sum_{i\in\mathbb Z/19}
\left|\{p\in P : M_{i,d}(p)=\operatorname{rotCoord}_{i,d}(p)\}\right|=38
$$

を言っています。A-fiber が 19 個あるので、最終的には各 fiber でちょうど 2 個の解を示すことに相当します。

以前の自然言語スケッチでは「A-fiber contribution は 38」と直接言っていましたが、Lean 化ではこれを次の二段階に分けているのが正しいです。

### 2.1 上界

`ReferenceFiberMatchingExceptionSetTwo` が、reference fiber の matching equation solution set が二点 exception set に含まれることを表します。

そこから rotation invariance により、各 fiber で support-complement card ≤ 2 が出ます。

### 2.2 下界

`AllFibersSupportComplementAtLeastTwoBoundary` が、各 fiber の support-complement card ≥ 2 を要求します。

この上界 ≤ 2 と下界 ≥ 2 を合わせて、各 fiber で card = 2、全体で 19・2 = 38 が出ます。

この分割は Lean 化として非常に良いです。以前の不安点だった「E の二点が固定されるかもしれない」という問題も、この route では `S_h ∩ E = ∅` 型の下界・上界整理に吸収されています。

---

## 3. 現在本当に足りないもの

`BranchOrbitABCLeanAwareFinalBoundary` は、残りをかなり明確に切っています。実質的に不足しているものは次の三つです。

### 3.1 `ReferenceRotationMatchingSolutionVertexFixedBoundary`

必要な内容：reference matching solution が A-fixing reflection によって固定されること。

自然言語では、reference solution は midpoint reflection の fixed side に対応しており、固定星の中心・A-fiber 座標と整合すると、A-fixing reflection の固定点になる、という主張です。

Lean では、まず vertex-level の statement を避けずに、次を明示的に証明するのがよいです。

```lean
ReferenceRotationMatchingSolutionVertexFixedBoundary labeling
```

この補題は後続の `ReferenceRotationMatchingSolutionAFixingSupportComplBoundary` や reference matching pipeline に流れます。

### 3.2 `MidpointExceptionAFixingSupportSingletonFixedBoundary`

必要な内容：もし

```lean
S_m ∩ E = {p}
```

なら、その点 `p` は A-fixing reflection によって固定されること。

しかし `p ∈ E` は A-fixing reflection support に属すること、つまり動くことを意味するため、矛盾します。

これは card-one case を排除するための clean な形です。

### 3.3 `NoAllOffsetsEndpointAdj` または同等の all-offset support-subset 排除

card-two case の排除では、`E ⊆ S_m` が起こると support 上の endpoint adjacency が全 offset で成立し、それにより非隣接 endpoint pair が二つの共通近傍を持つ、という矛盾を使っています。

現在の all-offset common-neighbor route は妥当です。ここでは単一 offset ではなく **all-offset** の形にしたのが重要です。単一 offset 版では候補点を二つ選ぶ余地が不足しやすいので、現在の all-offset 化は正しい修正です。

---

## 4. 優先順位

推奨する順番は次です。

### Step A: `AFiberCardinality38Boundary` へ閉じる最短経路を固定する

まず次の chain だけを目標にします。

```lean
LeanAwareFixedStarFinalBoundary
  → FixedStarReferenceMatchingCardinalityPipelineBoundary
  → AFiberCardinality38Boundary
```

ここで必要なのは、`middle`, `referenceSolutionVertexFixed`, `midpointExceptionAFixingSupportCase` の三 field です。

### Step B: card-one/card-two を別々に閉じる

card-one:

```lean
MidpointExceptionAFixingSupportSingletonFixedBoundary
  → no_card_one
```

card-two:

```lean
NoAllOffsetsEndpointAdj
  → NoAllOffsetsSupportSubsetBoundary
  → no_card_two
```

### Step C: residual split は集合等式より寄与等式を優先する

branch vertices は rotation で動いても adjacent-moved に寄与しないため、集合として residual を完全に A-fiber に等しいとするより、まず

```lean
fixed/branch part contribution = 0
A-fiber part contribution = 38
```

を示す方が堅いです。

既に `rotationOneFixedResidualPart_filter_adjacent_rotation_card_eq_zero` 系があるので、現在の split witness 方式で問題ありません。

### Step D: final no-go bridge を一つに絞る

多数の connector が存在するので、最終的には canonical route を一つ選んだ方がよいです。推奨は次です。

```lean
raw action
  → reflectionFixedStarBoundary_of_raw_action
  → fixedCenterLeafDefaultBaseLabeling_of_raw_action
  → LeanAwareFixedStarFinalBoundary
  → no_D19_leanAwareFixedStarFinalBoundary
```

複数の alternative connector は残してよいですが、README または `gaps.md` では canonical route を一つだけ太字で示すと Codex が迷いにくくなります。

---

## 5. 数学的再検討

現時点で、全体方針に数学的な致命的誤りは見当たりません。

特に次は妥当です。

- `D_q.card ≤ 2` は 4-cycle 禁止から正しい。
- selected 56 orbit を B-side rotation orbits とし、reflection copy を C-side として数える形は正しい。
- `2 * sum over Fin 56` によって B/C 両側の寄与を数える形は正しい。
- trace/character 側から `a1` 候補を出し、`38 + 38*N_d` に代入して下界を得る downstream は正しい。
- exact `38` を直接主張するのではなく、support-complement 上界 ≤2 と下界 ≥2 を合わせる現在の route は、Lean 化にも数学にも合っている。

注意点は一つだけです。

`AFiberCardinality38Boundary` を raw action から作るには、単に midpoint reflection criterion を持つだけでは足りません。必ず `S_m ∩ E = ∅` 相当、すなわち card-one と card-two の排除を通す必要があります。現在の `LeanAwareFixedStarFinalBoundary` がまさにそこを field として残しているので、これは設計上正しい切り分けです。

---

## 6. GitHub に貼る短いコメント案

```markdown
方向性は合っています。downstream の `D19FinalInputs → D19GeometricInputs → D19ReducedHypotheses → D19OrbitContributionData → D19ActionOrbitConcreteData` はそのままでよいです。

現在の本当の未完成点は `fixed_or_A_contribution = 38`、より正確には `AFiberCardinality38Boundary` を raw action から作る部分です。これは midpoint reflection だけでは足りず、現在の設計どおり

1. reference matching solutions are fixed by the A-fixing reflection,
2. `card (S_m ∩ E) ≠ 1`,
3. `card (S_m ∩ E) ≠ 2`, equivalently no all-offset support-subset / endpoint-adjacency branch,

を示して `S_m ∩ E = ∅` に落とし、support-complement の upper ≤2 と lower ≥2 を合わせて各 A-fiber contribution = 2、全体 38 を得るのが正しいルートです。

特に all-offset 化は正しい修正です。single-offset noAllEndpointAdj では二つの distinct common neighbors を作る余地が不足しやすいので、`BranchOrbitABCCardTwoAllOffsetsCommonNeighborBoundary` 経由を canonical route にするのがよいです。

次に集中すべき Lean target は、`LeanAwareFixedStarFinalBoundary` の三 field：

- `middle`,
- `referenceSolutionVertexFixed`,
- `midpointExceptionAFixingSupportCase`,

特に後二者です。`D19FinalInputs` 側の downstream は既に十分整理されています。
```
