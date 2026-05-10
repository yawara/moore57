# Codex への返信案：Moore57 / D19 / involution・trace・orbit contribution の Lean-aware 分解

この返信は、`yawara/moore57` の現行ファイル名・record 名に合わせて、既読論文の該当補題を Lean 化するための分解案です。論文本文のページ単位確認ではなく、ユーザーが指定した Macaj--Širáň 2010 / Makhnev--Paduchikh 2001 の主張を、現在の Lean パイプラインに接続できる形へ再構成しています。

結論を先に書くと、いま重い入力はほぼ次の二つに集約できます。

1. reflection/involution の固定点数側：`fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56`、またはそれを強制するための lower bound / candidate exclusion。
2. 表現論側：`h.e7ProjectionRepresentation` の D19 character class boundary、そこから `D19LinearCharacterInput h` や `TraceRepresentationData h.a1` を構成すること。

固定集合が star になる部分は、`fixedVertexCount = 56` があれば現 Lean ではほぼ閉じています。orbit/contribution 側も、`BranchOrbitABCFromCenter` と `AFiberCardinality38Boundary` を使うと `D19GeometricInputs` へかなり直接に流せます。

---

## 1. Macaj--Širáň 2010 の involution fixed count `56` を Lean 化する粒度

### 1.1 まず証明対象を分ける

一般の Moore57 involution `σ : Equiv.Perm V` について、以下を分離すると Lean に載せやすいです。

```lean
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable (hΓ : IsMoore57 Γ)
variable (σ : Equiv.Perm V)

-- graph automorphism
variable (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
-- involution
variable (hinv : Function.Involutive σ)
```

置く記号は次です。

```lean
a0 := fixedVertexCount σ
a1 := adjacentMovedCount Γ σ
F  := fixedVertexSet σ
e  := edge count of the graph induced on F
```

Macaj--Širáň Lemma 2 相当を一つの巨大補題にせず、次の四層に分けるのがよいです。

1. Moore57 / SRG 事実から固定誘導グラフが strong `(0,1)` を継承する。
2. Higman trace formula から合同条件を得る。
3. involution から偶奇条件と edge-count formula を得る。
4. bound / candidate exclusion を使って `a0 = 56` に落とす。

---

### 1.2 SRG / fixed-induced graph 側

Moore57 は `(v,k,λ,μ) = (3250,57,0,1)` の SRG として使います。Lean 側では `IsMoore57 Γ` がこの役割を持っています。

固定誘導グラフについて必要なのは次の事実です。

```lean
-- D19 専用には既にある：
D19ActsOnMoore57.fixedInducedGraph_commonNeighbors_card_of_adj
D19ActsOnMoore57.fixedInducedGraph_commonNeighbors_card_of_not_adj
D19ActsOnMoore57.fixedInducedGraph_isStrongZeroOne
```

数学的内容は単純です。

* 固定点 `x,y` が隣接なら、Moore57 の `λ=0` により共通近傍はない。
* 固定点 `x,y` が非隣接なら、Moore57 の `μ=1` により一意の共通近傍 `z` がある。
* `σ` は graph automorphism で `x,y` を固定するので、`σ z` も `x,y` の共通近傍。
* 一意性から `σ z = z`。従って `z` は固定誘導グラフに入る。

この結果は `IsStrongZeroOne` として保存するのが良いです。

```lean
structure IsStrongZeroOne (G : SimpleGraph V) : Prop where
  of_adj : ... commonNeighbors card = 0
  of_not_adj : ... commonNeighbors card = 1
```

次に regular branch の排除です。

```lean
D19ActsOnMoore57.fixedInducedGraph_isSRGWith_of_regular
not_isSRGWith_56_k_0_1
not_isSRGWith_n_k_0_1_of_card_between_52_56
D19ActsOnMoore57.fixedInducedGraph_not_regular_of_fixedVertexCount_eq_56
D19ActsOnMoore57.fixedInducedGraph_not_regular_of_fixedVertexCount_between_52_56
```

特に `fixedVertexCount = 56` が既にあるなら、regular branch は `k^2 = 55` 型の SRG parameter equation に反して排除できます。したがって non-regular strong `(0,1)` branch に入り、star が出ます。

```lean
IsStrongZeroOne.exists_isStarWithCenter_of_not_regular
```

---

### 1.3 Higman trace formula と合同条件

Higman trace は、現 Lean では次の形に切り出されています。

```lean
IsMoore57.higman_trace_int_intModEq
IsMoore57.higman_trace_int_natModEq
D19ActsOnMoore57.D19LinearCharacterInput.reflection_higman_natModEq
```

実際に使う式は次です。

```text
trace_E7(σ) = (8 * a0 + a1 - 65) / 15
```

従って、`trace_E7(σ)` が整数 `z` なら、

```text
8 * a0 + a1 - 65 = 15 * z
```

なので、

```text
a1 ≡ 7 * a0 + 5  (mod 15)
```

が出ます。Lean では次の shape がちょうど良いです。

```lean
theorem involution_higman_congruence
    (htrace : Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ)) :
    adjacentMovedCount Γ σ ≡ 7 * fixedVertexCount σ + 5 [MOD 15]
```

D19 reflection では `D19LinearCharacterInput h` があれば trace は `α - β` なので整数性込みで使えます。

```lean
hin.reflection_higman_natModEq k
```

raw involution で進めるなら、必要な trace integrality は独立補題にしてください。

```lean
-- 目標 shape
∃ z : ℤ,
  Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ)
```

既存方針としては、E7 projection range 上の制限写像が involution であることを示し、有限次元 ℚ-線形 involution の trace は整数、という線形代数補題で処理するのが自然です。`gaps.md` にはこの方向の既存名として次が出ています。

```lean
Moore57.LinearMap.exists_int_trace_of_involutive
D19ActsOnMoore57.exists_int_E7Matrix_mul_permMatrix_reflection_trace
```

---

### 1.4 involution の偶奇条件

involution では非固定点は 2-cycle に分かれるので、

```text
Fintype.card V - fixedVertexCount σ
```

は偶数です。Moore57 では `Fintype.card V = 3250` も偶数なので、`a0` も偶数になります。

既存 Lean 名は次です。

```lean
two_dvd_card_sub_fixedVertexCount_of_involutive
two_dvd_adjacentMovedCount_of_involutive
D19ActsOnMoore57.two_dvd_card_sub_reflection_fixedVertexCount
D19ActsOnMoore57.two_dvd_reflection_adjacentMovedCount
```

`a1` 側の偶奇は補助的です。`a0 = 56` を出す算術では、主に `a0` 偶数が使われます。

---

### 1.5 fixed-induced edge count formula

involution の固定誘導グラフの edge 数を `e` とします。現 Lean の整理では、次の raw formula が中核です。

```text
a1 = 3250 - 58 * a0 + 2 * e
```

固定誘導グラフが star なら `e = a0 - 1` なので、

```text
a1 = 3250 - 58 * a0 + 2 * (a0 - 1)
   = 3248 - 56 * a0
```

に特殊化します。

関連する既存名は次です。

```lean
adjacentMovedCount_eq_involution_fixed_edge_formula
fixed_neighbor_sum_eq_twice_fixed_induced_edges
fixed_to_moved_edge_count_eq
IsStarWithCenter.card_edgeFinset_eq_card_sub_one
D19ActsOnMoore57.fixedInducedGraph_card_edgeFinset_eq_fixedVertexCount_sub_one_of_isStarWithCenter
D19ActsOnMoore57.reflection_starEdgeCountFormula_of_fixedInduced_isStarWithCenter
```

この formula は Higman 合同条件と組み合わせて使います。

```lean
InvolutionHigmanCountArithmetic.starEdgeCountFormula_higman_a0_intModEq_five
```

数学的には、star formula を Higman congruence に代入すると

```text
a0 ≡ 1  (mod 5)
```

が出ます。

---

### 1.6 `a0 = 56` への算術 reduction

現 Lean には、算術部分だけを切り出した補題があります。

```lean
InvolutionHigmanCountArithmetic.starEdgeCountFormula_a0_eq_56_of_bounds
IsMoore57.starEdgeCountFormula_fixedVertexCount_eq_56_of_bounds
D19ActsOnMoore57.D19LinearCharacterInput.reflection_starEdgeCountFormula_fixedVertexCount_eq_56_of_bounds
```

使う仮定は次です。

```text
star edge formula
a1 ≡ 7*a0 + 5 (mod 15)
a0 is even
52 ≤ a0 ≤ 56
```

これで `a0 = 56` が出ます。

したがって、Macaj--Širáň の「固定点数が 56」部分を Lean 化するなら、最終的な大補題は次のような構成にするのが良いです。

```lean
theorem involution_fixedVertexCount_eq_56_of_MS_bounds
    (hΓ : IsMoore57 Γ)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ)
    (htraceInt : ∃ z : ℤ,
      Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ))
    (hbounds : 52 ≤ fixedVertexCount σ ∧ fixedVertexCount σ ≤ 56)
    (hstar : fixed-induced graph of σ is a star) :
    fixedVertexCount σ = 56
```

ただし、現 repo の D19 reflection 用ルートではさらに整理済みです。`fixedVertexCount = 56` そのものを一気に証明するより、現在の target としては次のどちらかが効きます。

```lean
D19ActsOnMoore57.ReflectionFixedCountBounds
-- または、より弱いが十分な：
D19ActsOnMoore57.ReflectionFixedCountLower47
```

`ReflectionFixedCountLower47` は、現行の候補削減に合わせた実用目標です。すでに Lean は trace-compatible candidates を

```text
6, 10, 16, 26, 36, 46, 56
```

まで落としているので、`fixedVertexCount ≥ 47` で `56` に強制できます。

---

## 2. Makhnev--Paduchikh 2001 の fixed subgraph = star に本当に必要な仮定

結論：D19 reflection 文脈では、`fixedVertexCount = 56` 以外に論文由来の追加仮定はほぼ不要です。

必要なのは次だけです。

1. `IsMoore57 Γ`、つまり Moore57 の `(3250,57,0,1)` 性質。
2. 対象写像が graph automorphism であること。
3. `fixedVertexCount σ = 56`。
4. `InvolutionFixedSetStar56` record に詰める場合だけ、`Function.Involutive σ`。

D19 reflection では 2 と 4 は自動です。

```lean
D19ActsOnMoore57.reflection_smulEquiv_involutive
D19ActsOnMoore57.reflection_smulEquiv_automorphism
```

固定点数 `56` から star へ行く既存ルートは次です。

```lean
D19ActsOnMoore57.fixedInducedGraph_isStrongZeroOne
D19ActsOnMoore57.fixedInducedGraph_not_regular_of_fixedVertexCount_eq_56
IsStrongZeroOne.exists_isStarWithCenter_of_not_regular
D19ActsOnMoore57.fixedSetStarWithCenter_of_fixedInduced_isStarWithCenter
D19ActsOnMoore57.exists_fixedSetStarWithCenter_of_fixedVertexCount_eq_56
D19ActsOnMoore57.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56
```

最後の補題は、まさに「reflection の固定点数が 56 なら、fixed set は paper-shaped な `56` 頂点 star」という statement です。

```lean
D19ActsOnMoore57.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56
    (k : ZMod 19)
    (hfix : fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k))
```

この後は downstream に合わせて、次が取り出せます。

```lean
InvolutionFixedSetStar56.fixedVertexCount_eq_56
InvolutionFixedSetStar56.nonempty_involutionK155
InvolutionFixedSetStar56.adjacentMovedCount_eq_112
D19ActsOnMoore57.nonempty_involutionK155_of_reflectionFixedSetStar56
D19ActsOnMoore57.adjacentMovedCount_reflection_eq_112_of_reflectionFixedSetStar56
```

したがって Codex への実装指示としては、Makhnev--Paduchikh の star proof を再実装し直すより、次の確認だけで十分です。

```lean
-- 追加 paper 仮定なしでこの route を使う。
exact h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56 k hfix
```

構成的 center data は代替ルートです。

```lean
ReflectionFixedNeighborStarCenterData
ReflectionFixedInducedStarCenterData
ReflectionFixedNeighborStarCounts
ReflectionFixedInducedStarDegrees
ReflectionFixedStarBoundary
```

しかし `fixedVertexCount = 56` が既にある場合、これらを入力にする必要はありません。center は `IsStrongZeroOne.exists_isStarWithCenter_of_not_regular` から得れば足ります。

---

## 3. D19 permutation representation から `TraceRepresentationData h.a1` を作る道筋

ここは手作り表現論を避け、mathlib の `Representation`, `character`, `trace` API に乗せるべきです。現 repo にはかなりの橋が既にあります。

### 3.1 vertex permutation representation

まず頂点作用は mathlib の permutation representation として構成済みです。

```lean
D19ActsOnMoore57.vertexMulAction
D19ActsOnMoore57.vertexPermutationRepresentation
D19ActsOnMoore57.vertexPermutationRepresentation_character_eq_fixedVertexCount
D19ActsOnMoore57.trace_permMatrix_smulEquiv_eq_vertexPermutationRepresentation_character
```

generic 側では次があります。

```lean
PermutationRepresentationCharacter.permutationRepresentation
PermutationRepresentationCharacter.trace_permutationRepresentation
PermutationRepresentationCharacter.character_permutationRepresentation
PermutationRepresentationCharacter.character_permutationRepresentation_eq_ncard_setOf
```

これは `Representation.ofMulAction ℚ G X` の character が fixed point 数であることを示す橋です。

---

### 3.2 E7 projection representation

Higman trace に必要なのは、頂点 permutation representation そのものではなく、E7 projection range 上の representation です。

既存ルートは次です。

```lean
D19ActsOnMoore57.smulPermHom
D19ActsOnMoore57.vertexPermutationMatrixRepresentationOnPi
E7Matrix_toLin'_commute_permMatrix
Representation.onCommutingRange
D19ActsOnMoore57.e7ProjectionRepresentation
```

構成原理はこうです。

1. `V → ℚ` 上で permutation matrix representation を作る。
2. `E7Matrix Γ` が graph automorphism の permutation matrix と可換であることを示す。
3. 可換性から `LinearMap.range (E7Matrix Γ).toLin'` が invariant submodule になる。
4. `Representation.onCommutingRange` で range 上の representation を得る。

---

### 3.3 E7 character = concrete matrix trace

次がすでに必要な橋です。

```lean
D19ActsOnMoore57.e7ProjectionRepresentation_character_eq_matrix_trace
```

statement は以下です。

```lean
(h.e7ProjectionRepresentation).character g =
  Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g))
```

この証明の内部では、projection trace lemma が使われています。

```lean
E7Matrix_toLin'_isIdempotentElem
trace_restrict_E7Range_permMatrix_toLin'_eq_matrix_trace
D19ActsOnMoore57.trace_restrict_E7Range_smulEquiv_toLin'_eq_matrix_trace
```

---

### 3.4 dimension `1729`

E7 range の dimension は mathlib の `Representation.char_one` から出しています。

```lean
D19ActsOnMoore57.finrank_E7Range_eq_1729
D19ActsOnMoore57.finrank_e7ProjectionRepresentation_eq_1729
```

ここはもう手で dimension を数えない方が良いです。

---

### 3.5 D19 character class boundary から `D19LinearCharacterInput h`

有限 D19 character 側は次の record に寄せるのが良いです。

```lean
D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma
```

これは次を持つ class-level 入力です。

```lean
dimension : alpha + beta + 18 * gamma = 1729
rotation_value : ∀ d : ZMod 19, d ≠ 0 →
  ρ.character (DihedralGroup.r d) =
    (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)
reflection_zero :
  ρ.character (DihedralGroup.sr 0) = (alpha : ℚ) - (beta : ℚ)
```

identity value は `Representation.char_one` から導出されるので、別入力にしなくてよいです。

これがあれば、次で `D19LinearCharacterInput h` にできます。

```lean
D19ActsOnMoore57.D19LinearCharacterInput.ofE7ProjectionCharacterClassBoundary
```

入力は次です。

```lean
(alpha beta gamma : ℕ)
(characterClass : D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
(reflection : (alpha : ℤ) - (beta : ℤ) = 33)
(minus8_trivial_nonneg : alpha ≤ 113)
(minus8_sign_nonneg : beta ≤ 58)
```

`minus8_*_nonneg` は E7 complement の multiplicity 非負性です。`minus8ProjectionRepresentation` 側がすでにあるなら、ここは complementary character から出すルートを使えます。

---

### 3.6 `TraceRepresentationData h.a1` への最短補題列

`TraceRepresentationData h.a1` は、現行では split records 経由が一番きれいです。

既存 record は次です。

```lean
RotationFixedData h.rotation
TraceMultiplicityData
TraceCharacterCoreData Γ h.rotation h.a1
TraceCharacterCoreData.toTraceRepresentationData
D19ActsOnMoore57.toTraceCharacterCoreData
D19ActsOnMoore57.toTraceRepresentationData
```

必要な入力は以下です。

```lean
hmult : TraceMultiplicityData
hchar : ∀ d : ZMod 19, d ≠ 0 →
  Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
    (hmult.alpha : ℚ) + (hmult.beta : ℚ) - (hmult.gamma : ℚ)
hfixed : RotationFixedData h.rotation
```

推奨する橋補題の shape は次です。

```lean
noncomputable def D19ActsOnMoore57.traceRepresentationData_of_E7CharacterClassBoundary
    (h : D19ActsOnMoore57 V Γ)
    (hrot : RotationFixedData h.rotation)
    (alpha beta gamma : ℕ)
    (hclass : D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (href : (alpha : ℤ) - (beta : ℤ) = 33)
    (hminus0 : alpha ≤ 113)
    (hminus1 : beta ≤ 58) :
    TraceRepresentationData h.a1 := by
  let hmult : TraceMultiplicityData :=
    TraceMultiplicityData.ofMathlibCharacterClassBoundary
      h.e7ProjectionRepresentation alpha beta gamma
      h.finrank_E7Range_eq_1729
      hclass href hminus0 hminus1
  let hchar : ∀ d : ZMod 19, d ≠ 0 →
      Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
        (hmult.alpha : ℚ) + (hmult.beta : ℚ) - (hmult.gamma : ℚ) := by
    intro d hd
    -- use:
    --   h.e7ProjectionRepresentation_character_eq_matrix_trace (DihedralGroup.r d)
    --   hclass.rotation_value d hd
    -- plus definitional simplification of h.rotation d.
    sorry
  exact h.toTraceRepresentationData hmult hchar hrot
```

`hchar` の証明は基本的に次の `calc` です。

```lean
calc
  Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d))
      = (h.e7ProjectionRepresentation).character (DihedralGroup.r d) := by
        -- symm of e7ProjectionRepresentation_character_eq_matrix_trace
        -- plus h.rotation d = h.smulEquiv (DihedralGroup.r d)
        simpa [D19ActsOnMoore57.rotation] using
          (h.e7ProjectionRepresentation_character_eq_matrix_trace
            (DihedralGroup.r d)).symm
  _ = (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ) :=
        hclass.rotation_value d hd
```

`hmult.alpha = alpha` などは `rfl` / simp で処理できるはずです。

残る本質は、`h.e7ProjectionRepresentation` の `D19CharacterClassBoundary` をどう作るかです。そこだけが有限 D19 表現論の中身であり、trace API そのものは既存の橋を使えば十分です。

---

## 4. orbit / contribution 側の自然言語証明を既存 record 名に対応させる

ここは、最終的には次の record に入れることを意識すると整理しやすいです。

```lean
D19GeometricInputs h
```

fields は次です。

```lean
characterInput : D19ActsOnMoore57.D19CharacterInput h
orbitBase : OrbitBaseSelectionInput h
fixedOrAContribution : ZMod 19 → ℕ
fixed_or_A_contribution : ∀ d, d ≠ 0 → fixedOrAContribution d = 38
adjacentMovedDecomposition :
  D19AdjacentMovedDecomposition h orbitBase.base fixedOrAContribution
```

---

### 4.1 「56 個の moved rotation orbit の選択」

自然言語では、回転の唯一固定点を `u` とし、`N(u)` の 3 つの 19-orbit を `A,B,C` とします。reflection の添字を調整して、

```text
t(a_i) = a_{-i},
t(b_i) = c_{-i},
t(c_i) = b_{-i}
```

とします。

`B` 側の代表枝を `b0` とし、その branch fiber `L_{b0}` は 56 点です。この 56 点を `Fin 56` で列挙し、それぞれの rotation orbit を選ぶのが `orbitBase` です。

Lean record は次です。

```lean
OrbitBaseSelectionInput h
```

fields は次です。

```lean
base : Fin 56 → V
base_moved : ∀ q, h.rotation 1 (base q) ≠ base q
pairwise_disjoint : ∀ q r, q ≠ r →
  Disjoint (h.rotationOrbitFinset (base q))
           (h.rotationOrbitFinset (base r))
```

`BranchOrbitABCFromCenter` から行く場合、canonical input はこれです。

```lean
BranchOrbitABCFromCenter.toOrbitBaseSelectionInputFromBFibers
```

使える事実は次です。

```lean
OrbitBaseSelectionInput.W
OrbitBaseSelectionInput.W_injective
OrbitBaseSelectionInput.rotationOrbitFinset_card_base
OrbitBaseSelectionInput.orbitFamilyUnion
OrbitBaseSelectionInput.orbitFamilyUnion_card  -- 1064
```

数学的内容は：`L_{b0}` の点は rotation で固定されないので各 orbit は長さ 19、異なる `q` の orbit は B-side branch leaf 内で disjoint、というだけです。

---

### 4.2 reflection copy と two-copy partition

reflection が `b0` を `c0` へ送るとき、選んだ B-side 56 orbits の reflection image は C-side 56 orbits になります。

この B/C 二つのコピーを、partition index `Fin 2 × Fin 56` として数えます。generic な record は次です。

```lean
D19ActsOnMoore57.AdjacentMovedPartition h d (Fin 2 × Fin 56)
```

より高水準には、次を使う方が安全です。

```lean
AdjacentMovedReflectionComplementResidualSplit38Witness h input
```

この record は、B-copy / C-copy の disjointness と、residual を二つに割った形を持ちます。

```lean
k : ZMod 19
cross_disjoint : ∀ q r : Fin 56,
  Disjoint
    (h.rotationOrbitFinset (input.base q))
    (h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) (input.base r)))
fixedPart : Finset V
aPart : Finset V
parts_disjoint : Disjoint fixedPart aPart
residual_eq : reflectionCopyResidual h input.base k = fixedPart ∪ aPart
residual_contribution : ∀ d, d ≠ 0 →
  (fixedPart.filter fun y => Γ.Adj y (h.rotation d y)).card +
  (aPart.filter fun y => Γ.Adj y (h.rotation d y)).card = 38
```

`BranchOrbitABCFromCenter` では、mixed B/C disjointness は既に次で処理されています。

```lean
BranchOrbitABCFromCenter.cross_disjoint_toOrbitBaseSelectionInputFromBFibers_of_reflection_smul_b0_eq_c0
```

---

### 4.3 residual split：zero part + A-fibers

B-side と C-side の leaf union を取り除いた complement は、

```text
{u} ∪ N(u)   と   A-side all fibers
```

に分かれます。

Lean 名では、

```lean
centerNeighborPart Γ data.u

data.toAFiberCoordinates.allFibers
```

です。既存補題は次です。

```lean
BranchOrbitABCFromCenter.compl_bSideLeaf_union_cSideLeaf_eq_zeroPart_union_aSideLeaf
BranchOrbitABCFromCenter.reflectionCopyResidual_b0FiberBase_eq_zeroPart_union_aFibers
BranchOrbitABCFromCenter.reflectionCopyResidual_toOrbitBaseSelectionInputFromBFibers_eq_zeroPart_union_aFibers
BranchOrbitABCFromCenter.zeroPart_disjoint_toAFiberCoordinates_allFibers
```

つまり、split witness では

```lean
fixedPart := centerNeighborPart Γ data.u
aPart := data.toAFiberCoordinates.allFibers
```

と入れるのが自然です。

---

### 4.4 residual contribution `38`

residual contribution は二つに分けます。

1. `centerNeighborPart Γ data.u` は非自明 rotation の adjacent-moved count に寄与しない。
2. A-fiber all fibers は常に `38` 寄与する。

既存名は次です。

```lean
D19ActsOnMoore57.centerNeighborPart_filter_adjacent_rotation_card_eq_zero
AFiberCardinality38Boundary
BranchOrbitABCFromCenter.zeroPart_union_allFibers_residual_contribution
```

A-fiber contribution `38` の自然言語証明は、次のように `AFiberCoordinates` 言語へ落とすとよいです。

* `A` 側の branch orbit を `a_i = r^i a0` とし、fiber を `L_{a_i}` とする。
* `L_{a_i}` を共通座標集合 `P`、`|P|=56` で座標化する。
* rotation は `(i,p) ↦ (i+d,p)`。
* `L_i` と `L_{i+d}` の完全 matching を permutation `A_d : P ≃ P` として表す。
* `Γ.Adj (i,p) (i+d,p)` は、座標上 `A_d p = p` 型の固定点条件に変換される。
* reflection midpoint argument で、各 `d ≠ 0` について `A_d` の fixed point がちょうど 2 個であることを示す。
* index `i : ZMod 19` が 19 個あるので、A-fiber 全体の adjacent-moved contribution は `19 * 2 = 38`。

関連しそうな既存ファイル・名前は次です。

```lean
AFiberCoordinates
AFiberRotationEquivariance
AFiberMatchingPerm
AFiberMatchingSupportEquations
AFiberCardinality38Boundary
AFiberUnionFilterCardinality
```

この `38` を record 化したものが `AFiberCardinality38Boundary h data.toAFiberCoordinates (Finset.univ : Finset (ZMod 19))` です。

---

### 4.5 compact witness から decomposition へ

`BranchOrbitABCFromCenter` と `AFiberCardinality38Boundary` があれば、次で split witness を作れます。

```lean
BranchOrbitABCFromCenter.toComplementResidualSplit38WitnessFromBFibersOfReflection
```

その後、以下で downstream 用の adjacent-moved decomposition に変換できます。

```lean
AdjacentMovedReflectionComplementResidualSplit38Witness.toDecomposition
```

結果は

```lean
D19AdjacentMovedDecomposition h input.base fixedOrAContribution38
```

です。

generic partition から直接行く場合は、次の constructor が対応します。

```lean
D19AdjacentMovedDecomposition.of_twoCopyPartition
```

ただし、実装上は compact reflection-copy witness を通す方が楽です。`of_twoCopyPartition` は partition bookkeeping の最終形で、B/C geometry の証明は compact witness 側の補題で吸収できます。

---

### 4.6 `D19GeometricInputs` への組み立て

目標補題の shape は次でよいと思います。

```lean
noncomputable def BranchOrbitABCFromCenter.toD19GeometricInputs
    (data : BranchOrbitABCFromCenter h)
    (characterInput : D19ActsOnMoore57.D19CharacterInput h)
    (boundary :
      AFiberCardinality38Boundary h data.toAFiberCoordinates
        (Finset.univ : Finset (ZMod 19)))
    {k : ZMod 19}
    (href : h.smul (DihedralGroup.sr k) data.b0 = data.c0) :
    D19GeometricInputs h where
  characterInput := characterInput
  orbitBase := data.toOrbitBaseSelectionInputFromBFibers
  fixedOrAContribution := fixedOrAContribution38
  fixed_or_A_contribution := by
    intro d hd
    rfl
  adjacentMovedDecomposition :=
    (data.toComplementResidualSplit38WitnessFromBFibersOfReflection
      boundary href).toDecomposition
```

`fixed_or_A_contribution := rfl` が通らない場合でも、`fixedOrAContribution38` の定義展開だけの補題を一つ作れば十分です。

---

## 5. Codex に渡す実装優先順位

### 最優先 1：fixed-count 側は star proof を増やさない

`fixedVertexCount = 56` から star へは既に閉じています。新規実装対象は star 化ではなく、次のいずれかです。

```lean
D19ActsOnMoore57.ReflectionFixedCountBounds
D19ActsOnMoore57.ReflectionFixedCountLower47
fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56
```

star が必要なら、以下を直接使います。

```lean
h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56 k hfix
```

### 最優先 2：表現論側は `D19CharacterClassBoundary h.e7ProjectionRepresentation` を作る

mathlib bridge はかなり揃っています。次の record を作れれば、`D19LinearCharacterInput h` も `TraceRepresentationData h.a1` もかなり機械的に出せます。

```lean
D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma
```

そこから：

```lean
D19ActsOnMoore57.D19LinearCharacterInput.ofE7ProjectionCharacterClassBoundary
D19ActsOnMoore57.toTraceRepresentationData
```

へ進めます。

### 最優先 3：orbit/contribution は `BranchOrbitABCFromCenter` canonical B-fiber route を使う

手で一般 partition を作るより、次を使います。

```lean
data.toOrbitBaseSelectionInputFromBFibers

data.toComplementResidualSplit38WitnessFromBFibersOfReflection boundary href

(...).toDecomposition
```

これで `D19AdjacentMovedDecomposition` へ落ちます。

---

## 6. 追加で作るとよい小補題リスト

### fixed-count / Higman side

```lean
-- General non-D19 version if useful:
fixedInducedGraph_isStrongZeroOne_of_automorphism
fixedInducedGraph_not_regular_of_fixedVertexCount_eq_56_of_automorphism
exists_fixedSetStarWithCenter_of_fixedVertexCount_eq_56_of_automorphism

-- Trace integrality for involution on E7 range:
exists_int_E7_trace_of_involutive_automorphism

-- One-shot arithmetic wrapper:
involution_fixedVertexCount_eq_56_of_starEdgeFormula_bounds_traceInt
```

### representation side

```lean
D19ActsOnMoore57.traceRepresentationData_of_E7CharacterClassBoundary
D19ActsOnMoore57.rotationFixedData_of_rotation_fixed_one
D19ActsOnMoore57.traceCharacterCoreData_of_E7CharacterClassBoundary
```

### orbit/contribution side

```lean
BranchOrbitABCFromCenter.toD19GeometricInputs
BranchOrbitABCFromCenter.toAdjacentMovedDecompositionFromBFibers
AFiberCardinality38Boundary.of_matchingPerm_fixedPoint_two
```

この分解なら、論文の補題を Lean に移す時に「論文全体を読む」問題ではなく、現在の record/API に足りない補題を局所化できます。
