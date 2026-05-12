# Moore57 local propositions: Codex への回答

## 前提と記法

Moore graph of degree 57, diameter 2, girth 5 を仮定する。  
\(D_{19}\) が作用し、rotation subgroup \(C_{19}\) の固定点 \(u\) があり、\(u\) の近傍が 3 つの 19-orbit \(A,B,C\) に分かれている。A-fiber coordinates \(P\) を取り、A-fixing reflection \(s\) と midpoint reflection \(s_m\) を考える。

以下、A-fiber coordinate 上で次の記法を使う。

- \(\theta :=\) `labeling.aFiberReflectionCoordPerm`  
  A-fixing reflection \(s\) が reference A-fiber \(L_0\) に誘導する involution。
- \(E :=\) `labeling.aFiberReflectionSupport`  
  すなわち \(p \in E \iff \theta p \ne p\)。
- \(M_d :=\) `AFiberCoordinates.matchingEquiv ... 0 (0+d)`  
  \(L_0\) から \(L_d\) への Moore matching。
- \(R_d :=\) `labeling.data.toAFiberRotationEquivariance.coordPerm d 0`。
- \(T_m :=\) `labeling.midpointReflectionCoordPerm m`。
- \(S_m :=\) `labeling.midpointExceptionSet m hm`。
- \(Q_m :=\) `labeling.midpointEquationSet m hm`。

重要な既存恒等式は

\[
T_m(p)=R_{2m}(\theta p).
\]

Lean では次が対応する。

```lean
midpointReflectionCoordPerm_eq_rotationCoordPerm_aFiberReflectionCoordPerm
rotationCoordPerm_eq_midpointReflectionCoordPerm_midpointOf_iff
```

したがって \(d=2m\) のとき、

\[
R_d(p)=T_{d/2}(p)
\quad\Longleftrightarrow\quad
\theta p=p.
\]

この点が Proposition 1 の循環性の中心である。

---

## 1. `ReferenceRotationMatchingSolutionVertexFixedBoundary`

### 結論

現状の仮定、すなわち Moore graph geometry と \(D_{19}\)-action だけからは証明不足。

この命題は本質的に

\[
M_d(p)=R_d(p)
\quad\Longrightarrow\quad
p\notin E
\]

を主張している。これは「reference rotation matching equation の解が A-fixing reflection の moving support に乗らない」という独立の局所 obstruction である。

### なぜ自動ではないか

reference equation は

\[
x_p \sim r^d x_p
\]

という endpoint adjacency である。

一方、midpoint reflection equation は

\[
x_p \sim r^d s x_p
\]

である。

両者の右辺は、\(\theta p=p\) のときだけ一致する。したがって、reference equation から midpoint exception 側へ移すには、すでに \(\theta p=p\) を知っている必要がある。これはまさに証明したい結論である。

また、\(p\in E\) の場合、辺

\[
x_p \sim r^d x_p
\]

を仮定しても、\(s\) を作用させると

\[
s x_p \sim r^{-d} s x_p
\]

が得られるだけで、同じ offset \(d\) の矛盾や 4-cycle は直ちには出ない。\(C_{19}\)-orbit 上の 19-cycle 的な辺配置は、no triangle / no 4-cycle だけでは排除されない。

### 最小追加仮定

Lean 上の最小形は既にある

```lean
ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling
```

である。unbundled に書くと次。

```lean
∀ d : ZMod 19, ∀ hd : d ≠ 0,
  ∀ p : labeling.data.toAFiberCoordinates.P,
    AFiberCoordinates.matchingEquiv h.isMoore
      labeling.data.toAFiberCoordinates 0 (0 + d)
      (index_ne_add_of_ne_zero hd) p =
    labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p →
    p ∉ labeling.aFiberReflectionSupport
```

この仮定があれば、証明は形式的に進む。

### 証明

\(p\) が reference equation の解とする。追加仮定より \(p\notin E\)。一方、

\[
p\in E \iff \theta p\ne p.
\]

よって \(\theta p=p\)。既存補題

```lean
aFiberReflectionCoordPerm_fixed_iff_vertex_fixed
```

により、reference-fiber vertex

\[
x_p := \operatorname{coord}(0,p)
\]

は A-fixing reflection \(s\) で固定される。したがって

```lean
ReferenceRotationMatchingSolutionVertexFixedBoundary
```

が得られる。

Lean では実質的に次の constructor が最小である。

```lean
ReferenceRotationMatchingSolutionVertexFixedBoundary
  .of_referenceMatchingSolutionSet_subset_aFiberReflectionSupport_compl
```

### 注意

`ReferenceMatchingPipelineBoundary` からこの命題を導く経路は、`referenceToMidpoint` が

```lean
ReferenceRotationToMidpointReflectionBoundary.of_aFixingFixed
```

から作られている場合、循環する。非循環に使うには、`ReferenceRotationToMidpointReflectionBoundary` を fixedness とは独立に証明しておく必要がある。

---

## 2. `MidpointExceptionAFixingSupportSingletonFixedBoundary`

### 結論

次の invariance を追加すれば正しい。

```lean
MidpointExceptionAFixingSupportIntersectionInvariantBoundary labeling
```

つまり

\[
p\in S_{d/2}\cap E
\quad\Longrightarrow\quad
\theta p\in S_{d/2}\cap E.
\]

この仮定のもとでは、証明は Cameron Ch.3 Step 2 型の singleton invariance argument そのものである。

### 最小追加仮定

最小は intersection 自体の invariance。

```lean
∀ d : ZMod 19, ∀ hd : d ≠ 0,
  ∀ p,
    p ∈ labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd) →
    labeling.aFiberReflectionCoordPerm p ∈
      labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)
```

これより強いが自然な仮定は次。

```lean
MidpointExceptionSetAFixingInvariantBoundary labeling
```

理由は、\(E\) の \(\theta\)-invariance は既に次で得られるからである。

```lean
aFiberReflectionCoordPerm_mem_support_of_mem
```

さらに midpoint criterion を使うなら、次でも十分。

```lean
MidpointEquationAFixingCoordinateBoundary labeling
MidpointReflectionCriterionBoundary labeling
```

`MidpointEquationAFixingCoordinateBoundary` は、座標で書くと

\[
M_d(p)=R_d(\theta p)
\quad\Longrightarrow\quad
M_d(\theta p)=R_d(p)
\]

である。これはまさに「A-fixing support の 2 点を交換しても midpoint equation が保たれる」という label exchange 型入力である。

### 証明

\(I_d:=S_{d/2}\cap E\) とおく。仮定として

\[
I_d=\{p\}
\]

を持つ。

1. \(p\in I_d\)。
2. invariance より \(\theta p\in I_d\)。
3. \(I_d=\{p\}\) なので \(\theta p=p\)。

したがって \(p\) は A-fixing reflection で固定される。

Lean では形式的部分が既に次として切り出されている。

```lean
MidpointExceptionAFixingSupportIntersectionInvariantBoundary
  .toMidpointExceptionAFixingSupportSingletonFixedBoundary
```

その後、

```lean
MidpointExceptionAFixingSupportSingletonFixedBoundary.no_card_one
```

により、\(p\in E\) であることと \(\theta p=p\) が矛盾し、card-one case が排除される。

### 不足している点

\(D_{19}\)-action だけでは、\(S_{d/2}\) が A-fixing reflection \(\theta\) で不変とは言えない。実際、\(s\) を作用させると offset \(d\) は通常 \(-d\) 側へ移る。同じ \(d\) の midpoint exception set に戻るには、追加の label-exchange 型補題が必要である。

したがって Proposition 2 は「intersection invariance があれば正しい」が、現状の graph geometry + action だけでは仮定不足。

---

## 3. `MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary`

### 結論

これも現状の仮定だけでは証明不足。

`ExceptionAllSupportBoundary` は

\[
E\subseteq S_{d/2}
\]

から endpoint adjacency を引き出す connector であって、endpoint adjacency が不可能であること自体を証明していない。

### endpoint adjacency の意味

\(m=d/2\) とすると、endpoint adjacency は

\[
x_p \sim T_m(x_p)
\]

すなわち

\[
x_p \sim r^d s x_p
\]

である。

\(p\in E\) なら、\(\theta p\ne p\)。support size two のもとでは

\[
E=\{p,\theta p\}.
\]

「全ての support 点が endpoint adjacency を満たす」とは、局所的には

\[
x_p \sim r^d s x_p,
\qquad
s x_p \sim r^d x_p
\]

という 2 本の crossed matching edge が存在する、ということである。

この 2 本だけでは no triangle / no 4-cycle に直ちには反しない。各辺は \(u,a_0,a_d\) と 5-cycle を作るだけで、girth 5 とは両立する。したがって、ここにも追加の obstruction が必要である。

### 最小追加仮定 1: witness form

最小の Lean 入力は次。

```lean
MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary labeling
```

unbundled には次。

```lean
∀ d : ZMod 19, ∀ hd : d ≠ 0,
  ∃ p,
    p ∈ labeling.aFiberReflectionSupport ∧
    ¬ endpointAdj d p
```

この仮定から `NoAllEndpointAdj` は即座に従う。

#### 証明

仮に全ての \(p\in E\) が endpoint adjacency を満たすとする。witness form より、ある \(p\in E\) が存在して endpoint adjacency を満たさない。矛盾。

Lean では次。

```lean
MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary
  .toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
```

### 最小追加仮定 2: pair form

support が 2 点であることを使うなら、より構造的には次が自然。

```lean
MidpointExceptionAFixingSupportPairEndpointNonadjBoundary labeling
```

これは

\[
p\in E
\]

を一つ選んだとき、

\[
\neg\bigl(
  endpointAdj(d,p)
  \wedge
  endpointAdj(d,\theta p)
\bigr)
\]

を仮定するもの。

support-cardinality input

```lean
AFixingReflectionFixedNeighborCardBoundary labeling
```

があれば、全 support endpoint adjacency はこの 2 点の endpoint adjacency と同値なので、`NoAllEndpointAdj` が従う。

### 最小追加仮定 3: common-neighbor obstruction

graph geometry だけで閉じたいなら、実際に必要なのは次の形。

```lean
MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary labeling
```

すなわち、

```lean
all endpoint adjacency on E
  →
∃ x y z w,
  x ≠ y ∧
  ¬ Γ.Adj x y ∧
  z ≠ w ∧
  Γ.Adj x z ∧ Γ.Adj y z ∧
  Γ.Adj x w ∧ Γ.Adj y w
```

これが証明できれば、Moore graph の \(\mu=1\)、同値に no 4-cycle / unique common neighbor により矛盾する。

Lean では形式的矛盾部分は既に次に分離されている。

```lean
IsMoore57.no_two_commonNeighbors_of_not_adj

MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary
  .toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
```

したがって、Proposition 3 を純粋 graph geometry で証明するには、残る本質的作業は

> all endpoint adjacency から、どの非隣接対 \(x,y\) と、どの 2 つの distinct common neighbors \(z,w\) を作るか

を明示することである。この coordinate construction なしに `NoAllEndpointAdj` は出ない。

---

## 推奨する整理

### Proposition 1

現在の仮定だけでは証明しない方がよい。非循環に進めるなら、次のいずれかを明示的な追加入力にする。

```lean
ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling
```

または unbundled に

```lean
reference equation solution → p ∉ aFiberReflectionSupport
```

### Proposition 2

次を追加すれば証明可能。

```lean
MidpointExceptionAFixingSupportIntersectionInvariantBoundary labeling
```

より自然には、次から導く。

```lean
MidpointEquationAFixingCoordinateBoundary labeling
MidpointReflectionCriterionBoundary labeling
```

証明本体は singleton invariance:

\[
I=\{p\},\ p\in I,\ \theta I\subseteq I
\quad\Rightarrow\quad
\theta p=p.
\]

### Proposition 3

次のいずれかを追加する。

最小 witness:

```lean
MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary labeling
```

2 点 support を使う pair form:

```lean
AFixingReflectionFixedNeighborCardBoundary labeling
MidpointExceptionAFixingSupportPairEndpointNonadjBoundary labeling
```

Moore geometry で閉じる common-neighbor form:

```lean
MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary labeling
```

この最後の form が、no triangle / unique common neighbor / no 4-cycle を使う最も自然な境界である。

---

## 依存関係の注意

現在のファイル構成では、

```lean
ReferenceRotationToMidpointReflectionBoundary.of_aFixingFixed
```

が `ReferenceRotationEquationAFixingFixedBoundary` を使っている。したがって、Proposition 1 を証明するために、この経路で作った `ReferenceMatchingPipelineBoundary` を使うと循環する。

非循環の流れにするなら、次のように分けるのが安全。

```text
MidpointEquationAFixingCoordinateBoundary
  + MidpointReflectionCriterionBoundary
    → SingletonFixed / no_card_one

Endpoint witness または two-common-neighbor obstruction
    → NoAllEndpointAdj / no_card_two

no_card_one + no_card_two + support_card_two
    → S_(d/2) ∩ E = ∅

非循環な reference-to-midpoint input
    + S_(d/2) ∩ E = ∅
    → reference solutions lie outside E
    → ReferenceRotationMatchingSolutionVertexFixedBoundary
```

ただし最後の「非循環な reference-to-midpoint input」は、`of_aFixingFixed` から作ってはいけない。そこは Proposition 1 そのものを使っているためである。

---

## Codex への実装上の提案

### すぐ formalize できる部分

以下は既存 connector でほぼ直接使える。

```lean
-- Proposition 2, assuming intersection invariance
MidpointExceptionAFixingSupportIntersectionInvariantBoundary
  .toMidpointExceptionAFixingSupportSingletonFixedBoundary

-- Proposition 3, assuming endpoint witness
MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary
  .toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary

-- Proposition 3, assuming two-common-neighbor construction
MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary
  .toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary

-- Proposition 1, assuming support complement
ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
  .toReferenceRotationMatchingSolutionVertexFixedBoundary
```

### 新しく証明すべき boundary 候補

非循環化のために、次のいずれかを実証するのが実質的な残り。

1. `MidpointEquationAFixingCoordinateBoundary`  
   A-fixing reflection による midpoint equation の label exchange invariance。

2. `MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary`  
   all endpoint adjacency から no 4-cycle / unique common neighbor contradiction を作る coordinate construction。

3. `ReferenceRotationMatchingSolutionAFixingSupportComplBoundary`  
   reference matching solution が A-fixing support に入らないこと。ただし、これを midpoint pipeline から導くと循環しやすいので注意。

### 判断

3 つの命題は、現在の graph geometry + \(D_{19}\)-action だけから一括で自動証明できる形ではない。  
(2) は invariance があれば Cameron Step 2 と同型に証明可能。  
(3) は endpoint obstruction、特に two-common-neighbor construction があれば Moore geometry で閉じられる。  
(1) は support-complement statement を追加するのが最小で、`ReferenceRotationToMidpointReflectionBoundary.of_aFixingFixed` を経由する証明は循環する。
