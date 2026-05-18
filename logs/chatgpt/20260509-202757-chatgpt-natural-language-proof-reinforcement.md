# ChatGPT Prompt: Natural-Language Proof Reinforcement

- Timestamp: 2026-05-09 20:27:57 +0900
- Topic: Moore57 D19 contradiction formalization
- Purpose: Ask ChatGPT to strengthen the natural-language proof so remaining Lean assumptions can be replaced by formal lemmas.

## Prompt

```text
Moore graph of degree 57 and diameter 2 に D19 が自己同型群として作用することは不可能、という証明を Lean で形式化しています。現在、強い仮定を消す作業中ですが、自然言語証明の以下の部分が薄く、形式化で詰まっています。自然言語証明を、Lean で補題化できる粒度まで詳しく補強してください。

目標：
degree = 57, diameter = 2 の Moore graph Γ について、Aut(Γ) が D19 ではないことを示す。最終的には、D19 作用から導くべき具体データを仮定として置かず、mathlib と Moore graph の基本性質だけから矛盾を出したい。

特に補強してほしい箇所：

1. D19 作用から具体軌道データを構成する部分
- rotation r, reflection s を取り、r の位数 19、srs = r⁻¹ を使って、頂点集合上の軌道・固定点集合・反射コピーをどう定義するか。
- base vertex の選び方、rotation orbit、reflection orbit、orbit family の disjointness をどのように証明するか。
- 「D19ConcreteHypotheses」のような具体データを仮定するのではなく、D19 作用から各フィールドを導出する自然言語証明がほしい。

2. residual split の証明
現在 Lean 側では、次の形の residual split が仮定として残りがちです：
- 非固定 residual 頂点が selected A-fiber union に入ること
- selected A-fiber union が residual に含まれること
- それにより residual = fixed part ∪ A-fiber union と分解できること

ここを、D19 作用と Moore graph の diameter 2 / regularity 57 / girth 的性質から証明したいです。

特に次の形を自然言語で詳しく証明してください：
- y が reflection-copy residual に属し、かつ r に固定されないなら、ある selected index i が存在して y ∈ branchFiber(u, a_i) となる。
- 逆に、selected branchFiber に属する任意の頂点は reflection-copy residual に属する。
- selected branchFiber の頂点は rotation r に固定されない。
- これらの包含から moving residual = A-fiber union を得る。

「明らか」「対称性より」ではなく、どの隣接関係、どの軌道関係、どの Moore graph の一意性を使うかを書いてください。

3. A-fiber cardinality 38 boundary の証明
現在の最大の未解消点は、A-fiber 側の cardinality = 38 に相当する境界条件です。これを仮定せずに証明したいです。

補強してほしい内容：
- A-fiber contribution がなぜ 38 になるのか。
- fixed vertices inside A-fibers を matching permutation の support complement として数える理由。
- 各 selected fiber / branch / index がどのように寄与するか。
- fixed-d column sum の下限、つまり概念的には
  ∑_{i in selected indices} support_complement(matchingRotationPerm d i).card ≥ 38
  のような評価を、どこから導くのか。
- 既に形式化済みの “固定された (i,p) に対して d が高々 2 個” という横方向の評価ではなく、最終証明に必要なのは “固定された d に対する selected indices 全体の縦方向の評価” です。この違いを意識して証明を書いてください。

4. matching permutation と A-fiber counting の対応
以下を自然言語で明確にしてください：
- matchingRotationPerm が何を置換しているのか。
- support complement の元が、どの固定点または A-fiber 内のどの頂点に対応するのか。
- その対応が単射・全射になる理由。
- support complement の総和が A-fiber cardinality / contribution と一致する理由。
- rotation equivariance をどこで使うか。

5. character / trace argument の独立した導出
もし character theory や trace formula を使って 38 を出すなら、以下を省略せずに書いてください：
- D19 の既約指標または必要な character data。
- rotation と reflection の fixed-point count が trace とどう対応するか。
- Moore graph の隣接行列スペクトル、または strongly regular graph の固有値情報を使うなら、その式。
- 「fixed_or_A_contribution = 38」のような結論を途中で仮定しないこと。
- 38 がどの等式・不等式から出るのかを、計算式として追える形にすること。

6. Moore graph の組合せ補題
形式化で使えるように、以下の補題を自然言語で明確化してください：
- diameter 2 から、非隣接頂点には共通近傍が少なくとも 1 個あること。
- Moore graph / degree 57 / diameter 2 の性質から、特定の common neighbor や internal difference set の大きさが高々 2 になる理由。
- 4-cycle や短い cycle が生じる場合の矛盾をどう使うか。
- どの集合が互いに disjoint で、どの cardinality sum が disjoint union として正当化されるか。

出力してほしいもの：
- 形式化しやすい補題リスト。
- 各補題の自然言語証明。
- 依存関係の順序。
- 特に residual split と A-fiber cardinality 38 を、仮定ではなく定理として証明する道筋。
- 既存の強い仮定をどの補題で置き換えられるか。

注意：
- 「対称性より」「明らか」「標準的」だけで済ませず、Lean で補題化できる程度に量化・集合包含・cardinality 等式を明示してください。
- mathlib にありそうな有限群作用、Finset cardinality、Equiv/Perm の support、graph の adjacency preservation で表現できる形を意識してください。
```
