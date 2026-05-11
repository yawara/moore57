# ChatGPT response: reference sign symmetry correction

Date: 2026-05-11
Thread: https://chatgpt.com/c/6a017839-e340-83ab-8dfb-fb729ae2ec73

## Prompt context

Asked ChatGPT to re-check the previous same-offset A-invariance claim against the Lean-proved d-to-minus-d reflection transport.

## Response

確認結果です。直前回答の theorem 1 は、そのままでは説明不足でした。

正しくは：

lean
p ∈ L.referenceMatchingSolutionSet d hd
→ L.aFiberReflectionCoordPerm p ∈ L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd)

が A-fixing reflection から直接出る theorem です。これは repo で

lean
aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet_neg

として証明されています。

BranchOrbitABCReferenceSolution…

same-offset 版

lean
p ∈ L.referenceMatchingSolutionSet d hd
→ L.aFiberReflectionCoordPerm p ∈ L.referenceMatchingSolutionSet d hd

を使うには、さらに別の補題

lean
p ∈ L.referenceMatchingSolutionSet d hd
↔ p ∈ L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd)

が必要です。これは reflection ではなく、無向辺 + rotation by -d から出る symmetry です。現行検索でその名前の補題は見つかりませんでした。したがって、私の前回回答の「本当に証明できます」は、この neg-symmetry 補題を別途入れる前提なら正しい、というのが正確です。

1. same-offset theorem は正しいか

数学的には正しいです。ただし直接の A-fixing reflection theorem ではありません。

必要な2段階は：

lean
-- step 1: A-fixing reflection
p ∈ Sol d → A p ∈ Sol (-d)

-- step 2: reference solution set の d ↔ -d symmetry
A p ∈ Sol (-d) → A p ∈ Sol d

Lean では既存の step 1 は：

lean
BranchOrbitABCReflectionLabeling
  .aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet_neg

です。

BranchOrbitABCReferenceSolution…

足りない step 2 は、次の補題として追加すべきです。

lean
theorem BranchOrbitABCReflectionLabeling.mem_referenceMatchingSolutionSet_neg
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P) :
    p ∈ L.referenceMatchingSolutionSet d hd →
      p ∈ L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd)

または iff 版：

lean
theorem BranchOrbitABCReflectionLabeling.mem_referenceMatchingSolutionSet_neg_iff
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P) :
    p ∈ L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd) ↔
      p ∈ L.referenceMatchingSolutionSet d hd

証明の自然言語はこうです。

p ∈ Sol d は

x_p ~ r^d x_p

です。これは mem_referenceMatchingSolutionSet_iff_adj_rotationTarget で adjacency に変換されています。

BranchOrbitABCReferenceSolution…

グラフが無向で、rotation が graph automorphism なので：

x_p ~ r^d x_p
⇒ r^{-d} x_p ~ x_p       -- apply rotation -d
⇒ x_p ~ r^{-d} x_p       -- symmetry of adjacency
⇒ p ∈ Sol (-d)

Lean では主に次を使います。

lean
L.mem_referenceMatchingSolutionSet_iff_adj_rotationTarget d hd p
h.smul_adj (DihedralGroup.r (-d)) ...
AFiberRotationEquivariance.coord_coordPerm_apply_val
SimpleGraph.Adj.symm

matchingEquiv と adjacency 変換は AFiberMatchingPerm.lean の

lean
AFiberCoordinates.adj_iff_matchingEquiv_eq

です。

AFiberMatchingPerm

そのうえで same-offset theorem はこう合成できます。

lean
theorem BranchOrbitABCReflectionLabeling.aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P) :
    p ∈ L.referenceMatchingSolutionSet d hd →
      L.aFiberReflectionCoordPerm p ∈ L.referenceMatchingSolutionSet d hd := by
  intro hp
  have hneg :
      L.aFiberReflectionCoordPerm p ∈
        L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd) :=
    L.aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet_neg d hd p hp
  have hback :
      L.aFiberReflectionCoordPerm p ∈
        L.referenceMatchingSolutionSet (-(-d)) (neg_ne_zero.mpr (neg_ne_zero.mpr hd)) :=
    L.mem_referenceMatchingSolutionSet_neg (-d) (neg_ne_zero.mpr hd)
      (L.aFiberReflectionCoordPerm p) hneg
  simpa using hback

したがって、あなたの指摘は正しいです。reflection 単独では same-offset は出ません。Sol d = Sol (-d) の rotation/undirected symmetry を追加して初めて same-offset が出ます。

2. same-offset を入れない場合、SupportNoAllBoundary から support-complement へ落とすには何が必要か

same-offset theorem を追加しないなら、前回提案した

lean
ReferenceMatchingAFixingSupportNoAllBoundary

では足りません。

前回の route は：

p ∈ E ∩ Sol d
⇒ A p ∈ E ∩ Sol d
⇒ E ⊆ Sol d
⇒ noAllSupport に矛盾

でした。しかし実際に既存 theorem から直接出るのは

p ∈ E ∩ Sol d
⇒ A p ∈ E ∩ Sol (-d)

です。したがって、same-offset symmetry なしで閉じるには、boundary を d/-d paired form に修正すべきです。

最小 statement はこれです。

lean
structure BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingNoPairedSolutionBoundary
    (L : BranchOrbitABCReflectionLabeling h) : Prop where
  no_paired_reference_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : L.data.toAFiberCoordinates.P,
        p ∈ L.aFiberReflectionSupport →
          ¬
            (p ∈ L.referenceMatchingSolutionSet d hd ∧
             L.aFiberReflectionCoordPerm p ∈
               L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd))

これなら、既存の negative-offset theorem だけで support-complement に落とせます。

lean
def BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingNoPairedSolutionBoundary
    .toReferenceRotationMovingSolutionExclusionBoundary
    {L : BranchOrbitABCReflectionLabeling h}
    (B : ReferenceMatchingAFixingNoPairedSolutionBoundary L) :
    ReferenceRotationMovingSolutionExclusionBoundary L where
  no_moving_reference_solution := by
    intro d hd p hpSupport hpSol
    have hApSol :
        L.aFiberReflectionCoordPerm p ∈
          L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd) :=
      L.aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet_neg d hd p hpSol
    exact B.no_paired_reference_solution d hd p hpSupport
      ⟨hpSol, hApSol⟩

この route では support cardinality すら不要です。p と A p の paired obstruction だけで pointwise exclusion が出ます。

より equation-oriented に書くなら：

lean
structure BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingNoPairedEquationBoundary
    (L : BranchOrbitABCReflectionLabeling h) : Prop where
  no_paired_equation :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : L.data.toAFiberCoordinates.P,
        p ∈ L.aFiberReflectionSupport →
          ¬
            (AFiberCoordinates.matchingEquiv h.isMoore
                L.data.toAFiberCoordinates 0 (0 + d)
                (index_ne_add_of_ne_zero hd) p =
              L.data.toAFiberRotationEquivariance.coordPerm d 0 p ∧
             AFiberCoordinates.matchingEquiv h.isMoore
                L.data.toAFiberCoordinates 0 (0 + (-d))
                (index_ne_add_of_ne_zero (neg_ne_zero.mpr hd))
                (L.aFiberReflectionCoordPerm p) =
              L.data.toAFiberRotationEquivariance.coordPerm (-d) 0
                (L.aFiberReflectionCoordPerm p))

これは referenceMatchingSolutionSet 版と同値です。

3. ReferenceMatchingAFixingSupportNoAllBoundary はまだ妥当か

結論はこうです。

Sol d = Sol (-d) 補題を入れるなら妥当

mem_referenceMatchingSolutionSet_neg_iff を入れるなら、

lean
ReferenceMatchingAFixingSupportNoAllBoundary

はまだ妥当です。

その場合の route は：

p ∈ E ∩ Sol d
⇒ A p ∈ Sol (-d)       -- existing reflection transport
⇒ A p ∈ Sol d          -- new neg-symmetry

さらに E.card = 2 と p ∈ E から E = {p, A p} を得て、

E ⊆ Sol d

となり、not_all_support_reference_solution d hd に矛盾します。

つまり same-offset support no-all は、neg-symmetry lemma を隠れ依存として持つ statement です。

より自然な primitive target は d/-d paired support exclusion

Cameron Step 2 / label exchange の流れに忠実にするなら、私は修正版として

lean
ReferenceMatchingAFixingNoPairedSolutionBoundary

を first-class target にする方を推奨します。

理由は、A-fixing reflection が実際に送るのは

lean
Sol d → Sol (-d)

だからです。これは repo の既存 theorem と一致します。

BranchOrbitABCReferenceSolution…

したがって、reference-side target は次のように整理するのがよいです。

最小で自然:
  no paired solution:
    p ∈ E → ¬ (p ∈ Sol d ∧ A p ∈ Sol (-d))

そこから:
  existing Sol d → A p ∈ Sol (-d)
  により p ∉ Sol d

結果:
  ReferenceRotationMovingSolutionExclusionBoundary
  → ReferenceRotationMatchingSolutionAFixingSupportComplBoundary

一方、

lean
ReferenceMatchingAFixingSupportNoAllBoundary

は

E ⊆ Sol d

を禁止する shape なので、reflection の自然な出力 Sol (-d) と一段ずれています。使えますが、Sol d = Sol (-d) を先に入れる必要があります。

推奨する修正後の実装順
theorem 1: Sol d と Sol (-d) の symmetry
lean
theorem BranchOrbitABCReflectionLabeling.mem_referenceMatchingSolutionSet_neg
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P) :
    p ∈ L.referenceMatchingSolutionSet d hd →
      p ∈ L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd)

可能なら iff 版も：

lean
theorem BranchOrbitABCReflectionLabeling.mem_referenceMatchingSolutionSet_neg_iff
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P) :
    p ∈ L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd) ↔
      p ∈ L.referenceMatchingSolutionSet d hd
theorem 2: same-offset A-invariance
lean
theorem BranchOrbitABCReflectionLabeling.aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P) :
    p ∈ L.referenceMatchingSolutionSet d hd →
      L.aFiberReflectionCoordPerm p ∈ L.referenceMatchingSolutionSet d hd

これは

lean
aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet_neg

と theorem 1 の合成です。

theorem 3: paired-exclusion boundary から moving exclusion
lean
structure BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingNoPairedSolutionBoundary
    (L : BranchOrbitABCReflectionLabeling h) : Prop where
  no_paired_reference_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : L.data.toAFiberCoordinates.P,
        p ∈ L.aFiberReflectionSupport →
          ¬
            (p ∈ L.referenceMatchingSolutionSet d hd ∧
             L.aFiberReflectionCoordPerm p ∈
               L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd))
lean
def BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingNoPairedSolutionBoundary
    .toReferenceRotationMovingSolutionExclusionBoundary
    {L : BranchOrbitABCReflectionLabeling h}
    (B : ReferenceMatchingAFixingNoPairedSolutionBoundary L) :
    ReferenceRotationMovingSolutionExclusionBoundary L
最終回答

same-offset theorem は reflection だけからは出ません。 直接出るのは repo の既存 theorem 通り Sol d → Sol (-d) です。

same-offset theorem は数学的には正しいですが、追加で referenceMatchingSolutionSet の d ↔ -d symmetry が必要です。これは無向辺と rotation by -d で証明します。現状の theorem 名としては見当たらないので、mem_referenceMatchingSolutionSet_neg / mem_referenceMatchingSolutionSet_neg_iff を追加すべきです。

endpoint gap から独立な reference-side target としては、ReferenceMatchingAFixingSupportNoAllBoundary も使えますが、これは Sol d = Sol (-d) を先に入れる前提です。より自然で安全な primitive target は

lean
ReferenceMatchingAFixingNoPairedSolutionBoundary

です。

つまり、次の proof architecture に修正するのがよいです。

p ∈ Sol d
  -- existing reflection transport
⇒ A p ∈ Sol (-d)

no paired solution boundary
  ¬ (p ∈ Sol d ∧ A p ∈ Sol (-d))

therefore
  p ∉ Sol d on A-support

therefore
  ReferenceRotationMovingSolutionExclusionBoundary
  → ReferenceRotationMatchingSolutionAFixingSupportComplBoundary

この route は endpoint gap から独立です。依存するのは、reference-side の新しい本質入力

lean
ReferenceMatchingAFixingNoPairedSolutionBoundary

です。
