# ChatGPT GitHub Endpoint Frontier Response

Date: 2026-05-11
Repository: https://github.com/yawara/moore57
Commit requested: 306ac72

## Response

GitHub connector で commit 306ac723d2b649d41aa1a0f0bdc879a981224ebb を確認し、指定ファイルを読みました。対象 commit は “Add endpoint exchange common-neighbor frontier” です。

Add endpoint exchange common-ne…

読んだファイル:

gaps.md 

gaps

papers_info.md 

papers_info

Moore57/BranchOrbitABCEndpointExchangeCommonNeighborBoundary.lean 

BranchOrbitABCEndpointExchangeC…

Moore57/BranchOrbitABCEndpointCommonNeighborBasic.lean 

BranchOrbitABCEndpointCommonNei…

Moore57/BranchOrbitABCEndpointSignAdjacencyBoundary.lean 

BranchOrbitABCEndpointSignAdjac…

Moore57/BranchOrbitABCEndpointPairedSymmetryBoundary.lean 

BranchOrbitABCEndpointPairedSym…

Moore57/BranchOrbitABCEndpointSignMatchingSymmetry.lean 

BranchOrbitABCEndpointSignMatch…

Moore57/BranchOrbitABCMatchingTargetReflectionReduced.lean 

BranchOrbitABCMatchingTargetRef…

Moore57/BranchOrbitABCMidpointExceptionSetBoundary.lean 

BranchOrbitABCMidpointException…

Moore57/BranchOrbitABCCardTwoCommonNeighborBoundary.lean 

BranchOrbitABCCardTwoCommonNeig…

Moore57/ReflectionRawActionFixedStar.lean 

ReflectionRawActionFixedStar

Moore57/D19RotationSplitRawActionNoGoConnectors.lean 

D19RotationSplitRawActionNoGoCo…

追加で、依存確認のため BranchOrbitABCReferenceSolutionFixedBoundary.lean, BranchOrbitABCReferenceSolutionGeometryBoundary.lean, BranchOrbitABCReferenceMatchingPipeline.lean も読みました。

BranchOrbitABCReferenceSolution…

 

BranchOrbitABCReferenceSolution…

 

BranchOrbitABCReferenceMatching…

判定

EndpointReferenceExchangeCommonNeighborBoundary は Lean の現在の common-neighbor collision には非常に都合がよいですが、Cameron Ch.3 Step 2 風の label exchange からそのまま出る最小幾何入力としては 強すぎます。

この境界の statement は、実質的に次です。

lean
r_p ~ x_{d,p}  →  r_{A p} ~ x_{d,p}

ここで

lean
r_p     := labeling.endpointCommonNeighborReferenceVertex p
r_{A p} := labeling.endpointCommonNeighborReferenceVertex
             (labeling.aFiberReflectionCoordPerm p)

x_{d,p} := labeling.endpointCommonNeighborReflectedEndpointVertex d p
y_{d,p} := labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p

EndpointReferenceExchangeCommonNeighborBoundary があれば、repo 内の証明通り、endpoint pair を

lean
x := x_{d,p}
y := y_{d,p}

common neighbors を

lean
z := r_p
w := r_{A p}

として置けます。辺は次の4本です。

lean
x ~ z   -- original endpoint adjacency
x ~ w   -- EndpointReferenceExchange
y ~ z   -- EndpointReferenceExchange を A-fixing reflection で反射
y ~ w   -- original endpoint adjacency を A-fixing reflection で反射

さらに

lean
x ≠ y   -- d ≠ 0, endpointCommonNeighbor_reflected_endpoints_ne
z ≠ w   -- p ∈ aFiberReflectionSupport

なので、h.isMoore.no_two_commonNeighbors で矛盾が閉じます。この部分は Lean 的に正しいです。IsMoore57.not_adj_of_commonNeighbor, eq_of_commonNeighbor_of_commonNeighbor, no_two_commonNeighbors も commit で追加済みです。

BranchOrbitABCEndpointExchangeC…

 

BranchOrbitABCCardTwoCommonNeig…

問題は、r_p ~ x_{d,p} → r_{A p} ~ x_{d,p} という 同じ target endpoint を保った source-coordinate exchange が、raw A-fixing reflection からは出ないことです。

A-fixing reflection から直接出るのは repo に既にある

lean
aFixing_reflected_endpoint_adj_reflected_reference_of_endpoint_adj

で、これは

lean
r_p ~ x_{d,p}  →  y_{d,p} ~ r_{A p}

です。つまり、source だけでなく endpoint target も反射されます。

BranchOrbitABCEndpointSignAdjac…

さらに corrected paired symmetry から自然に出るのは

lean
EndpointSignPairedAdjacencyBoundary

であり、これは

lean
y_{d,p} ~ r_{A p}
  →
endpointCommonNeighborAFixingPairedReflectedEndpointVertex d p ~ r_p

です。ここで paired target は

lean
endpointCommonNeighborAFixingPairedReflectedEndpointVertex d p
= coord (0 + (-d)) (R_{-d} (A p))

であって、古い

lean
endpointCommonNeighborAFixingReflectedEndpointVertex d p
= coord (0 + (-d)) (R_{-d} p)

ではありません。repo のコメントも、この paired target が corrected statement であり、旧 EndpointSignMatchingBoundary は target R p を保つため強すぎる、と明示しています。

BranchOrbitABCEndpointPairedSym…

 

BranchOrbitABCEndpointSignMatch…

したがって、Step 2 型 label exchange から直接出る endpoint 側の正しい形式は

lean
EndpointSignNegativeMatchingPairBoundary

または adjacency 版の

lean
EndpointSignPairedAdjacencyBoundary

です。EndpointReferenceExchangeCommonNeighborBoundary は、その後にさらに

lean
R_{-d}(A p) = R_{-d} p

型の same-target equality を入れた場合に初めて旧 endpoint common-neighbor input へ戻れます。しかし p ∈ aFiberReflectionSupport では A p ≠ p で、R_{-d} は permutation なので、この same-target equality 自体が不可能です。

A. 1 と 2 のどちらを先に狙うべきか

現在の repo 状態から見ると、次に本気で証明対象にすべきなのは 1、ただし ReferenceRotationToMidpointReflectionBoundary そのものではなく、より強い

lean
ReferenceRotationMatchingSolutionVertexFixedBoundary

です。

理由は2つです。

第一に、ReferenceRotationToMidpointReflectionBoundary は repo 内で既に

lean
ReferenceRotationToMidpointReflectionBoundary.of_aFixingFixed

により

lean
ReferenceRotationEquationAFixingFixedBoundary

から作れるようになっています。さらに

lean
ReferenceRotationMatchingSolutionVertexFixedBoundary
  → ReferenceRotationEquationAFixingFixedBoundary
  → ReferenceRotationToMidpointReflectionBoundary

という wrapper も明確です。

BranchOrbitABCMidpointException…

 

BranchOrbitABCReferenceSolution…

第二に、endpoint 側の EndpointReferenceExchangeCommonNeighborBoundary は、matching form に直すとかなり露骨に強いです。M_d を

lean
AFiberCoordinates.matchingEquiv h.isMoore
  labeling.data.toAFiberCoordinates 0 (0 + d)
  (index_ne_add_of_ne_zero hd)

A を

lean
labeling.aFiberReflectionCoordPerm

R_d を

lean
labeling.data.toAFiberRotationEquivariance.coordPerm d 0

と書くと、r_p ~ x_{d,p} は

lean
M_d p = R_d (A p)

です。一方、r_{A p} ~ x_{d,p} は

lean
M_d (A p) = R_d (A p)

です。つまり EndpointReferenceExchangeCommonNeighborBoundary は support 上で

lean
M_d p = R_d (A p)
  →
M_d (A p) = R_d (A p)

を要求しています。M_d は equivalence なので、前件と後件が同時に成り立てば p = A p です。support 上ではこれは矛盾です。したがってこの境界は、実質的に

lean
¬ M_d p = R_d (A p)

つまり endpoint pointwise nonadjacency を既に含んでいます。

これは Lean input としては使いやすいですが、raw action/default-base から証明するには endpoint obstruction そのものをもう証明している必要があります。よって、これを「label exchange の最小幾何入力」として追うのは非推奨です。

B. 最も有望な target と補題列

推奨 target は次です。

lean
ReferenceRotationMatchingSolutionVertexFixedBoundary labeling

statement は既存ファイル通りです。

lean
structure ReferenceRotationMatchingSolutionVertexFixedBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  reference_solution_vertex_fixed :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p →
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (((labeling.data.toAFiberCoordinates.coord 0 p : _) : V)) =
          (((labeling.data.toAFiberCoordinates.coord 0 p : _) : V))

Lean に落とす最小補題列は、まずこの境界をさらに support-complement statement に落とすのがよいです。repo には既に

lean
referenceMatchingSolutionSet
referenceMatchingSolutionSet_eq_matchingRotationPerm_support_compl
ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
ReferenceRotationMatchingSolutionAFixingSupportComplBoundary.toReferenceRotationMatchingSolutionVertexFixedBoundary

があります。

BranchOrbitABCReferenceSolution…

したがって、Codex が次に狙うべき hard lemma はこの形です。

lean
structure ReferenceRotationMovingSolutionExclusionBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  no_moving_reference_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          ¬
            AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd) p =
            labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p

そこから既存境界へは完全に formal です。

lean
noncomputable def
  ReferenceRotationMovingSolutionExclusionBoundary
    .toReferenceRotationMatchingSolutionVertexFixedBoundary
    {labeling : BranchOrbitABCReflectionLabeling h}
    (B : ReferenceRotationMovingSolutionExclusionBoundary labeling) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling :=
by
  refine
    ReferenceRotationMatchingSolutionVertexFixedBoundary
      .of_referenceMatchingSolutionSet_subset_aFiberReflectionSupport_compl
      (labeling := labeling) ?_
  intro d hd p hpSol
  rw [Finset.mem_compl]
  intro hpSupport
  exact B.no_moving_reference_solution d hd p hpSupport
    ((labeling.mem_referenceMatchingSolutionSet d hd p).1 hpSol)

そして

lean
noncomputable def
  ReferenceRotationMovingSolutionExclusionBoundary
    .toReferenceRotationToMidpointReflectionBoundary
    {labeling : BranchOrbitABCReflectionLabeling h}
    (B : ReferenceRotationMovingSolutionExclusionBoundary labeling) :
    ReferenceRotationToMidpointReflectionBoundary labeling :=
  ReferenceRotationToMidpointReflectionBoundary.of_aFixingFixed
    (B.toReferenceRotationMatchingSolutionVertexFixedBoundary
      |>.toReferenceRotationEquationAFixingFixedBoundary)

自然言語証明としては、次を hard geometric input にします。

reference matching solution M_d p = R_d p は、reference fiber vertex r_p が offset d の rotation matching で自分の rotated label に接続されることを意味する。p が A-fixing support に入っているなら、A-fixing reflection は r_p を r_{A p} に動かす。Cameron Step 2 型の label exchange は、この moved two-cycle が reference matching solution set の support-complement、すなわち fixed-label 側に入ることを禁止する。したがって reference solution は support complement に含まれ、A p = p、すなわち reference vertex fixedness が出る。

ここで重要なのは、この geometric input を endpoint target exchange と混ぜないことです。ReferenceRotationMovingSolutionExclusionBoundary は「reference solution が A-moving support に存在しない」という statement であり、EndpointReferenceExchangeCommonNeighborBoundary のように endpoint target を同じまま source を交換する主張を含みません。

C. EndpointReferenceExchangeCommonNeighborBoundary を raw action/default-base から証明する道について

現状の既存定義に沿うと、非循環な道は見えません。理由は明確です。

出発点:

lean
hadj :
  Γ.Adj
    (labeling.endpointCommonNeighborReferenceVertex p)
    (labeling.endpointCommonNeighborReflectedEndpointVertex d p)

これは matching equation では

lean
M_d p = R_d (A p)

です。repo ではこの方向が

lean
endpoint_targetSign_hyp_of_endpoint_adj

としてあります。

BranchOrbitABCEndpointSignAdjac…

A-fixing reflection で formal に得られるのは

lean
Γ.Adj
  (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p)
  (labeling.endpointCommonNeighborReferenceVertex (A p))

つまり

lean
y_{d,p} ~ r_{A p}

です。これは aFixing_reflected_endpoint_adj_reflected_reference_of_endpoint_adj で既に証明済みです。

BranchOrbitABCEndpointSignAdjac…

corrected label exchange / paired symmetry が与えるのは

lean
EndpointSignPairedAdjacencyBoundary

の結論:

lean
Γ.Adj
  (labeling.endpointCommonNeighborAFixingPairedReflectedEndpointVertex d p)
  (labeling.endpointCommonNeighborReferenceVertex p)

です。ここで endpoint は R_{-d}(A p) 側です。

BranchOrbitABCEndpointPairedSym…

しかし MidpointExceptionEndpointAdjCommonNeighborBasicBoundary に必要なのは

lean
Γ.Adj
  (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p)
  (labeling.endpointCommonNeighborReferenceVertex p)

であり、こちらの endpoint は R_{-d} p 側です。したがって paired symmetry だけでは target が1つずれます。

その差を埋めるには

lean
endpointCommonNeighborAFixingPairedReflectedEndpointVertex d p
=
endpointCommonNeighborAFixingReflectedEndpointVertex d p

が必要です。repo ではこれが EndpointSignPairedTargetEqualityBoundary として分離されています。

BranchOrbitABCEndpointPairedSym…

しかし support 上ではこれは期待すべきではありません。定義を展開すると

lean
coord (0 + (-d)) (R_{-d} (A p))
=
coord (0 + (-d)) (R_{-d} p)

であり、coordinate map と R_{-d} の injectivity から A p = p を意味します。p ∈ aFiberReflectionSupport では矛盾です。

したがって、EndpointReferenceExchangeCommonNeighborBoundary を raw action/default-base から証明するルートは、実質的に

lean
M_d p = R_d (A p)

という endpoint-positive-target premise が support 上で不可能であることを先に証明するルートです。これは MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary / EndpointSignNoReflectedReferenceNegMatchingBoundary と同等の hard endpoint obstruction であり、label exchange の小補題ではありません。

結論:

EndpointReferenceExchangeCommonNeighborBoundary は downstream connector としてはよい。

ただし raw/default-base から直接証明する target としては強すぎる。

endpoint 側を matching equation で書くなら、正しい label exchange 名は

lean
EndpointSignNegativeMatchingPairBoundary

または adjacency 版

lean
EndpointSignPairedAdjacencyBoundary

です。

final obstruction 用 endpoint input として残すなら

lean
EndpointSignNoReflectedReferenceNegMatchingBoundary

または

lean
MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

を狙うべきです。

D. 次に Codex が実装すべき小 theorem 案
1. endpoint adjacency と positive matching equation の iff

既に片方向 endpoint_targetSign_hyp_of_endpoint_adj はあります。逆方向もまとめて iff にすると、EndpointReferenceExchangeCommonNeighborBoundary の強さが見えます。

lean
theorem endpointCommonNeighbor_endpoint_adj_iff_positive_target_matching
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    Γ.Adj
      (labeling.endpointCommonNeighborReferenceVertex p)
      (labeling.endpointCommonNeighborReflectedEndpointVertex d p)
    ↔
    AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + d)
        (index_ne_add_of_ne_zero hd) p =
      labeling.data.toAFiberRotationEquivariance.coordPerm d 0
        (labeling.aFiberReflectionCoordPerm p)
2. EndpointReferenceExchangeCommonNeighborBoundary の matching equation 版
lean
structure EndpointReferenceExchangePositiveMatchingBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  positive_matching_exchange :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd) p =
            labeling.data.toAFiberRotationEquivariance.coordPerm d 0
              (labeling.aFiberReflectionCoordPerm p) →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd)
              (labeling.aFiberReflectionCoordPerm p) =
            labeling.data.toAFiberRotationEquivariance.coordPerm d 0
              (labeling.aFiberReflectionCoordPerm p)

そして conversion:

lean
def EndpointReferenceExchangePositiveMatchingBoundary
    .toEndpointReferenceExchangeCommonNeighborBoundary :
    EndpointReferenceExchangeCommonNeighborBoundary labeling

def EndpointReferenceExchangeCommonNeighborBoundary
    .toEndpointReferenceExchangePositiveMatchingBoundary :
    EndpointReferenceExchangePositiveMatchingBoundary labeling
3. positive exchange が endpoint obstruction そのものを含むことを明示
lean
def EndpointReferenceExchangePositiveMatchingBoundary
    .toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
    (B : EndpointReferenceExchangePositiveMatchingBoundary labeling) :
    MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling

証明は、hadj を iff で M_d p = R_d (A p) に変換し、B で M_d (A p) = R_d (A p) を得て、M_d.injective から p = A p、support と矛盾、で閉じます。これは common-neighbor collision より短い diagnostic proof になります。

4. paired target と old target は support 上で異なる
lean
theorem endpointCommonNeighborAFixingPairedReflectedEndpointVertex_ne_reflected
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19)
    (p : labeling.data.toAFiberCoordinates.P)
    (hp : p ∈ labeling.aFiberReflectionSupport) :
    labeling.endpointCommonNeighborAFixingPairedReflectedEndpointVertex d p ≠
      labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p

これは EndpointSignPairedTargetEqualityBoundary が support 上で vacuous でなければならないことを Lean に見せるための補助定理です。

5. paired adjacency から old exchange へ戻るには target equality が必要、という wrapper
lean
def EndpointSignPairedAdjacencyBoundary
    .toEndpointReferenceExchangeCommonNeighborBoundary_of_targetEq
    (paired : EndpointSignPairedAdjacencyBoundary labeling)
    (targetEq : EndpointSignPairedTargetEqualityBoundary labeling) :
    EndpointReferenceExchangeCommonNeighborBoundary labeling

中身は既存 route の合成です。

lean
paired.toEndpointSignAdjacencyBoundary targetEq
  |>.toMidpointExceptionEndpointAdjCommonNeighborBasicBoundary
  |>.toEndpointReferenceExchangeCommonNeighborBoundary

これにより、「paired symmetry alone では足りず、same-target equality が必要」という依存が明示されます。

6. reference 側の推奨 hard input
lean
structure ReferenceRotationMovingSolutionExclusionBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  no_moving_reference_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          ¬
            AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd) p =
            labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p

formal conversions:

lean
def ReferenceRotationMovingSolutionExclusionBoundary
    .toReferenceRotationMatchingSolutionVertexFixedBoundary :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling

def ReferenceRotationMovingSolutionExclusionBoundary
    .toReferenceRotationToMidpointReflectionBoundary :
    ReferenceRotationToMidpointReflectionBoundary labeling

この6番を fixedCenterLeafDefaultBaseLabeling_of_raw_action k に対して証明するのが、次の本命です。

最終判断

EndpointReferenceExchangeCommonNeighborBoundary は、現在の Lean downstream を閉じるには有効ですが、Cameron Step 2 型 label exchange の最小自然主張ではありません。matching equation で見ると、support 上の endpoint-positive-target matching を即座に潰す強い仮定です。

raw action/default-base から非循環に狙うなら、優先度は次です。

1. ReferenceRotationMatchingSolutionVertexFixedBoundary
   またはその support-complement 版
   ReferenceRotationMovingSolutionExclusionBoundary

2. endpoint 側なら EndpointReferenceExchange ではなく
   EndpointSignNoReflectedReferenceNegMatchingBoundary
   / MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

3. label exchange として直接 formalize するなら
   EndpointSignNegativeMatchingPairBoundary
   / EndpointSignPairedAdjacencyBoundary

EndpointReferenceExchangeCommonNeighborBoundary は残してよいですが、証明目標としては「corrected paired exchange + impossible same-target equality」を隠してしまうため、次の raw-action proof target にはしない方がよいです。
