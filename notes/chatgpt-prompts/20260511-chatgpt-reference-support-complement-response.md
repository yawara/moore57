# ChatGPT response: reference support-complement route

Date: 2026-05-11
Repository commit read by ChatGPT: e0f2adb61ce83c07e37654be2c63838e4ad277d3
Current local follow-up commit at save time: f09bac7 plus local moving-exclusion edits

## Prompt context

Question asked ChatGPT to use the GitHub connector and classify the shortest non-circular route from raw action/default-base data to `RawActionDefaultBaseReferenceSolutionSupportComplBoundary`, including cycle checks and local-obstruction field classification.

## Response

GitHub connector で e0f2adb61ce83c07e37654be2c63838e4ad277d3 を確認し、次を読みました。

gaps.md 

gaps

Moore57/ReflectionRawActionDefaultBaseFrontier.lean 

ReflectionRawActionDefaultBaseF…

Moore57/BranchOrbitABCReferenceSolutionGeometryBoundary.lean 

BranchOrbitABCReferenceSolution…

Moore57/BranchOrbitABCReferenceSolutionFromExceptions.lean 

BranchOrbitABCReferenceSolution…

Moore57/BranchOrbitABCReferenceMatchingLocalObstructionBridge.lean 

BranchOrbitABCReferenceMatching…

Moore57/BranchOrbitABCFixedStarLocalObstructionBoundary.lean 

BranchOrbitABCFixedStarLocalObs…

Moore57/BranchOrbitABCReferenceMatchingLocalObstructionFrontier.lean 

BranchOrbitABCReferenceMatching…

Moore57/BranchOrbitABCDefaultBaseLocalObstructionFrontier.lean 

BranchOrbitABCDefaultBaseLocalO…

Moore57/BranchOrbitABCExceptionCaseBoundary.lean 

BranchOrbitABCExceptionCaseBoun…

Moore57/BranchOrbitABCExceptionCaseEndpointPointwiseBoundary.lean 

BranchOrbitABCExceptionCaseEndp…

Moore57/BranchOrbitABCEndpointSignMatchingSymmetry.lean 

BranchOrbitABCEndpointSignMatch…

Moore57/BranchOrbitABCEndpointPairedSymmetryBoundary.lean 

BranchOrbitABCEndpointPairedSym…

追加で、4-field の出所確認のため BranchOrbitABCExceptionCaseLocalObstruction.lean, BranchOrbitABCExceptionCardOneBoundary.lean, BranchOrbitABCExceptionAllSupportBoundary.lean, BranchOrbitABCCardTwoAllOffsetsNoCardBoundary.lean も読みました。

BranchOrbitABCExceptionCaseLoca…

 

BranchOrbitABCExceptionCardOneB…

 

BranchOrbitABCExceptionAllSuppo…

 

BranchOrbitABCCardTwoAllOffsets…

A. 何を先に証明するのが最短か

最短かつ非循環なのは、FixedStarLocalObstructionBoundary ではなく、default-base labeling ごとの

lean
BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
  (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

を直接証明することです。

理由は単純です。RawActionDefaultBaseReferenceSolutionSupportComplBoundary の field はまさに各 k に対する ReferenceRotationMatchingSolutionAFixingSupportComplBoundary です。そこから Lean は既に

lean
toReferenceRotationMatchingSolutionVertexFixedBoundary
toReferenceRotationToMidpointReflectionBoundary

を持っています。つまり support-complement 形を出せば、reference side は閉じます。

ReflectionRawActionDefaultBaseF…

 

BranchOrbitABCReferenceSolution…

ReferenceMatchingLocalObstructionBoundary は direct support-complement の一段上です。構造体は

lean
aFixing
referenceMatching
singletonFixed
noAllEndpointAdj

を持ち、そこから toMidpointExceptionAFixingSupportCaseBoundary、さらに toReferenceRotationMatchingSolutionAFixingSupportComplBoundary に行きます。

BranchOrbitABCReferenceMatching…

ただし、この route の referenceMatching : ReferenceMatchingPipelineBoundary labeling が危険です。ReferenceMatchingPipelineBoundary は ReferenceRotationToMidpointReflectionBoundary を含む pipeline なので、これを support-complement から作ると循環します。ReferenceMatchingLocalObstructionBoundary を使うなら、referenceMatching は support-complement 由来ではなく、独立に証明済みでなければなりません。

BranchOrbitABCReferenceSolution…

 

BranchOrbitABCReferenceMatching…

FixedStarLocalObstructionBoundary はさらに大きい package です。field は

lean
middle
referenceMatching
localObstruction

で、localObstruction の中に aFixing, singletonFixed, noAllEndpointAdj が入ります。middle は raw action から供給しやすいですが、reference support-complement を得るためには不要です。したがって first target としては大きすぎます。

BranchOrbitABCFixedStarLocalObs…

 

BranchOrbitABCExceptionCaseLoca…

MidpointExceptionAFixingSupportCaseBoundary は、S_(d/2) ∩ E の有限 case split を閉じる boundary です。これは exception disjointness を出すには有効ですが、reference solution を exception set に入れる referenceMatching がなければ support-complement は出ません。したがってこれも単独では first target になりません。

BranchOrbitABCExceptionCaseBoun…

 

BranchOrbitABCReferenceSolution…

判定は次です。

最短:
  ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
  for h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k

次善:
  ReferenceMatchingLocalObstructionBoundary
  ただし referenceMatching が supportCompl / referenceToMidpoint 由来でない場合のみ

避ける:
  FixedStarLocalObstructionBoundary を first target にすること
  -- middle など余分な field を含む

不十分:
  MidpointExceptionAFixingSupportCaseBoundary 単独
  -- referenceMatching がないと supportCompl に届かない
B. 次に実装すべき小 theorem 案
1. direct hard lemma: default-base reference solution は A-support に入らない

これが本命です。

lean
theorem D19ActsOnMoore57.referenceMatchingSolution_not_mem_aFiberReflectionSupport_of_raw_action_defaultBase
    (h : D19ActsOnMoore57 V Γ)
    (k d : ZMod 19) (hd : d ≠ 0)
    (p :
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
        .data.toAFiberCoordinates.P) :
    p ∈
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
          .referenceMatchingSolutionSet d hd →
    p ∉
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
          .aFiberReflectionSupport

同値に、より tactic-friendly には：

lean
theorem D19ActsOnMoore57.false_of_referenceMatchingSolution_mem_aFiberReflectionSupport_of_raw_action_defaultBase
    (h : D19ActsOnMoore57 V Γ)
    (k d : ZMod 19) (hd : d ≠ 0)
    (p :
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
        .data.toAFiberCoordinates.P)
    (hpSol :
      p ∈
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
          .referenceMatchingSolutionSet d hd)
    (hpSupport :
      p ∈
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
          .aFiberReflectionSupport) :
    False

これは既存 referenceMatchingSolutionSet を使うので、matching equation を毎回展開せずに済みます。referenceMatchingSolutionSet は M_d p = R_d p の finset form です。

BranchOrbitABCReferenceSolution…

2. direct hard lemma から per-k support-complement boundary
lean
noncomputable def D19ActsOnMoore57.referenceRotationMatchingSolutionAFixingSupportComplBoundary_of_raw_action_defaultBase_direct
    (h : D19ActsOnMoore57 V Γ)
    (k : ZMod 19)
    (hnot :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p :
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            .data.toAFiberCoordinates.P,
          p ∈
              (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
                .referenceMatchingSolutionSet d hd →
          p ∉
              (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
                .aFiberReflectionSupport) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

proof は：

lean
where
  reference_matching_solution_subset_aFiberReflectionSupport_compl := by
    intro d hd p hpSol
    exact Finset.mem_compl.mpr (hnot d hd p hpSol)
3. per-k support-complement から raw-action package
lean
noncomputable def D19ActsOnMoore57.rawActionDefaultBaseReferenceSolutionSupportComplBoundary_of_direct
    (h : D19ActsOnMoore57 V Γ)
    (hcompl :
      ∀ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary h where
  supportCompl := hcompl

これは既存 structure の薄い constructor です。

ReflectionRawActionDefaultBaseF…

4. raw action で aFixing を自動注入する local-obstruction wrapper

ReferenceMatchingLocalObstructionBoundary を使う route を残すなら、raw supplied field を消す wrapper が有用です。

lean
noncomputable def D19ActsOnMoore57.referenceMatchingLocalObstructionBoundary_of_raw_action_defaultBase_fields
    (h : D19ActsOnMoore57 V Γ)
    (k : ZMod 19)
    (referenceMatching :
      BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (singletonFixed :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingLocalObstructionBoundary
      h.reflectionFixedStarBoundary_of_raw_action
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
{ aFixing :=
    (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.reflectionFixedStarAFixingBoundary_of_raw_action
  referenceMatching := referenceMatching
  singletonFixed := singletonFixed
  noAllEndpointAdj := noAllEndpointAdj }

これは aFixing が raw action で供給済みであることを Lean に明示します。

ReflectionRawActionDefaultBaseF…

 

BranchOrbitABCReferenceMatching…

5. local-obstruction fields から raw-action support-complement package
lean
noncomputable def D19ActsOnMoore57.rawActionDefaultBaseReferenceSolutionSupportComplBoundary_of_localObstruction_fields
    (h : D19ActsOnMoore57 V Γ)
    (referenceMatching :
      ∀ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (singletonFixed :
      ∀ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      ∀ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary h :=
  D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary
    .of_referenceMatchingLocalObstruction
      (fun k =>
        h.referenceMatchingLocalObstructionBoundary_of_raw_action_defaultBase_fields
          k (referenceMatching k) (singletonFixed k) (noAllEndpointAdj k))

この theorem は「local-obstruction route を採るなら、残り3 field は何か」を明確化します。ただし referenceMatching を support-complement から作らない、という条件が必要です。

6. FixedStarLocalObstructionBoundary は raw package には不要であることを明示する wrapper

既存に RawActionDefaultBaseReferenceSolutionSupportComplBoundary.of_fixedStarLocalObstruction はありますが、FixedStarLocalObstructionBoundary が大きい route であることを Codex が見失わないよう、ReferenceMatchingLocalObstructionBoundary への縮約を別名で置くのは有用です。

lean
noncomputable def BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
    .toReferenceMatchingLocalObstructionBoundary
    {star : ReflectionFixedStarBoundary h}
    {labeling : BranchOrbitABCReflectionLabeling h}
    (B : BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary star labeling) :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingLocalObstructionBoundary star labeling :=
{ aFixing := B.localObstruction.aFixing
  referenceMatching := B.referenceMatching
  singletonFixed := B.localObstruction.singletonFixed
  noAllEndpointAdj := B.localObstruction.noAllEndpointAdj }

今の toReferenceRotationMatchingSolutionAFixingSupportComplBoundary の中で inline されている構成を名前にするだけです。

BranchOrbitABCFixedStarLocalObs…

C. 循環性チェック

現状の wiring で最も危険なのは次の循環です。

supportCompl
  → ReferenceRotationToMidpointReflectionBoundary
  → ReferenceMatchingPipelineBoundary
  → ReferenceMatchingLocalObstructionBoundary
  → supportCompl

ReferenceRotationMatchingSolutionAFixingSupportComplBoundary.toReferenceRotationToMidpointReflectionBoundary は既に追加されています。したがって、referenceMatching field をこの consequence から作って ReferenceMatchingLocalObstructionBoundary に入れると循環します。

BranchOrbitABCReferenceSolution…

 

BranchOrbitABCReferenceMatching…

Endpoint pointwise nonadjacency から case boundary や endpoint side が出る route もありますが、それは endpoint gap に依存します。BranchOrbitABCExceptionCaseEndpointPointwiseBoundary.lean は、pointwise endpoint nonadjacency を使って MidpointExceptionAFixingSupportCaseBoundary を作る route を明示しています。これは reference side を endpoint gap から出す route なので、独立な reference proof としては使わない方がよいです。

BranchOrbitABCExceptionCaseEndp…

Cameron Step 2 / label exchange から reference support-complement を endpoint gap と独立に出せる自然な議論が、今の repo の theorem 名だけで既にあるかというと、まだないです。endpoint label exchange として Lean に入っているのは corrected negative-pair form:

lean
EndpointSignNegativeMatchingPairBoundary
EndpointSignPairedAdjacencyBoundary

であり、これは paired endpoint target R (A p) を返す形です。old target R p への復帰には same-target equality が必要で、それは別 boundary として分離されています。

BranchOrbitABCEndpointSignMatch…

 

BranchOrbitABCEndpointPairedSym…

reference side で独立にやるなら、戻るべき中間 gap は

lean
ReferenceRotationMatchingSolutionAFixingSupportComplBoundary

そのものです。自然言語では次の主張です。

default-base labeling で、reference matching solution
M_d p = R_d p が A-fixing reflection support E 上にあることはない。

Lean ではこれを

lean
p ∈ referenceMatchingSolutionSet d hd →
p ∉ aFiberReflectionSupport

として証明するのが最小です。これなら endpoint gap に触れず、ReferenceRotationToMidpointReflectionBoundary も前提にしません。

もしこれが直接難しいなら、次に戻るべき中間 gap は ReferenceMatchingLocalObstructionBoundary ではなく、さらに分解された

lean
MidpointExceptionAFixingSupportSingletonFixedBoundary
MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary

です。ただし NoAllEndpointAdj は endpoint side なので、reference independent route からは外れます。

D. 4 field の分類

ReferenceMatchingLocalObstructionBoundary の4 field は次です。

BranchOrbitABCReferenceMatching…

lean
aFixing
referenceMatching
singletonFixed
noAllEndpointAdj

分類は以下です。

field	raw action から供給済みか	判定
aFixing	はい	reflectionFixedStarAFixingBoundary_of_raw_action で default-base labeling に入る。
referenceMatching	いいえ	ReferenceMatchingPipelineBoundary は ReferenceRotationToMidpointReflectionBoundary を含む。supportCompl を証明するために supportCompl 由来の referenceToMidpoint で作ると循環。
singletonFixed	いいえ	MidpointExceptionAFixingSupportSingletonFixedBoundary は local one-point obstruction。endpoint negative-pair などから no-card-one route はあるが、raw action から無条件供給済みではない。
noAllEndpointAdj	いいえ	raw action は global NoAllOffsetsEndpointAdj を供給するが、local obstruction field は offset-by-offset の MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary。global 版はこの field を埋めるには弱い。

補足すると、FixedStarLocalObstructionBoundary の middle は raw action から供給済みと見てよいです。しかし FixedStarLocalObstructionBoundary を証明しても、実質的に残るのは referenceMatching, singletonFixed, noAllEndpointAdj です。middle と aFixing は raw fixed-star 側で既に処理できます。

BranchOrbitABCFixedStarLocalObs…

 

BranchOrbitABCExceptionCaseLoca…

NoAllOffsetsEndpointAdj については注意が必要です。ReflectionRawActionDefaultBaseFrontier.lean では raw action から

lean
noAllOffsetsEndpointAdj_of_raw_action_defaultBase
noAllOffsetsSupportSubsetBoundary_of_raw_action_defaultBase

が出ています。しかしこれは「全 offset で同時に all endpoint adjacency が起こることはない」という global statement です。ReferenceMatchingLocalObstructionBoundary.noAllEndpointAdj が要求するのは、各 d ごとに

lean
¬ ∀ p ∈ aFiberReflectionSupport, endpoint adjacency at d p

です。global 版から offsetwise 版は出ません。

ReflectionRawActionDefaultBaseF…

 

BranchOrbitABCCardTwoAllOffsets…

実装方針の結論

Codex の次手としては、FixedStarLocalObstructionBoundary を直接狙わない方がよいです。最小 non-circular target はこれです。

lean
theorem D19ActsOnMoore57.referenceRotationMatchingSolutionAFixingSupportComplBoundary_of_raw_action_defaultBase_direct
    (h : D19ActsOnMoore57 V Γ)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

その証明の hard core は

lean
p ∈ referenceMatchingSolutionSet d hd →
p ∉ aFiberReflectionSupport

です。

ReferenceMatchingLocalObstructionBoundary は fallback route として残してよいですが、その referenceMatching field を supportCompl / referenceToMidpoint から作ると循環します。FixedStarLocalObstructionBoundary はさらに大きい wrapper なので、今の reference-side target には過剰です。
