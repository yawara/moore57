# ChatGPT response: reference no-paired solution boundary

Saved: 2026-05-11 19:11:10 JST
Source: ChatGPT browser thread `6a017839-e340-83ab-8dfb-fb729ae2ec73`

確認しました。最新 commit は 3a7b8509432c471dbbc6404c3f4fc5042c200050 です。内容は prompt log の timestamp 化が主で、Lean 本体の relevant change はその直前の状態と整合しています。

Timestamp ChatGPT prompt logs

読んだ主要ファイル:

Moore57/BranchOrbitABCReferenceSolutionGeometryBoundary.lean：referenceMatchingSolutionSet, mem_referenceMatchingSolutionSet_neg, referenceMatchingSolutionSet_neg_iff, aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet, ReferenceMatchingAFixingNoPairedSolutionBoundary, ReferenceMatchingAFixingSupportNoAllBoundary, ReferenceMatchingAFixingSourceExchangeBoundary, ReferenceMatchingAFixingCrossAdjacencyBoundary を確認。

BranchOrbitABCReferenceSolution…

Moore57/ReflectionRawActionDefaultBaseFrontier.lean：raw/default-base 用の RawActionDefaultBaseReferenceNoPairedSolutionBoundary と、それを moving exclusion / support-complement に送る route を確認。

ReflectionRawActionDefaultBaseF…

Moore57/BranchOrbitABCSupportPairBoundary.lean：aFiberReflectionSupport_eq_pair_of_mem, mem_aFiberReflectionSupport_iff_eq_or_eq_reflection_of_mem を確認。

BranchOrbitABCSupportPairBounda…

1. 既存 repo の定義・補題だけで ReferenceMatchingAFixingNoPairedSolutionBoundary は証明できるか

できません。
少なくとも、読んだ範囲の既存補題だけでは endpoint-independent にこの boundary を閉じる theorem は存在しません。

現在 Lean にあるのは、主に次の3種類です。

まず、reference solution set の基本変換です。

lean
mem_referenceMatchingSolutionSet_neg :
  p ∈ Sol d → p ∈ Sol (-d)

referenceMatchingSolutionSet_neg_iff :
  p ∈ Sol (-d) ↔ p ∈ Sol d

aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet :
  p ∈ Sol d → A p ∈ Sol d

ここで Sol d は

lean
L.referenceMatchingSolutionSet d hd

です。これらは BranchOrbitABCReferenceSolutionGeometryBoundary.lean に入っています。

BranchOrbitABCReferenceSolution…

次に、support pair の有限集合補題です。

lean
aFiberReflectionSupport_eq_pair_of_mem :
  p ∈ E → E = {p, A p}

これは AFixingReflectionFixedNeighborCardBoundary から E.card = 2 を使って出ます。

BranchOrbitABCSupportPairBounda…

最後に、NoPaired から downstream へ送る route です。

lean
RawActionDefaultBaseReferenceNoPairedSolutionBoundary
  → RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary
  → RawActionDefaultBaseReferenceSolutionSupportComplBoundary

これは ReflectionRawActionDefaultBaseFrontier.lean に入っています。

ReflectionRawActionDefaultBaseF…

しかし、肝心の

lean
RawActionDefaultBaseReferenceNoPairedSolutionBoundary h

または各 default-base labeling ごとの

lean
ReferenceMatchingAFixingNoPairedSolutionBoundary
  (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

を raw action から構成する theorem は、現状の repo にはありません。

数学的にも、既存補題だけでは矛盾を作れません。仮に

lean
p ∈ L.aFiberReflectionSupport
p ∈ L.referenceMatchingSolutionSet d hd
A p ∈ L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd)

とします。referenceMatchingSolutionSet_neg_iff により、これは実質的に

lean
p ∈ Sol d
A p ∈ Sol d

です。頂点で書くと：

x := reference vertex p
y := reference vertex A p
z := r^d x
w := r^d y

得られる辺は：

x ~ z
y ~ w
x ~ a₀
y ~ a₀
z ~ a_d
w ~ a_d

これは x-a₀-y-w-a_d-z-x 型の 6-cycle 配置です。λ = 0 で x と y の非隣接は出ますが、x,y に第二 common neighbor はありません。μ = 1 で衝突させる材料が不足しています。

したがって、既存 repo の定義・補題だけで NoPaired を証明する route はありません。NoPaired 自体が今の reference-side hard mathematical input です。

2. 証明できる場合の変換列

証明できると仮定したときの Lean 変換列は既にほぼ完成しています。必要 import は raw/default-base theorem なら基本的にこれで足ります。

lean
import Moore57.ReflectionRawActionDefaultBaseFrontier

local theorem を別ファイルで作るなら、より小さく：

lean
import Moore57.BranchOrbitABCReferenceSolutionGeometryBoundary
import Moore57.BranchOrbitABCSupportPairBoundary

現在の変換列は以下です。

Local labeling 版
lean
BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingNoPairedSolutionBoundary
  → BranchOrbitABCReflectionLabeling.ReferenceRotationMovingSolutionExclusionBoundary
  → BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
  → BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary

NoPairedSolutionBoundary と moving-exclusion / support-complement 系の structures は BranchOrbitABCReferenceSolutionGeometryBoundary.lean にあります。

BranchOrbitABCReferenceSolution…

Raw/default-base 版
lean
D19ActsOnMoore57.RawActionDefaultBaseReferenceNoPairedSolutionBoundary
  → D19ActsOnMoore57.RawActionDefaultBaseReferenceMovingSolutionExclusionBoundary
  → D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary

raw package と conversions は ReflectionRawActionDefaultBaseFrontier.lean にあります。

ReflectionRawActionDefaultBaseF…

したがって、Codex がもし hard theorem を入れるなら、最も直接の theorem surface はこれです。

lean
theorem D19ActsOnMoore57.rawActionDefaultBaseReferenceNoPairedSolutionBoundary_of_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    D19ActsOnMoore57.RawActionDefaultBaseReferenceNoPairedSolutionBoundary h

または per-labeling 版：

lean
theorem D19ActsOnMoore57.referenceMatchingAFixingNoPairedSolutionBoundary_of_raw_action_defaultBase
    (h : D19ActsOnMoore57 V Γ)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingNoPairedSolutionBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

中身の field は：

lean
no_paired_reference_solution :
  ∀ d hd p,
    p ∈ L.aFiberReflectionSupport →
      ¬ (p ∈ L.referenceMatchingSolutionSet d hd ∧
          L.aFiberReflectionCoordPerm p ∈
            L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd))

です。

3. 証明できない場合に本当に必要な新しい数学的補題

最小 input は、まさに次です。

lean
theorem BranchOrbitABCReflectionLabeling.no_paired_reference_solution_of_defaultBase_geometry
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P)
    (hp : p ∈ L.aFiberReflectionSupport) :
    ¬ (p ∈ L.referenceMatchingSolutionSet d hd ∧
        L.aFiberReflectionCoordPerm p ∈
          L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd))

raw/default-base に固定するなら：

lean
theorem D19ActsOnMoore57.no_paired_reference_solution_of_raw_action_defaultBase
    (h : D19ActsOnMoore57 V Γ)
    (k d : ZMod 19) (hd : d ≠ 0)
    (p :
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
        .data.toAFiberCoordinates.P)
    (hp :
      p ∈
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
          .aFiberReflectionSupport) :
    ¬
      (p ∈
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            .referenceMatchingSolutionSet d hd ∧
       (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
          .aFiberReflectionCoordPerm p ∈
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            .referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd))

これが endpoint-independent reference-side proof の本体です。

support-pair / common-neighbor / endpoint-free の分類

この補題は support-pair / endpoint-free です。

support-pair: p と A p の2点 support pair を扱う。

endpoint-free: endpoint target endpointCommonNeighborReflectedEndpointVertex や endpoint pointwise nonadjacency を使わない。

common-neighbor ではない: 現状の2本の reference-solution edge からは common-neighbor collision が作れない。

もし common-neighbor で閉じたいなら、さらに強い cross adjacency が必要です。repo にはその boundary も定義されています。

lean
ReferenceMatchingAFixingCrossAdjacencyBoundary

中身は概念的に：

lean
p ∈ support →
p ∈ Sol d →
Γ.Adj (reference vertex A p) (rotated target R_d p)

です。これは ReferenceMatchingAFixingSourceExchangeBoundary と同等方向に使え、matching injectivity で support contradiction を作れます。ReferenceMatchingAFixingCrossAdjacencyBoundary と ReferenceMatchingAFixingSourceExchangeBoundary は BranchOrbitABCReferenceSolutionGeometryBoundary.lean にあります。

BranchOrbitABCReferenceSolution…

ただし、これは NoPaired より強いです。実際：

lean
M_d p = R_d p
M_d (A p) = R_d p

を作るので、M_d.injective から A p = p となり、support に反します。

したがって、最小 hard lemma としては cross adjacency ではなく、NoPaired を推奨します。

4. endpoint gap を使う route は別

endpoint gap を使うなら、たとえば endpoint-positive target や endpoint exchange から moving support 上の matching を潰す route はあります。しかしこれは reference-side proof ではありません。

今回欲しい endpoint-independent route では、以下を使わないのが正しいです。

lean
EndpointReferenceExchangeCommonNeighborBoundary
MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
EndpointSignNoReflectedReferenceNegMatchingBoundary
EndpointMatchingAFixingNoPositiveTargetBoundary
ReferenceMatchingPipelineBoundary
ReferenceRotationToMidpointReflectionBoundary

特に ReferenceMatchingPipelineBoundary は ReferenceRotationToMidpointReflectionBoundary を field として持つので、support-complement を証明する前提に使うと循環します。

実装すべき theorem 名と statement

まず、既に transformation route はあるので、Codex が本当に実装すべき最初の theorem はこれです。

lean
theorem D19ActsOnMoore57.referenceMatchingAFixingNoPairedSolutionBoundary_of_raw_action_defaultBase
    (h : D19ActsOnMoore57 V Γ)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingNoPairedSolutionBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

中身は：

lean
where
  no_paired_reference_solution := by
    intro d hd p hpSupport hpair
    ...

次に raw package wrapper：

lean
theorem D19ActsOnMoore57.rawActionDefaultBaseReferenceNoPairedSolutionBoundary_of_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    D19ActsOnMoore57.RawActionDefaultBaseReferenceNoPairedSolutionBoundary h where
  noPairedSolution k :=
    h.referenceMatchingAFixingNoPairedSolutionBoundary_of_raw_action_defaultBase k

そして既存 route で support-complement：

lean
noncomputable def D19ActsOnMoore57.rawActionDefaultBaseReferenceSolutionSupportComplBoundary_of_noPairedSolution
    (h : D19ActsOnMoore57 V Γ)
    (B : D19ActsOnMoore57.RawActionDefaultBaseReferenceNoPairedSolutionBoundary h) :
    D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary h :=
  B.toRawActionDefaultBaseReferenceSolutionSupportComplBoundary

この最後の def は既存 conversion を使うだけなので、必要なら別名 alias として置く程度です。

ReflectionRawActionDefaultBaseF…

何がまだ数学的に足りないか

足りないのは、次の純 reference-side 幾何命題です。

A-fixing reflection moving support の2点 p, A p が、互いに反射対応する reference matching solution pair
p ∈ Sol d and A p ∈ Sol (-d)
を同時に満たすことはない。

これを λ/μ だけで自動的に証明する既存配置はありません。現状得られる reference-solution edges は 6-cycle 型であり、common-neighbor collision を作りません。したがって、endpoint-independent に閉じるなら、support-pair endpoint-free の NoPairedSolutionBoundary が本当の数学入力です。Common-neighbor で閉じたい場合は、より強い ReferenceMatchingAFixingCrossAdjacencyBoundary 型の新入力が必要です。

最終判定：

既存補題だけでは NoPairedSolutionBoundary は証明できない。
endpoint-independent に必要な最小 input は
ReferenceMatchingAFixingNoPairedSolutionBoundary。
これは support-pair / endpoint-free であり、common-neighbor 型ではない。
endpoint gap を使う route は分離すべき。
