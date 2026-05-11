# ChatGPT response: support-pair exclusion direction

Date: 2026-05-11
Thread: https://chatgpt.com/c/6a017839-e340-83ab-8dfb-fb729ae2ec73

## Prompt context

The user asked ChatGPT to give a natural-language proof target with a real goal, after the previous endpoint-independent pointwise reference support-complement route looked questionable.

## Response

結論から言うと、全体の方向性はまずくないです。ただし、いま狙っている

lean
p ∈ L.referenceMatchingSolutionSet d hd →
p ∉ L.aFiberReflectionSupport

を pointwise に直接、λ/μ common-neighbor だけで証明しようとする方向はまずいです。そこには自然な矛盾が出ません。

次に証明すべき本体は、pointwise support-complement ではなく、次の support-pair exclusion です。

lean
structure ReferenceMatchingAFixingSupportNoAllBoundary
    (L : BranchOrbitABCReflectionLabeling h) : Prop where
  not_all_support_reference_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ¬ ∀ p : L.data.toAFiberCoordinates.P,
          p ∈ L.aFiberReflectionSupport →
            p ∈ L.referenceMatchingSolutionSet d hd

つまり自然言語では：

A-fixing reflection の moving support E = L.aFiberReflectionSupport の2点が、同じ offset d の reference matching solution set に丸ごと入ることはない。

これを証明すれば、現在ほしい pointwise hard core は Lean で形式的に出せます。

1. なぜ pointwise ではなく support-pair exclusion なのか

記号を置きます。

lean
L      := h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k
coords := L.data.toAFiberCoordinates
A      := L.aFiberReflectionCoordPerm
E      := L.aFiberReflectionSupport

M_d    := AFiberCoordinates.matchingEquiv h.isMoore coords 0 (0 + d)
            (index_ne_add_of_ne_zero hd)

R_d    := L.data.toAFiberRotationEquivariance.coordPerm d 0

referenceMatchingSolutionSet は、定義上

lean
p ∈ L.referenceMatchingSolutionSet d hd

が

lean
M_d p = R_d p

と同値です。これは repo 内で referenceMatchingSolutionSet / mem_referenceMatchingSolutionSet として定義済みです。

BranchOrbitABCReferenceSolution…

また M_d p = R_d p は、matching adjacency equivalence により、頂点

lean
x_p := L.referenceFiberVertex p

がその rotation target

lean
r^d x_p

に隣接する、という意味です。matchingEquiv と adj_iff_matchingEquiv_eq は AFiberMatchingPerm.lean にあります。

AFiberMatchingPerm

ここで重要なのは、A-fixing reflection によって reference solution set は 同じ offset d で不変になることです。

自然言語証明はこうです。

仮に

x_p ~ r^d x_p

とする。A-fixing reflection を θ と書くと、

θ x_p = x_{A p}

です。これは coord_aFiberReflectionCoordPerm_apply_val に対応します。

BranchOrbitABCReflectionLabeling

辺 x_p ~ r^d x_p に θ を作用させると、

x_{A p} ~ r^{-d} x_{A p}

を得ます。グラフは無向なので

r^{-d} x_{A p} ~ x_{A p}

です。これに rotation r^d を作用させると

x_{A p} ~ r^d x_{A p}

となります。つまり

lean
A p ∈ L.referenceMatchingSolutionSet d hd

です。

したがって、もし p ∈ E かつ p ∈ Sol_d なら、A p ∈ E かつ A p ∈ Sol_d も成り立ちます。raw action から E.card = 2 が出るので、E = {p, A p} です。よって

lean
E ⊆ Sol_d

になります。

つまり hard core

lean
Sol_d ∩ E = ∅

は、実質的に

lean
¬ E ⊆ Sol_d

を証明すればよい、という構造です。

2. λ=0 / μ=1 だけではなぜ閉じないか

p ∈ E かつ p ∈ Sol_d と仮定します。頂点を置きます。

x := x_p
y := x_{A p}

z := r^d x
w := r^d y

得られる辺は：

x ~ z        -- p ∈ Sol_d
y ~ w        -- A-invariance of Sol_d
x ~ a_0      -- x is in the reference A-fiber
y ~ a_0      -- y is in the same reference A-fiber
z ~ a_d
w ~ a_d

さらに p ∈ E から x ≠ y です。x と y は common neighbor a_0 を持つので、λ = 0 により

x ∤ y

は出ます。

しかし、ここで second common neighbor はありません。z は x に隣接しますが、y に隣接するとは限りません。w は y に隣接しますが、x に隣接するとは限りません。

構図は

x -- z -- a_d -- w -- y -- a_0 -- x

という 6-cycle 型です。Moore graph は triangle と 4-cycle を禁止しますが、6-cycle 自体は λ=0, μ=1 だけでは禁止されません。

したがって、common-neighbor collision で hard core を直接閉じる道はありません。ここが現在の詰まりの本質です。

3. では何を証明すべきか

証明すべき本体はこれです。

lean
structure BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSupportNoAllBoundary
    (L : BranchOrbitABCReflectionLabeling h) : Prop where
  not_all_support_reference_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ¬ ∀ p : L.data.toAFiberCoordinates.P,
          p ∈ L.aFiberReflectionSupport →
            p ∈ L.referenceMatchingSolutionSet d hd

default-base raw action 用には：

lean
theorem D19ActsOnMoore57.referenceMatchingAFixingSupportNoAllBoundary_of_raw_action_defaultBase
    (h : D19ActsOnMoore57 V Γ)
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSupportNoAllBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)

これが Cameron Step 2 風の label exchange から出すべき最小幾何入力です。

pointwise ではなく「support の2点全部が reference solution になることはない」と言うべきです。理由は、reference solution は A-fixing reflection に対して pairwise に運ばれるので、support 上では「0点か2点」しか起こらないからです。

4. その theorem から現在の hard core を出す証明

これは Lean に落ちます。

必要な補題は3つです。

補題1: reference solution set の A-invariance
lean
theorem BranchOrbitABCReflectionLabeling.aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P) :
    p ∈ L.referenceMatchingSolutionSet d hd →
      L.aFiberReflectionCoordPerm p ∈ L.referenceMatchingSolutionSet d hd

自然言語証明は上で書いた通りです。

x_p ~ r^d x_p
apply θ:
x_{A p} ~ r^{-d} x_{A p}
symmetry + rotate by d:
x_{A p} ~ r^d x_{A p}

これは endpoint gap も ReferenceMatchingPipelineBoundary も使いません。

補題2: support は {p, A p}

raw action から AFixingReflectionFixedNeighborCardBoundary が出て、そこから

lean
L.aFiberReflectionSupport.card = 2

が出ます。

BranchOrbitABCAFixingReflection…

したがって：

lean
theorem BranchOrbitABCReflectionLabeling.aFiberReflectionSupport_eq_pair_of_mem
    (L : BranchOrbitABCReflectionLabeling h)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary L)
    (p : L.data.toAFiberCoordinates.P)
    (hp : p ∈ L.aFiberReflectionSupport) :
    L.aFiberReflectionSupport =
      ({p, L.aFiberReflectionCoordPerm p} : Finset L.data.toAFiberCoordinates.P)

自然言語証明：

p ∈ E なので A p ≠ p;

A は involution なので A p ∈ E;

E.card = 2;

よって E はちょうど {p, A p}。

補題3: no-all-support から support-complement
lean
noncomputable def BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSupportNoAllBoundary
    .toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    {L : BranchOrbitABCReflectionLabeling h}
    (B : ReferenceMatchingAFixingSupportNoAllBoundary L)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary L) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary L

証明の流れ：

lean
intro d hd p hpSol
rw [Finset.mem_compl]
intro hpSupport

have hApSol :
    L.aFiberReflectionCoordPerm p ∈ L.referenceMatchingSolutionSet d hd :=
  L.aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet d hd p hpSol

have hE :
    L.aFiberReflectionSupport =
      ({p, L.aFiberReflectionCoordPerm p} : Finset _) :=
  L.aFiberReflectionSupport_eq_pair_of_mem supportCard p hpSupport

have hall :
    ∀ q, q ∈ L.aFiberReflectionSupport →
      q ∈ L.referenceMatchingSolutionSet d hd := by
  intro q hq
  rw [hE] at hq
  simp at hq
  rcases hq with hq | hq
  · simpa [hq] using hpSol
  · simpa [hq] using hApSol

exact B.not_all_support_reference_solution d hd hall

これで現在の hard core が出ます。

さらに raw/default-base では：

lean
noncomputable def D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary
    .of_referenceMatchingSupportNoAll
    (B :
      ∀ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSupportNoAllBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary h where
  supportCompl k :=
    (B k).toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
      ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
        |>.reflectionFixedStarAFixingBoundary_of_raw_action
        |>.toAFixingReflectionFixedNeighborCardBoundary)

RawActionDefaultBaseReferenceSolutionSupportComplBoundary は現在の raw-action reference-side target です。

ReflectionRawActionDefaultBaseF…

5. では ReferenceMatchingAFixingSupportNoAllBoundary はどう証明するのか

ここが本当の数学 gap です。

仮定は：

lean
∀ p ∈ E, p ∈ L.referenceMatchingSolutionSet d hd

自然言語では：

A-fixing reflection の moving support の2点 p, A p の両方について、reference matching equation
M_d q = R_d q が成り立つ。

頂点では：

x := x_p
y := x_{A p}
z := r^d x
w := r^d y

辺は：

x ~ z
y ~ w
x ~ a_0
y ~ a_0
z ~ a_d
w ~ a_d

これは先ほどの 6-cycle 型です。

ここから λ=0, μ=1 だけでは矛盾しません。したがって、Cameron Step 2 の label exchange を使うなら、証明すべき内容は次のように言語化されます。

A-fixing reflection support pair {p, A p} が、offset d の reference matching permutation の fixed pair になることはない。

Lean statement は：

lean
theorem BranchOrbitABCReflectionLabeling.not_all_support_referenceMatchingSolutionSet
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0) :
    ¬ ∀ p : L.data.toAFiberCoordinates.P,
        p ∈ L.aFiberReflectionSupport →
          p ∈ L.referenceMatchingSolutionSet d hd

default-base 版：

lean
theorem D19ActsOnMoore57.not_all_support_referenceMatchingSolutionSet_of_raw_action_defaultBase
    (h : D19ActsOnMoore57 V Γ)
    (k d : ZMod 19) (hd : d ≠ 0) :
    ¬ ∀ p :
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
          .data.toAFiberCoordinates.P,
        p ∈
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            .aFiberReflectionSupport →
        p ∈
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            .referenceMatchingSolutionSet d hd

これが本当に証明すべき theorem です。

6. これは endpoint gap から独立か

ReferenceMatchingAFixingSupportNoAllBoundary 自体は、endpoint gap から独立に statement できます。

ただし、その証明に endpoint-positive target の否定や EndpointReferenceExchangeCommonNeighborBoundary を使ってはいけません。EndpointReferenceExchangeCommonNeighborBoundary は endpoint adjacency を reflected reference adjacency に交換して common-neighbor collision を作るための endpoint-side input であり、reference side に使うと endpoint gap 依存になります。

BranchOrbitABCEndpointExchangeC…

また、ReferenceMatchingPipelineBoundary も使ってはいけません。これは field として ReferenceRotationToMidpointReflectionBoundary を含むので、support-complement から reference-to-midpoint へ進める現在の route では循環します。

BranchOrbitABCReferenceMatching…

したがって、証明は次のどちらかである必要があります。

純 reference-side の label exchange proof
E ⊆ referenceMatchingSolutionSet d hd が D19/coherent-configuration label exchange に反することを直接示す。

combined support-pair theorem に切り替える
reference identity case と endpoint swap case を同時に排除する theorem を作る。

combined theorem は例えば：

lean
structure AFixingSupportPairMatchingAvoidanceBoundary
    (L : BranchOrbitABCReflectionLabeling h) : Prop where
  no_reference_or_endpoint_target_on_support :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : L.data.toAFiberCoordinates.P,
        p ∈ L.aFiberReflectionSupport →
          AFiberCoordinates.matchingEquiv h.isMoore
              L.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd) p ≠
            L.data.toAFiberRotationEquivariance.coordPerm d 0 p ∧
          AFiberCoordinates.matchingEquiv h.isMoore
              L.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd) p ≠
            L.data.toAFiberRotationEquivariance.coordPerm d 0
              (L.aFiberReflectionCoordPerm p)

これは強いですが、証明できれば reference support-complement と endpoint no-positive-target を同時に出せます。

7. Codex が最初に実装すべき 3 theorem
theorem 1: reference solution set の A-invariance
lean
theorem BranchOrbitABCReflectionLabeling.aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P) :
    p ∈ L.referenceMatchingSolutionSet d hd →
      L.aFiberReflectionCoordPerm p ∈ L.referenceMatchingSolutionSet d hd

これは本当に証明できます。endpoint gap も pipeline も不要です。

theorem 2: support pair の明示
lean
theorem BranchOrbitABCReflectionLabeling.aFiberReflectionSupport_eq_pair_of_mem
    (L : BranchOrbitABCReflectionLabeling h)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary L)
    (p : L.data.toAFiberCoordinates.P)
    (hp : p ∈ L.aFiberReflectionSupport) :
    L.aFiberReflectionSupport =
      ({p, L.aFiberReflectionCoordPerm p} :
        Finset L.data.toAFiberCoordinates.P)

これは supportCard.aFiberReflectionSupport_card_two と mem_aFiberReflectionSupport で閉じます。aFiberReflectionSupport.card = 2 は既存です。

BranchOrbitABCAFixingReflection…

theorem 3: no-all-support から support-complement
lean
structure BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSupportNoAllBoundary
    (L : BranchOrbitABCReflectionLabeling h) : Prop where
  not_all_support_reference_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ¬ ∀ p : L.data.toAFiberCoordinates.P,
          p ∈ L.aFiberReflectionSupport →
            p ∈ L.referenceMatchingSolutionSet d hd
lean
noncomputable def BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSupportNoAllBoundary
    .toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    {L : BranchOrbitABCReflectionLabeling h}
    (B : ReferenceMatchingAFixingSupportNoAllBoundary L)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary L) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary L

この3つを入れると、現在の hard core は「pointwise 証明」ではなく「support-pair exclusion 証明」に整理されます。

最終判断

今の全体方向は、Lean engineering としては悪くありません。RawActionDefaultBaseReferenceSolutionSupportComplBoundary を reference side の interface にするのは有効です。

ただし、数学的証明方針として

p ∈ support かつ p ∈ reference solution
から λ/μ common-neighbor collision を直接作る

という狙いは間違っています。そこから出るのは 6-cycle 型で、Moore graph の λ/μ だけでは矛盾しません。

次に証明すべき本物の target は：

lean
ReferenceMatchingAFixingSupportNoAllBoundary

です。

これは endpoint gap から独立に statement できます。ただし、その証明には現在 repo にまだない Cameron Step 2 / coherent-configuration の label exchange 入力が必要です。具体的には、

A-fixing support pair {p, A p} が
reference matching equation M_d q = R_d q の fixed pair になることはない

という幾何命題です。

この証明が出せるなら reference side は閉じます。出せないなら、reference side と endpoint side を完全に分ける設計をやめて、support pair 上の reference identity case と endpoint swap case を同時に排除する combined boundary に戻すべきです。
