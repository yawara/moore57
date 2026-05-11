# ChatGPT response: hard core reference moving-solution exclusion

Date: 2026-05-11
Repository commit read by ChatGPT: f09bac7848cebeac87791b0703f1eec63f3a24bf

## Prompt context

Asked ChatGPT, using GitHub connector, for a non-circular natural-language proof of the hard core reference-side claim: for raw/default-base labeling, a reference matching solution cannot lie in the A-fixing reflection moving support. The prompt explicitly forbade ReferenceMatchingPipelineBoundary, ReferenceRotationToMidpointReflectionBoundary, endpoint gaps, and support-complement-derived routes.

## Response

GitHub connector で commit f09bac7848cebeac87791b0703f1eec63f3a24bf を確認し、次を読みました。

gaps.md 

gaps

Moore57/ReflectionRawActionDefaultBaseFrontier.lean 

ReflectionRawActionDefaultBaseF…

Moore57/BranchOrbitABCReferenceSolutionGeometryBoundary.lean 

BranchOrbitABCReferenceSolution…

Moore57/BranchOrbitABCReferenceSolutionFixedBoundary.lean 

BranchOrbitABCReferenceSolution…

Moore57/BranchOrbitABCReferenceMatchingPipeline.lean 

BranchOrbitABCReferenceMatching…

Moore57/AFiberMatchingSupportEquations.lean 

AFiberMatchingSupportEquations

Moore57/AFiberCoordinates.lean 

AFiberCoordinates

Moore57/BranchOrbitABCAFixingReflectionSupportBoundary.lean 

BranchOrbitABCAFixingReflection…

Moore57/BranchOrbitABCEndpointSignMatchingSymmetry.lean 

BranchOrbitABCEndpointSignMatch…

Moore57/BranchOrbitABCEndpointPairedSymmetryBoundary.lean 

BranchOrbitABCEndpointPairedSym…

Moore57/BranchOrbitABCEndpointExchangeCommonNeighborBoundary.lean 

BranchOrbitABCEndpointExchangeC…

Moore57/AFiberMatchingEquiv.lean は commit f09bac7 で 404 でした。repository 内検索で、matchingEquiv, adj_iff_matchingEquiv_eq, matchingEquiv_eq_of_adj は AFiberMatchingPerm.lean と AFiberMatchingPermAdjacency.lean にあることを確認し、これらを読みました。

Moore57/AFiberMatchingStepBound

 

AFiberMatchingPermAdjacency

 

AFiberMatchingPerm

追加で、aFiberReflectionCoordPerm と reflection coordinate action の定義確認のため BranchOrbitABCReflectionLabeling.lean、endpoint matching adjacency iff の確認のため BranchOrbitABCEndpointSignAdjacencyBoundary.lean、matching inverse/symmetry の確認のため AFiberMatchingPermSymmetry.lean も読みました。

BranchOrbitABCReflectionLabeling

 

BranchOrbitABCEndpointSignAdjac…

 

AFiberMatchingPermSymmetry

結論

現行定義から見る限り、目的の hard core

lean
p ∈ L.referenceMatchingSolutionSet d hd →
p ∉ L.aFiberReflectionSupport

は、endpoint gap と ReferenceMatchingPipelineBoundary から独立に、Cameron Step 2 風 label exchange だけで直ちに出る形にはなっていません。

Step 2 型の「reflection / label exchange」から formal に出るのは、せいぜい次です。

lean
p ∈ referenceMatchingSolutionSet d hd
→
L.aFiberReflectionCoordPerm p ∈
  referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd)

つまり、reference matching solution は A-fixing reflection によって d から -d へ運ばれます。これは対称性であって、p ∈ support と矛盾しません。

hard core を閉じるには、さらに same-target source exchange または cross adjacency 型の追加幾何入力が必要です。この追加入力は endpoint gap とは別に statement できますが、内容としては hard core とほぼ同等の強さです。

A. 頂点配置と、現行定義から出るもの

L := h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k と置きます。以後、一般の labeling : BranchOrbitABCReflectionLabeling h でも同じです。

既存定義に沿って、次の頂点を置きます。

lean
coords := L.data.toAFiberCoordinates
A      := L.aFiberReflectionCoordPerm
R_d    := L.data.toAFiberRotationEquivariance.coordPerm d 0
M_d    := AFiberCoordinates.matchingEquiv h.isMoore coords 0 (0 + d)
            (index_ne_add_of_ne_zero hd)

x      := L.referenceFiberVertex p
       = ((coords.coord 0 p : _) : V)

y      := L.referenceFiberVertex (A p)
       = ((coords.coord 0 (A p) : _) : V)

z      := ((coords.coord (0 + d) (R_d p) : _) : V)
       = h.rotation d x

θ      := h.smul (DihedralGroup.sr L.aFixingReflectionIndex)

referenceMatchingSolutionSet は M_d p = R_d p の finset form です。これは既に mem_referenceMatchingSolutionSet としてあります。

BranchOrbitABCReferenceSolution…


matchingEquiv は distinct A-fibers 間の perfect matching で、adj_iff_matchingEquiv_eq により matching equation は adjacency に変換できます。

AFiberMatchingPerm

したがって

lean
p ∈ L.referenceMatchingSolutionSet d hd

から得られるグラフ事実は

lean
Γ.Adj x z

です。自然言語では、reference vertex x = r_p がその d-rotation target r^d x に隣接する、ということです。

一方、

lean
p ∈ L.aFiberReflectionSupport

は既存 simp lemma により

lean
A p ≠ p

です。aFiberReflectionCoordPerm は A-fixing reflection が reference fiber coordinate に誘導する permutation であり、coord_aFiberReflectionCoordPerm_apply_val により

lean
y = θ x

です。

BranchOrbitABCReflectionLabeling

ここまでで分かるのは：

lean
x ≠ y
Γ.Adj x (coords.a 0)
Γ.Adj y (coords.a 0)

です。したがって x と y は同じ common neighbor coords.a 0 を持ちます。Moore graph の λ = 0 により x と y は非隣接です。

ただし、これは矛盾ではありません。μ = 1 を使うには、x,y の 第二の common neighbor が必要です。

reflection で Γ.Adj x z を移すと、

lean
Γ.Adj (θ x) (θ z)

すなわち

lean
Γ.Adj y z'

が出ます。ここで

lean
z' := θ z
    = h.rotation (-d) y
    = ((coords.coord (0 + (-d))
          (L.data.toAFiberRotationEquivariance.coordPerm (-d) 0 (A p)) : _) : V)

です。これは coordinate statement では

lean
A p ∈ L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd)

になります。

しかし、これは x,y の common neighbor を作りません。得られる辺は

lean
x ~ z
y ~ z'

だけです。z が y に隣接する、または z' が x に隣接する、または z = z' という情報は、現行の raw/default-base/reflection action からは出ていません。

実際、z と z' は一般には別 fiber にいます。z は offset d 側、z' は offset -d 側です。d ≠ 0 なら d ≠ -d in ZMod 19 なので、coordinate-fiber distinctness の方向から同一視は期待できません。

B. λ=0 / μ=1 を使う場合に必要な exact collision

λ = 0 と μ = 1 で hard core を閉じるには、次のような追加辺が必要です。

Option 1: y ~ z を追加する

追加仮定：

lean
Γ.Adj
  (L.referenceFiberVertex (L.aFiberReflectionCoordPerm p))
  (((coords.coord (0 + d)
      (L.data.toAFiberRotationEquivariance.coordPerm d 0 p) : _) : V))

matching equation では：

lean
M_d (A p) = R_d p

このとき、x,y は

lean
coords.a 0

と

lean
z = coord (0+d) (R_d p)

の2つを common neighbor に持ちます。

x ~ coords.a 0, y ~ coords.a 0: reference fiber の定義から出る。

x ~ z: reference matching equation M_d p = R_d p から出る。

y ~ z: 追加 cross adjacency から出る。

x ≠ y: p ∈ support, coordinate injectivity.

z ≠ coords.a 0: z は branch fiber over a_d の vertex、coords.a 0 は center-neighbor branch vertex。Lean では別途小補題にするのが安全。

この場合、μ = 1 により common neighbor は一意なので

lean
z = coords.a 0

となり、fiber/branch separation と矛盾します。

しかし、この Option 1 の追加仮定は matching-equation だけでもすでに強いです。なぜなら

lean
M_d p = R_d p
M_d (A p) = R_d p

から M_d.injective で

lean
A p = p

となり、p ∈ aFiberReflectionSupport と即矛盾します。つまり μ = 1 すら不要です。

Option 2: x ~ z' を追加する

追加仮定：

lean
Γ.Adj
  (L.referenceFiberVertex p)
  (((coords.coord (0 + (-d))
      (L.data.toAFiberRotationEquivariance.coordPerm (-d) 0 (A p)) : _) : V))

matching equation では：

lean
M_{-d} p = R_{-d} (A p)

この場合、x,y は

lean
coords.a 0

と

lean
z' = coord (0+(-d)) (R_{-d} (A p))

の2つの common neighbor を持ちます。

y ~ z': reflected reference solution から出る。

x ~ z': 追加 cross adjacency。

x,y は coords.a 0 を共有。

x ≠ y は support から。

これも μ = 1 で閉じられます。matching equation だけで閉じるなら、M_{-d} (A p) = R_{-d} (A p) と M_{-d} p = R_{-d} (A p) から A p = p です。

現行定義から自動で出るのは Option 1/2 ではない

現行の A-fixing reflection から出るのは

lean
p ∈ Sol_d → A p ∈ Sol_{-d}

です。これは

lean
M_d p = R_d p
→
M_{-d} (A p) = R_{-d} (A p)

であり、Option 1/2 の cross equation ではありません。

endpoint 側では corrected paired statement が既にこの問題を明示しています。paired symmetry は target R (A p) を返し、旧 target R p に戻すには別の same-target equality が必要だ、と EndpointSignPairedAdjacencyBoundary 側で分離されています。

BranchOrbitABCEndpointPairedSym…


reference 側でも同じ構造です。reflection は sign/offset を変えるだけで、同じ target に source を交換するわけではありません。

C. 循環性チェック

禁止条件に照らすと、次は使えません。

1. ReferenceMatchingPipelineBoundary

ReferenceMatchingPipelineBoundary は field として

lean
referenceToMidpoint : ReferenceRotationToMidpointReflectionBoundary labeling

を含みます。

BranchOrbitABCReferenceMatching…


hard core は ReferenceRotationToMidpointReflectionBoundary への upstream target なので、これを前提にすると循環です。

2. ReferenceRotationToMidpointReflectionBoundary

ReferenceRotationMatchingSolutionAFixingSupportComplBoundary から既に

lean
toReferenceRotationToMidpointReflectionBoundary

が出ます。

BranchOrbitABCReferenceSolution…


逆に ReferenceRotationToMidpointReflectionBoundary を使って support-complement を出すと、明確に循環します。

3. endpoint pointwise / endpoint exchange

EndpointReferenceExchangeCommonNeighborBoundary は endpoint adjacency を reflected reference adjacency に交換し、Moore common-neighbor collision で endpoint pointwise nonadjacency を出すための boundary です。

BranchOrbitABCEndpointExchangeC…


これを reference support-complement の証明に使うと、reference side が endpoint gap に依存します。

また、EndpointSignNoReflectedReferenceNegMatchingBoundary や EndpointMatchingAFixingNoPositiveTargetBoundary も endpoint-positive/negative target matching を消す diagnostic です。EndpointSignMatchingSymmetry.lean では pointwise endpoint nonadjacency から no-reflected-reference negative matching が出る route も明示されています。

BranchOrbitABCEndpointSignMatch…


これも endpoint gap 依存です。

4. support-complement 自身から作った referenceToMidpoint

RawActionDefaultBaseReferenceSolutionSupportComplBoundary には既に toReferenceRotationToMidpointReflectionBoundary があり、final no-go alias もこの route を使っています。

ReflectionRawActionDefaultBaseF…

 

Add reference support-complemen…


これを hard core 証明の中で戻して使うのは循環です。

D. 直接出ない場合の最小 missing lemma 分解

現行定義から非循環に証明できそうなものと、本質 gap を分けると、次の 4 つです。

1. まず実装可能: reference solution の adjacency 版
lean
theorem BranchOrbitABCReflectionLabeling.mem_referenceMatchingSolutionSet_iff_reference_adj_rotation
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P) :
    p ∈ L.referenceMatchingSolutionSet d hd ↔
      Γ.Adj
        (L.referenceFiberVertex p)
        (((L.data.toAFiberCoordinates.coord (0 + d)
            (L.data.toAFiberRotationEquivariance.coordPerm d 0 p) : _) : V))

より強く、rotation vertex を使うなら：

lean
theorem BranchOrbitABCReflectionLabeling.mem_referenceMatchingSolutionSet_iff_adj_rotation
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P) :
    p ∈ L.referenceMatchingSolutionSet d hd ↔
      Γ.Adj (L.referenceFiberVertex p)
        (h.rotation d (L.referenceFiberVertex p))

これは mem_referenceMatchingSolutionSet, AFiberCoordinates.adj_iff_matchingEquiv_eq, rotation equivariance から証明する pure wrapper です。matchingEquiv と adjacency iff は AFiberMatchingPerm.lean にあります。

BranchOrbitABCReferenceSolution…

 

AFiberMatchingPerm

2. まず実装可能: A-fixing reflection による negative-offset transport
lean
theorem BranchOrbitABCReflectionLabeling.aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet_neg
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P) :
    p ∈ L.referenceMatchingSolutionSet d hd →
      L.aFiberReflectionCoordPerm p ∈
        L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd)

自然言語証明：

p ∈ Sol_d
⇔ r_p ~ r^d r_p
apply θ
⇒ θ r_p ~ θ(r^d r_p)
⇒ r_{A p} ~ r^{-d} r_{A p}
⇔ A p ∈ Sol_{-d}.

これは endpoint gap に依存しません。aFiberReflectionCoordPerm は A-fixing reflection が reference fiber に誘導する coordinate permutation で、coord_aFiberReflectionCoordPerm_apply_val が vertex-level equality を与えます。

BranchOrbitABCReflectionLabeling

ただし、これは hard core ではありません。support 上の 2-cycle solution pair を作るだけです。

3. 本質 missing lemma: same-target source exchange

これは hard core を閉じる最小の label-exchange 入力です。

lean
structure ReferenceMatchingAFixingSourceExchangeBoundary
    (L : BranchOrbitABCReflectionLabeling h) : Prop where
  source_exchange :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : L.data.toAFiberCoordinates.P,
        p ∈ L.aFiberReflectionSupport →
          AFiberCoordinates.matchingEquiv h.isMoore
              L.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd) p =
            L.data.toAFiberRotationEquivariance.coordPerm d 0 p →
          AFiberCoordinates.matchingEquiv h.isMoore
              L.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd)
              (L.aFiberReflectionCoordPerm p) =
            L.data.toAFiberRotationEquivariance.coordPerm d 0 p

この boundary があれば、証明は purely label-equation です。

lean
have hp  : M_d p = R_d p := ...
have hAp : M_d (A p) = R_d p :=
  source_exchange d hd p hpSupport hp
have hsame : M_d (A p) = M_d p := hAp.trans hp.symm
have hAeq : A p = p := M_d.injective hsame
exact (L.mem_aFiberReflectionSupport p).1 hpSupport hAeq

これは λ/μ 不要です。

ただし、この source_exchange は reflection からは出ません。reflection から出るのは d ↦ -d transport であり、same target R_d p を保つ source exchange ではありません。

4. graph 版 missing lemma: cross adjacency

上の source exchange の adjacency 版です。

lean
structure ReferenceMatchingAFixingCrossAdjacencyBoundary
    (L : BranchOrbitABCReflectionLabeling h) : Prop where
  cross_adj_of_reference_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : L.data.toAFiberCoordinates.P,
        p ∈ L.aFiberReflectionSupport →
          p ∈ L.referenceMatchingSolutionSet d hd →
          Γ.Adj
            (L.referenceFiberVertex (L.aFiberReflectionCoordPerm p))
            (((L.data.toAFiberCoordinates.coord (0 + d)
                (L.data.toAFiberRotationEquivariance.coordPerm d 0 p) : _) : V))

これがあれば μ = 1 で閉じることも、matching injectivity で閉じることもできます。matching injectivity の方が Lean では短いです。

5. paired-solution exclusion

reflection transport を使った後の obstruction として書くなら：

lean
structure ReferenceMatchingAFixingNoPairedSolutionBoundary
    (L : BranchOrbitABCReflectionLabeling h) : Prop where
  no_paired_reference_solution :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : L.data.toAFiberCoordinates.P,
        p ∈ L.aFiberReflectionSupport →
          ¬
            (p ∈ L.referenceMatchingSolutionSet d hd ∧
             L.aFiberReflectionCoordPerm p ∈
               L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd))

reflection transport により second conjunct は first conjunct から自動で出るので、これは hard core と同等です。ただし Cameron Step 2 風には、この form が一番近いかもしれません。「A-moving pair が d/-d reference-solution pair になることはない」という obstruction です。

E. Codex が最初に実装すべき 3 theorem
1. reference solution を adjacency に変換する lemma
lean
theorem BranchOrbitABCReflectionLabeling.mem_referenceMatchingSolutionSet_iff_reference_adj_rotationTarget
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P) :
    p ∈ L.referenceMatchingSolutionSet d hd ↔
      Γ.Adj
        (L.referenceFiberVertex p)
        (((L.data.toAFiberCoordinates.coord (0 + d)
            (L.data.toAFiberRotationEquivariance.coordPerm d 0 p) : _) : V))

これは以後の natural-language proof と Lean proof の接続点です。AFiberCoordinates.adj_iff_matchingEquiv_eq と mem_referenceMatchingSolutionSet だけで進みます。

2. A-fixing reflection transport for reference solutions
lean
theorem BranchOrbitABCReflectionLabeling.aFiberReflectionCoordPerm_mem_referenceMatchingSolutionSet_neg
    (L : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : L.data.toAFiberCoordinates.P) :
    p ∈ L.referenceMatchingSolutionSet d hd →
      L.aFiberReflectionCoordPerm p ∈
        L.referenceMatchingSolutionSet (-d) (neg_ne_zero.mpr hd)

これは非循環で、現行定義から出るはずです。ただし hard core はまだ閉じません。この theorem を入れることで、「現行 reflection label exchange から出る正確な到達点」が Lean 上で明示されます。

3. source exchange boundary から support-complement への formal closure
lean
structure BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSourceExchangeBoundary
    (L : BranchOrbitABCReflectionLabeling h) : Prop where
  source_exchange :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : L.data.toAFiberCoordinates.P,
        p ∈ L.aFiberReflectionSupport →
          AFiberCoordinates.matchingEquiv h.isMoore
              L.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd) p =
            L.data.toAFiberRotationEquivariance.coordPerm d 0 p →
          AFiberCoordinates.matchingEquiv h.isMoore
              L.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd)
              (L.aFiberReflectionCoordPerm p) =
            L.data.toAFiberRotationEquivariance.coordPerm d 0 p

formal connector:

lean
noncomputable def BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSourceExchangeBoundary
    .toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
    {L : BranchOrbitABCReflectionLabeling h}
    (B : ReferenceMatchingAFixingSourceExchangeBoundary L) :
    ReferenceRotationMatchingSolutionAFixingSupportComplBoundary L where
  reference_matching_solution_subset_aFiberReflectionSupport_compl := by
    intro d hd p hpSol
    rw [Finset.mem_compl]
    intro hpSupport
    have hpMatch :
        AFiberCoordinates.matchingEquiv h.isMoore
            L.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          L.data.toAFiberRotationEquivariance.coordPerm d 0 p :=
      (L.mem_referenceMatchingSolutionSet d hd p).1 hpSol
    have hApMatch :
        AFiberCoordinates.matchingEquiv h.isMoore
            L.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd)
            (L.aFiberReflectionCoordPerm p) =
          L.data.toAFiberRotationEquivariance.coordPerm d 0 p :=
      B.source_exchange d hd p hpSupport hpMatch
    have hsame :
        AFiberCoordinates.matchingEquiv h.isMoore
            L.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd)
            (L.aFiberReflectionCoordPerm p) =
          AFiberCoordinates.matchingEquiv h.isMoore
            L.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p :=
      hApMatch.trans hpMatch.symm
    have hfixed : L.aFiberReflectionCoordPerm p = p :=
      (AFiberCoordinates.matchingEquiv h.isMoore
        L.data.toAFiberCoordinates 0 (0 + d)
        (index_ne_add_of_ne_zero hd)).injective hsame
    exact (L.mem_aFiberReflectionSupport p).1 hpSupport hfixed

その後、raw/default-base wrapper は：

lean
noncomputable def D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary
    .of_referenceMatchingAFixingSourceExchange
    (B :
      ∀ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceMatchingAFixingSourceExchangeBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary h where
  supportCompl k :=
    (B k).toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
最終判定

この proof は、現状のままでは endpoint gap から独立には閉じていません。

依存しないで実装できる部分は：

lean
reference solution equation ↔ reference adjacency
reference solution at d transports to A p solution at -d
source-exchange boundary ⇒ support-complement

です。

本質的に足りないのは：

lean
M_d p = R_d p かつ p ∈ A-support
から
M_d (A p) = R_d p

または同等の cross adjacency / paired-solution exclusion です。

これは ReferenceMatchingPipelineBoundary, ReferenceRotationToMidpointReflectionBoundary, endpoint pointwise nonadjacency, EndpointReferenceExchangeCommonNeighborBoundary のいずれからも借りずに証明する必要があります。現行 repo の定義と theorem だけからは、reflection は d を -d に送る対称性までしか与えていないため、same-target source exchange はまだ独立の missing lemma です。
