# `EndpointMatchingAFixingTargetSignBoundary` について

## 結論

`EndpointMatchingAFixingTargetSignBoundary labeling` の missing statement

```lean
M_d p = R_d (θ p) →
coord (-d) (R_{-d} p) = coord d (R_d p)
```

は、非循環に証明できないというより、局所幾何的には **偽** です。

ここで

```lean
θ := labeling.aFiberReflectionCoordPerm
R_d := labeling.data.toAFiberRotationEquivariance.coordPerm d 0
M_d := AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates 0 (0 + d)
          (index_ne_add_of_ne_zero hd)
```

とします。

座標を展開すると、目標等式は

\[
  r^{-d} x_p = r^d x_p
\]

を主張しています。ただし

\[
  x_p := \operatorname{coord}(0,p).
\]

しかし `d ≠ 0` なら `d ≠ -d` in `ZMod 19` なので、左辺は A-branch fiber `L_{-d}`、右辺は A-branch fiber `L_d` に属します。これらの branch fiber は disjoint です。したがって、求められている等式は premise

```lean
M_d p = R_d (θ p)
```

とは無関係に成立しません。

従って、ここで使うべき Moore graph uniqueness fact は「等式を証明するもの」ではなく、むしろ次の否定方向の事実です。

> `coords.a (0 + d)` と `coords.a (0 + (-d))` は異なる center-neighbors であり、もし同じ endpoint vertex が両方の branch fiber に入れば、`coords.u` とその endpoint vertex がこの 2 点の 2 つの common neighbors になる。これは Moore graph の unique common neighbor / no 4-cycle に反する。

Lean では、この事実は通常

```lean
h.isMoore.not_adj_other_branch_of_mem_branchFiber
```

で使うのが最短です。

---

## 1. 目標等式の座標展開

以下の notation を使います。

```lean
let coords := labeling.data.toAFiberCoordinates
let R := labeling.data.toAFiberRotationEquivariance.coordPerm
let θ := labeling.aFiberReflectionCoordPerm
```

定義上、

```lean
((coords.coord (0 + (-d)) (R (-d) 0 p)) : V)
```

は

\[
  r^{-d}x_p
\]

であり、

```lean
((coords.coord (0 + d) (R d 0 p)) : V)
```

は

\[
  r^{d}x_p
\]

です。

これは次の既存 API から直接出ます。

```lean
AFiberRotationEquivariance.coord_coordPerm_apply_val
```

Lean-ready lemma は次の形です。

```lean
theorem endpointTargetNeg_eq_rotation_neg
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19)
    (p : labeling.data.toAFiberCoordinates.P) :
    (((labeling.data.toAFiberCoordinates.coord (0 + (-d))
        (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a (0 + (-d)))}) : V)) =
      h.rotation (-d)
        (((labeling.data.toAFiberCoordinates.coord 0 p :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a 0)}) : V)) := by
  simpa using
    AFiberRotationEquivariance.coord_coordPerm_apply_val
      (rot := labeling.data.toAFiberRotationEquivariance)
      (d := -d) (i := 0) (p := p)
```

同様に、

```lean
theorem endpointTargetPos_eq_rotation_pos
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19)
    (p : labeling.data.toAFiberCoordinates.P) :
    (((labeling.data.toAFiberCoordinates.coord (0 + d)
        (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a (0 + d))}) : V)) =
      h.rotation d
        (((labeling.data.toAFiberCoordinates.coord 0 p :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a 0)}) : V)) := by
  simpa using
    AFiberRotationEquivariance.coord_coordPerm_apply_val
      (rot := labeling.data.toAFiberRotationEquivariance)
      (d := d) (i := 0) (p := p)
```

従って、missing statement は

```lean
h.rotation (-d) x = h.rotation d x
```

すなわち

```lean
h.rotation (d + d) x = x
```

に等価です。これは branch fiber vertex では `d ≠ 0` のもとで不可能です。

---

## 2. 実際に証明できるのは等式ではなく不等式

`d ≠ 0` のとき、次が証明できます。

```lean
theorem endpointTargetNeg_ne_endpointTargetPos
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    (((labeling.data.toAFiberCoordinates.coord (0 + (-d))
        (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a (0 + (-d)))}) : V)) ≠
    (((labeling.data.toAFiberCoordinates.coord (0 + d)
        (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
      {x : V // x ∈
        branchFiber Γ labeling.data.toAFiberCoordinates.u
          (labeling.data.toAFiberCoordinates.a (0 + d))}) : V)) := by
  intro heq
  let coords := labeling.data.toAFiberCoordinates

  have hidx : (0 + d : ZMod 19) ≠ 0 + (-d) := by
    simpa using ne_neg_self_zmod19 hd

  have hpos_mem :
      (((coords.coord (0 + d)
          (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) ∈
        branchFiber Γ coords.u (coords.a (0 + d)) := by
    exact coords.coord_mem (0 + d)
      (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p)

  have hneg_mem :
      (((coords.coord (0 + (-d))
          (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (-d)))}) : V)) ∈
        branchFiber Γ coords.u (coords.a (0 + (-d))) := by
    exact coords.coord_mem (0 + (-d))
      (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p)

  have hneg_adj :
      Γ.Adj
        (((coords.coord (0 + d)
            (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V))
        (coords.a (0 + (-d))) := by
    have hraw :
        Γ.Adj
          (coords.a (0 + (-d)))
          (((coords.coord (0 + (-d))
              (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (-d)))}) : V)) :=
      (mem_branchFiber.mp hneg_mem).2
    simpa [heq] using hraw.symm

  have hnot :
      ¬ Γ.Adj
        (((coords.coord (0 + d)
            (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V))
        (coords.a (0 + (-d))) :=
    h.isMoore.not_adj_other_branch_of_mem_branchFiber
      (coords.hub (0 + d))
      (coords.hub (0 + (-d)))
      (coords.a_ne hidx)
      hpos_mem

  exact hnot hneg_adj
```

この lemma は premise

```lean
M_d p = R_d (θ p)
```

を一切使いません。つまり、missing statement の consequent は、`d ≠ 0` のもとで常に false です。

したがって `EndpointMatchingAFixingTargetSignBoundary` をこの形で証明するには、各 `d p` について antecedent

```lean
M_d p = R_d (θ p)
```

が impossible であることを証明するしかありません。しかしこれは現在の local graph geometry からは出ませんし、matching equation として自然に起こり得る形です。

---

## 3. どの uniqueness fact が使われるか

等式を証明する uniqueness fact はありません。

使える Moore graph fact は、等式を否定する次のものです。

### center-neighbor pair

比較すべき center-neighbor pair は

```lean
coords.a (0 + d)
coords.a (0 + (-d))
```

です。

`d ≠ 0` なので

```lean
(0 + d : ZMod 19) ≠ 0 + (-d)
```

が成り立ちます。Lean では

```lean
ne_neg_self_zmod19 hd
```

を使います。

### common neighbors

もし

```lean
coord (-d) (R_{-d} p) = coord d (R_d p)
```

なら、その共通値を `y` として、

```lean
Γ.Adj (coords.a (0 + d)) y
Γ.Adj (coords.a (0 + (-d))) y
```

が成り立ちます。

一方で、常に

```lean
Γ.Adj (coords.a (0 + d)) coords.u
Γ.Adj (coords.a (0 + (-d))) coords.u
```

も成り立ちます。

したがって `coords.a (0 + d)` と `coords.a (0 + (-d))` は、`coords.u` と `y` という 2 つの common neighbors を持つことになります。これは Moore graph の unique common neighbor / no 4-cycle に反します。

Lean ではこの argument は直接

```lean
h.isMoore.not_adj_other_branch_of_mem_branchFiber
```

として使うのが最短です。

---

## 4. 正しく非循環に証明できる statement

反射で本当に得られるのは same-sign target ではなく negative-sign target です。

つまり、premise

```lean
M_d p = R_d (θ p)
```

から非循環に証明できるのは

```lean
M_{-d} (θ p) = R_{-d} p
```

です。

これは完全に D19 equivariance と matching uniqueness だけで証明できます。

### Lean-ready local lemma

```lean
private theorem neg_ne_zero_of_ne_zero_zmod19
    {d : ZMod 19} (hd : d ≠ 0) : -d ≠ 0 := by
  exact neg_ne_zero.mpr hd

theorem endpointMatchingAFixing_negative_offset
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (hp :
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates 0 (0 + d)
          (index_ne_add_of_ne_zero hd) p =
        labeling.data.toAFiberRotationEquivariance.coordPerm d 0
          (labeling.aFiberReflectionCoordPerm p)) :
    AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + (-d))
        (index_ne_add_of_ne_zero (neg_ne_zero_of_ne_zero_zmod19 hd))
        (labeling.aFiberReflectionCoordPerm p) =
      labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p := by
  let coords := labeling.data.toAFiberCoordinates
  let target :=
    labeling.data.toAFiberRotationEquivariance.coordPerm d 0
      (labeling.aFiberReflectionCoordPerm p)

  have hadj :
      Γ.Adj
        (((coords.coord 0 p :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
        (((coords.coord (0 + d) target :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) :=
    (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore
      coords (index_ne_add_of_ne_zero hd) p target).2 hp

  have hadj_reflected :
      Γ.Adj
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)))
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord (0 + d) target :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V))) :=
    (h.smul_adj (DihedralGroup.sr labeling.aFixingReflectionIndex)
      (((coords.coord 0 p :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
      (((coords.coord (0 + d) target :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V))).mp
      hadj

  have hsource :
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) =
        (((coords.coord 0 (labeling.aFiberReflectionCoordPerm p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)) := by
    simpa [coords] using
      (labeling.coord_aFiberReflectionCoordPerm_apply_val p).symm

  have htarget :
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((coords.coord (0 + d) target :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) =
        (((coords.coord (0 + (-d))
            (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + (-d)))}) : V)) := by
    simpa [coords, target] using
      labeling.aFiberReflection_rotationCoordPerm_aFiberReflectionCoordPerm_vertex_eq
        d p

  rw [hsource, htarget] at hadj_reflected

  exact
    AFiberCoordinates.matchingEquiv_eq_of_adj h.isMoore
      coords
      (index_ne_add_of_ne_zero (neg_ne_zero_of_ne_zero_zmod19 hd))
      (by
        simpa [coords] using hadj_reflected)
```

この lemma が、反射計算から直接得られる正しい coordinate statement です。

---

## 5. 修正案

現在の

```lean
EndpointMatchingAFixingTargetSignBoundary
```

は same-sign vertex equality を要求しているため、局所的には不適切です。

置き換えるなら、次のような boundary が自然です。

```lean
structure EndpointMatchingAFixingNegativeOffsetBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_matching_eq_rotation_neg :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p) →
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + (-d))
            (index_ne_add_of_ne_zero (neg_ne_zero_of_ne_zero_zmod19 hd))
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p
```

この boundary は非循環に証明できます。

一方、same-sign の

```lean
M_d (θ p) = R_d p
```

を得たいなら、反射だけでは足りません。必要なのは sign を戻す追加仮定です。ただし、それは

```lean
coord (-d) (R_{-d} p) = coord d (R_d p)
```

ではありません。この等式は false です。

same-sign を得るには、例えば

```lean
M_{-d} (θ p) = R_{-d} p → M_d (θ p) = R_d p
```

のような、matching equation 自体の `d ↔ -d` 変換を別途仮定する必要があります。しかしこれは Moore graph の基本的な uniqueness からは出ません。

---

## 6. Codex への短い指示

`EndpointMatchingAFixingTargetSignBoundary` を証明しようとしない方がよいです。

missing equality

```lean
coord (-d) (R_{-d} p) = coord d (R_d p)
```

は、`d ≠ 0` では branch-fiber disjointness により否定されます。

使うべき局所 lemma は equality ではなく、次です。

```lean
M_d p = R_d (θ p) → M_{-d} (θ p) = R_{-d} p
```

これは次の 5 ステップで非循環に証明できます。

1. `AFiberCoordinates.adj_iff_matchingEquiv_eq` で premise を adjacency に変換する。
2. `h.smul_adj` で A-fixing reflection を作用させる。
3. source は `coord_aFiberReflectionCoordPerm_apply_val` で `coord 0 (θ p)` に書き換える。
4. target は `aFiberReflection_rotationCoordPerm_aFiberReflectionCoordPerm_vertex_eq` で `coord (-d, R_{-d} p)` に書き換える。
5. `AFiberCoordinates.matchingEquiv_eq_of_adj` で negative-offset matching equality に戻す。

この経路は `ReferenceRotationMatchingSolutionVertexFixedBoundary`、`ReferenceRotationToMidpointReflectionBoundary.of_aFixingFixed`、および `θ p = p` を先に証明する任意の循環ステップを使いません。
