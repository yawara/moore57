# ChatGPT Browser Response: endpoint common-neighbor direction

Date: 2026-05-11

Prompt sent from the in-app browser:

```text
Moore57 の Lean 形式化について相談です。現状、raw D19 action から fixed-star / K155 / support-card 系はかなり Lean で供給済みです。残りの主戦場は次の2種類の境界です。

1. ReferenceRotationToMidpointReflectionBoundary
2. MidpointExceptionEndpointAdjCommonNeighborBasicBoundary または EndpointSignNoReflectedReferenceNegMatchingBoundary

Cameron Ch.3 Step 2 風の label exchange / endpoint common-neighbor argument から、どちらを先に証明すべきかを判断したいです。抽象的な方針ではなく、Lean lemma に落ちる最小主張として、使う頂点、必要な隣接/非隣接条件、SRG(3250,57,0,1) の lambda=0, mu=1 をどこで使うか、矛盾の閉じ方を具体的に提案してください。
```

## Extracted Conclusion

Do not first attack `ReferenceRotationToMidpointReflectionBoundary` directly.
The recommended first target is the endpoint side, especially an
endpoint-common-neighbor lemma feeding
`MidpointExceptionEndpointAdjCommonNeighborBasicBoundary` or
`EndpointSignNoReflectedReferenceNegMatchingBoundary`.

The SRG core should be isolated from D19-specific label exchange data:

1. `lambda = 0`: if `x` and `y` have a common neighbor `m`, then `x` and `y`
   are not adjacent.
2. `mu = 1`: if distinct `x` and `y` have common neighbors `m` and `r`, then
   `m = r`.
3. A contradiction follows when the project-specific labels force those two
   common neighbors to be distinct, or when an assumed edge between them
   rewrites to a loop after `m = r`.

## Suggested Core Shape

Use a tiny common-neighbor predicate conceptually:

```lean
def CN (G : SimpleGraph V) (x y z : V) : Prop :=
  G.Adj x z ∧ G.Adj y z
```

Useful core lemmas:

```lean
-- lambda = 0 only
lemma endpoint_not_adj_of_common_neighbor
    {x y m : V} (hm : CN G x y m) :
    ¬ G.Adj x y

-- lambda = 0 gives non-adjacency; mu = 1 gives equality
lemma common_neighbor_eq_of_two_common_neighbors
    {x y m r : V}
    (hxy_ne : x ≠ y)
    (hm : CN G x y m)
    (hr : CN G x y r) :
    r = m

lemma two_common_neighbors_collision
    {x y m r : V}
    (hxy_ne : x ≠ y)
    (hm : CN G x y m)
    (hr : CN G x y r)
    (hne : r ≠ m) :
    False
```

The endpoint boundary should supply the concrete vertices:

```text
e0 e1 : endpoint pair
mid   : midpoint-reflection common neighbor
ref   : reference/reflected-reference common neighbor
```

Then `EndpointSignNoReflectedReferenceNegMatchingBoundary` should amount to:

```text
mid and ref are both common neighbors of e0,e1.
mu = 1 forces ref = mid.
The sign/no-negative-matching condition forbids this equality.
```

For `ReferenceRotationToMidpointReflectionBoundary`, do the same after the
endpoint exchange witness has been built:

```text
midRef and refRot are both common neighbors of the same endpoint pair.
mu = 1 forces refRot = midRef.
An assumed edge between them rewrites to a loop, giving contradiction.
```

## Implementation Order

1. Add/name the SRG core lemmas.
2. Use them to build the endpoint common-neighbor/no-negative-matching core.
3. Treat `ReferenceRotationToMidpointReflectionBoundary` as a wrapper once the
   endpoint exchange witness exists.

This matches the current Lean direction: the endpoint forms should be collapsed
to one geometric input first, then the reference comparison can be routed
through that endpoint exchange data.
