# Moore57 D19 Lean Gaps

Snapshot: 2026-05-10, after adding fixed-star paper-boundary connectors and
fixed-induced-graph inheritance wrappers.

This note records the current Lean gaps in difficulty order.  The final goal is
to prove, with no extra assumptions and depending only on mathlib, that no
`D19` action on a Moore graph of degree `57` exists.

## Gap List By Difficulty

### 1. Hardest: prove `h7` and `hMinus8` from the raw action

Many no-go routes currently consume the following character identities as
inputs:

- `h7`: the `E7Matrix` trace agrees with a `d19LinearCharacter`.
- `hMinus8`: the complementary minus-8 trace also agrees with a
  `d19LinearCharacter`.

The remaining work is to derive these from the raw `D19ActsOnMoore57` action,
using mathlib representation theory as much as possible and avoiding a custom
representation-theory reimplementation.

### 2. Hardest geometry: construct `InvolutionK155` from a reflection

The K155 no-go surfaces currently assume

```lean
InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))
```

Once this is available, Lean can convert it to the fixed-star reflection-count
input used downstream.  The first constructive bridge is now present:

```lean
D19ActsOnMoore57.involutionK155OfReflectionFixedNeighborCenterCount
```

This proves that a reflection fixed vertex with exactly `55` fixed neighbors,
together with the total reflection fixed count `56`, determines an explicit
`InvolutionK155`.  The remaining hard part is therefore sharper:

- construct a reflection fixed center with `55` fixed neighbors from the raw
  action, preferably as `ReflectionFixedNeighborStarCenterData`, or construct
  an induced fixed-graph degree-`55` center as
  `ReflectionFixedInducedStarCenterData`;
- derive or route the exact reflection fixed count `56`;
- prove the selected center is not `rotationFixedCenter` when routing onward to
  `ReflectionFixedCenterLeafBoundary`;
- keep in mind that existing fixed-star/count boundaries are Prop-valued, so
  they yield `Nonempty (InvolutionK155 ...)`, not reusable Type-valued witness
  data.

The paper-shaped statement "the fixed set of an involution is a star with
`56` vertices" is now represented by:

```lean
InvolutionFixedSetStar56
InvolutionFixedSetStar56.fixedVertexCount_eq_56
InvolutionFixedSetStar56.adjacentMovedCount_eq_112
InvolutionFixedSetStar56.nonempty_involutionK155
D19ActsOnMoore57.D19LinearCharacterInput.ofLinearCharacterAndPaperFixedStar56
D19ActsOnMoore57.D19RepresentationCharacterInput.ofLinearCharacterAndPaperFixedStar56
D19FinalCharacterInputs.ofLinearCharacterAndPaperFixedStar56
```

This matches the Makhnev-Paduchikh/Higman formulation more directly than the
constructive center-count records.  It is still a boundary: the proof that a
raw reflection satisfies `InvolutionFixedSetStar56` is the Higman/Cameron
fixed-star theorem and remains to be formalized.

The fixed-induced-graph inheritance part of the paper's Lemma 1(2) is now
available in both non-regular and regularity-parameterized forms:

```lean
D19ActsOnMoore57.fixedInducedGraph_isStrongZeroOne
D19ActsOnMoore57.fixedInducedGraph_isSRGWith_of_regular
not_isSRGWith_56_k_0_1
D19ActsOnMoore57.fixedInducedGraph_not_regular_of_fixedVertexCount_eq_56
D19ActsOnMoore57.reflectionFixedInducedStarDegrees_of_reflectionFixedSetStar56
D19ActsOnMoore57.reflectionFixedStarBoundary_of_reflectionFixedSetStar56
```

The first theorem records the paper-level common-neighbor condition directly:
adjacent fixed vertices have `0` common fixed neighbors, and distinct
non-adjacent fixed vertices have `1`.  The second packages the same inheritance
into mathlib's `IsSRGWith` API once constant degree is available.  The
`IsSRGWith.param_eq` arithmetic now rules out a regular `56`-vertex
`(λ, μ) = (0, 1)` fixed induced graph, so the remaining classification work is
the genuinely non-regular fixed-star step: prove that the fixed induced graph
has a degree-`55` center and all other fixed vertices are leaves.

If the paper-shaped fixed-star theorem is available for every reflection, and
one separately knows that `rotationFixedCenter` is not the paper-star center,
Lean can now convert this directly into `ReflectionFixedInducedStarDegrees`
and the older `ReflectionFixedStarBoundary`.

### 3. Raw action to default-base / branch-orbit frontier

The no-go side is now broad: default-base, endpoint, fixed-star, current-gap,
and action-level connector aliases all route to contradictions once the
corresponding frontier or wrapper exists.

What remains is to construct one of these packages from the raw action.  In
particular, Lean still needs routes producing the data behind
`RemainingNonRepresentationFrontierAfterDefaultBase`, such as:

- `fixedCenterLeaf`
- `referenceMatching`
- `support_card_boundary`
- `no_card_one`
- `noAllEndpointAdj`

The new K155 bridge reduces one route through this frontier to constructing
explicit fixed-neighbor centers for reflections and the reflection fixed count
`56`.

### 4. A-fiber midpoint reflection and support-card case split

The natural-language proof's A-fiber midpoint reflection argument remains a
major geometric step.  Lean has many boundary structures for the support-card,
card-one/card-two, endpoint, and all-offset cases, but the raw-action
construction into those structures is still the difficult part.

### 5. Endpoint obstruction / singleton / doubling case coverage

The connector and no-go layers for endpoint obstruction, singleton fixedness,
and doubling geometry are mostly present.  The remaining work is to show that
the raw action necessarily falls into one of these cases and to build the
corresponding Lean wrapper.

### 6. Representation component entrypoints

This is mostly reduced.  Current connector files now expose direct routes from
`D19RepresentationCharacterInput`, `TraceCoreCharacterBoundary`,
`D19FinalCharacterInputs`, and `h7`/`hMinus8`/`InvolutionK155` inputs to the
component-boundary no-go surfaces.

Remaining work here is mostly naming cleanup and additional convenience aliases,
not a core mathematical obstacle.

### 7. Public wrapper and alias cleanup

The default-base, endpoint-final, fixed-star, current-gap, action-level, and
endpoint K155 aliases are now significantly expanded.  Further work in this
category should be low-risk: add missing aliases only where they shorten later
proofs or clarify the route from natural-language proof steps to Lean theorem
names.

### 8. Rotation and reflection count plumbing

Rotation fixed-count plumbing is essentially closed.  Reflection-count plumbing
is also available once `InvolutionK155` is supplied, via the existing conversion
to `InvolutionFixedStar55`.

### 9. Pure no-go collapse lemmas

This is the easiest remaining category.  It consists of small lemmas that
collapse a wrapper to an existing no-go theorem.  These are useful for
maintenance and theorem naming, but they do not address the main mathematical
gaps.

## Current Summary

The contradiction routes are now well connected once their inputs exist.  The
main missing work is still:

1. derive the representation character identities `h7` and `hMinus8`;
2. derive `InvolutionK155` from a raw reflection;
3. construct a default-base / branch-orbit frontier wrapper from the raw action.

The current best decomposition of item 2 is:

1. raw reflection geometry -> constructive fixed-neighbor center data
   (`55` fixed neighbors), or constructive induced degree-`55` center data;
2. raw/reflection trace data -> reflection fixed count `56`;
3. center separation from `rotationFixedCenter` for the fixed-center-leaf route;
4. the existing Lean bridge -> `InvolutionK155` and downstream frontiers.
