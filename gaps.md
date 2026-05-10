# Moore57 D19 Lean Gaps

Snapshot: 2026-05-10, after commit `074c3ce`.

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
input used downstream.  The missing part is the raw geometric proof that a
reflection in a hypothetical `D19` action has the required `K_{1,55}` fixed-star
shape.

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

