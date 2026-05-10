# Moore57 D19 Lean Gaps

Snapshot: 2026-05-10, after adding reflection-orbit fixed-point local facts and
Higman/star-edge arithmetic connectors.

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
InvolutionK155.toInvolutionFixedSetStar56
D19ActsOnMoore57.reflection_smulEquiv_involutive
D19ActsOnMoore57.involutionFixedSetStar56_of_reflection_fixedVertexCount_and_fixedSetStarWithCenter
D19ActsOnMoore57.involutionFixedSetStar56OfReflectionFixedNeighborCenterCount
IsStrongZeroOne.exists_isStarWithCenter_of_not_regular
D19ActsOnMoore57.exists_fixedSetStarWithCenter_of_fixedVertexCount_eq_56
D19ActsOnMoore57.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56
D19ActsOnMoore57.involutionFixedSetStar56_of_linear_character_reflection_eq_and_adjacentMovedCount_eq_112
D19ActsOnMoore57.D19LinearCharacterInput.involutionFixedSetStar56_of_adjacentMovedCount_eq_112
D19ActsOnMoore57.D19LinearCharacterInput.nonempty_involutionK155_of_adjacentMovedCount_eq_112
two_dvd_card_sub_fixedVertexCount_of_involutive
two_dvd_adjacentMovedCount_of_involutive
D19ActsOnMoore57.two_dvd_reflection_adjacentMovedCount
IsMoore57.higman_trace_int_natModEq
D19ActsOnMoore57.D19LinearCharacterInput.reflection_higman_natModEq
D19ActsOnMoore57.rotationFixedCenter_fixed_reflection
D19ActsOnMoore57.exists_three_rotation_orbits_on_rotationFixedCenter_neighbors
D19ActsOnMoore57.reflection_fixed_points_in_rotationOrbitFinset_card_eq_one_of_mem
D19ActsOnMoore57.reflection_fixed_center_neighbor_orbit_card_eq_one_of_index_eq
fixedNeighborFinsetOf_card_odd_of_moore57
D19ActsOnMoore57.reflectionFixedNeighborFinset_card_odd
D19ActsOnMoore57.fixedInducedGraph_reflection_degree_odd
BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex_involutive
BranchOrbitABCReflectionLabeling.exists_reflectionCenterNeighborOrbitIndex_eq_self
D19ActsOnMoore57.exists_reflection_fixed_center_neighbor_orbit_card_eq_one
InvolutionHigmanCountArithmetic.starEdgeCountFormula_a0_eq_56_of_bounds
IsMoore57.starEdgeCountFormula_fixedVertexCount_eq_56_of_bounds
D19ActsOnMoore57.D19LinearCharacterInput.reflection_starEdgeCountFormula_fixedVertexCount_eq_56_of_bounds
D19ActsOnMoore57.involutionFixedSetStar56_of_reflection_trace_starEdgeCountFormula_bounds
D19ActsOnMoore57.D19LinearCharacterInput.involutionFixedSetStar56_of_starEdgeCountFormula_bounds
adjacentMovedCount_eq_involution_fixed_edge_formula
fixed_neighbor_sum_eq_twice_fixed_induced_edges
fixed_to_moved_edge_count_eq
IsStarWithCenter.card_edgeFinset_eq_card_sub_one
D19ActsOnMoore57.fixedInducedGraph_card_edgeFinset_eq_fixedVertexCount_sub_one_of_isStarWithCenter
D19ActsOnMoore57.reflection_starEdgeCountFormula_of_fixedInduced_isStarWithCenter
D19ActsOnMoore57.D19LinearCharacterInput.involutionFixedSetStar56_of_fixedInduced_starEdgeCountFormula_bounds
D19ActsOnMoore57.D19LinearCharacterInput.ofLinearCharacterAndPaperFixedStar56
D19ActsOnMoore57.D19RepresentationCharacterInput.ofLinearCharacterAndPaperFixedStar56
D19FinalCharacterInputs.ofLinearCharacterAndPaperFixedStar56
```

This matches the Makhnev-Paduchikh/Higman formulation more directly than the
constructive center-count records.  After reading Macaj-Siran 2010, the Lean
route now follows their state-of-the-art summary: Lemma 1 supplies the
fixed-induced strong-graph classification, while Lemma 2 supplies the
involution fixed count.

The raw-reflection automatic fields are now separated out: a reflection in a
`D19ActsOnMoore57` action is already an involutive graph automorphism.  The
Macaj-Siran Lemma 1 classification branch needed here is also formalized in
the non-regular form `IsStrongZeroOne.exists_isStarWithCenter_of_not_regular`.
Combining it with fixed-induced common-neighbor inheritance and the
`56`-vertex regular-branch exclusion gives:

```lean
D19ActsOnMoore57.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56
```

So the remaining raw-reflection-to-paper-star gap is no longer fixed-star
geometry itself; it is the Higman/Macaj-Siran Lemma 2 count
`fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56` from the raw
involutory automorphism.  A packaged trace route is also now available:
`D19LinearCharacterInput` plus the standard reflection adjacent-moved count
`a₁ = 112` gives both `InvolutionFixedSetStar56` and
`Nonempty (InvolutionK155 ...)`.  Thus the remaining Lemma 2 work is either
to prove `a₀ = 56` directly for involutions, or to prove the trace/character
and `a₁ = 112` data that forces the same fixed count.  General involution
parity constraints are now available: non-fixed vertices and adjacent-moved
vertices come in swapped pairs, so `Fintype.card V - fixedVertexCount σ` and
`adjacentMovedCount Γ σ` are even.  These are not enough by themselves to prove
Macaj-Siran Lemma 2, but they are reusable arithmetic constraints for the
remaining count argument.  Higman's Lemma 3 congruence is also separated out:
if the `E7` trace is integer-valued, then
`adjacentMovedCount Γ σ ≡ 7 * fixedVertexCount σ + 5 [MOD 15]`; packaged
`D19LinearCharacterInput` supplies this congruence for every reflection.
The arithmetic part of the Lemma 2 route is now factored further:
if the fixed-induced graph is a star, the explicit edge-count formula
`a₁ = 3250 - 58*a₀ + 2*(a₀ - 1)` and bounds `52 ≤ a₀ ≤ 56` force
`a₀ = 56`.  Thus the remaining non-paper arithmetic hypotheses are now
localized to proving the star-edge formula and the fixed-count bounds from
the raw involution/reflection geometry.

The local reflection action around `rotationFixedCenter` is also recorded:
each reflection fixes `rotationFixedCenter`, the center-neighbor set splits
into three 19-point rotation orbits, and any center-neighbor rotation orbit
preserved by a reflection contains exactly one reflection-fixed vertex.  The
induced action on these three orbit indices is now an involution, hence fixes
at least one orbit; consequently every reflection fixes exactly one vertex in
at least one center-neighbor rotation orbit.  Separately, every fixed vertex
of a Moore57 involution has an odd number of fixed neighbors, so every degree
in the fixed-induced reflection graph is odd.  These local constraints are
not yet the full fixed-count theorem, but they are raw-reflection consequences
that narrow the remaining fixed-induced classification and count work.

There is also now a direct Higman-arithmetic bridge from `trace integer +
star-edge formula + 52..56 fixed-count bounds` to
`InvolutionFixedSetStar56`.  The fixed-induced edge-count formula itself is
now formalized for any involutive automorphism of a Moore57 graph:
`a₁ = 3250 - 58*a₀ + 2*e`, where `e` is the fixed-induced edge count.  The
star specialization is also formalized: if the fixed-induced graph is a star,
then `e = a₀ - 1`, and the packaged character bridge reaches
`InvolutionFixedSetStar56` from that star plus the `52..56` bounds.

The remaining non-paper-count bottleneck has therefore shifted again:
derive the fixed-induced star/non-regular branch and the fixed-count bounds
`52 ≤ a₀ ≤ 56` from the raw reflection geometry, or prove the exact
Macaj-Siran/Higman count `a₀ = 56` directly.

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
2. prove the Higman/Macaj-Siran involution counts, especially reflection
   `a₀ = 56` and, for the trace bridge, `a₁ = 112`;
3. construct a default-base / branch-orbit frontier wrapper from the raw action.

The current best decomposition of item 2 is:

1. raw involution trace/character data -> reflection fixed count `56`;
2. if using the linear-character route, prove the standard adjacent-moved count
   `112`;
3. the existing Lean bridge -> `InvolutionFixedSetStar56` and Prop-level
   `Nonempty (InvolutionK155 ...)`;
4. for constructive fixed-center-leaf routes, still build Type-valued
   fixed-neighbor center data and separate it from `rotationFixedCenter`.
