# Moore57 D19 Lean Gaps

Snapshot: 2026-05-10, after deriving the concrete `(-8)` value-boundary as
the complement of `TraceRepresentationData h.a1` and routing it through the
packaged raw-reflection/no-go frontiers.

This note records the current Lean gaps in difficulty order.  The final goal is
to prove, with no extra assumptions and depending only on mathlib, that no
`D19` action on a Moore graph of degree `57` exists.

## Gap List By Difficulty

### 1. Hardest: derive E7 trace data and standard count inputs from the raw action

Many no-go routes now consume the following upstream package, plus the standard
reflection count inputs:

- `TraceRepresentationData h.a1`, or the slightly richer `D19TraceInput h`;
- fixed count `56` and adjacent-moved count `112` for one reflection
  representative.

The remaining work is to derive these from the raw `D19ActsOnMoore57` action,
using mathlib representation theory as much as possible and avoiding a custom
representation-theory reimplementation.  The `(-8)` character boundary is no
longer an independent representation-decomposition gap: once
`TraceRepresentationData h.a1` is available, Lean derives the complementary
`(-8)` values from the existing projection-character formula.  The hard residue
is now the finite E7 trace data and the raw-action count inputs used by the
packaged bridges.

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
not_isSRGWith_n_k_0_1_of_card_between_52_56
D19ActsOnMoore57.fixedInducedGraph_not_regular_of_fixedVertexCount_between_52_56
D19ActsOnMoore57.involutionFixedSetStar56_of_reflection_trace_fixedVertexCount_bounds
D19ActsOnMoore57.nonempty_involutionK155_of_reflection_trace_fixedVertexCount_bounds
Moore57.LinearMap.exists_int_trace_of_involutive
D19ActsOnMoore57.exists_int_E7Matrix_mul_permMatrix_reflection_trace
D19ActsOnMoore57.ReflectionFixedCountBounds.involutionFixedSetStar56
D19ActsOnMoore57.involutionFixedSetStar56_of_reflection_fixedVertexCount_nat_bounds
adjacentMovedCount_eq_involution_fixed_edge_formula
fixed_neighbor_sum_eq_twice_fixed_induced_edges
fixed_to_moved_edge_count_eq
IsStarWithCenter.card_edgeFinset_eq_card_sub_one
D19ActsOnMoore57.fixedInducedGraph_card_edgeFinset_eq_fixedVertexCount_sub_one_of_isStarWithCenter
D19ActsOnMoore57.reflection_starEdgeCountFormula_of_fixedInduced_isStarWithCenter
D19ActsOnMoore57.D19LinearCharacterInput.involutionFixedSetStar56_of_fixedInduced_starEdgeCountFormula_bounds
D19ActsOnMoore57.D19LinearCharacterInput.fixedVertexCount_reflection_eq_56_of_starEdgeCountFormula
D19ActsOnMoore57.D19LinearCharacterInput.involutionFixedSetStar56_of_starEdgeCountFormula
D19ActsOnMoore57.D19LinearCharacterInput.involutionFixedSetStar56_of_fixedInduced_isStarWithCenter
D19ActsOnMoore57.D19LinearCharacterInput.involutionFixedSetStar56_of_fixedInduced_not_regular
D19ActsOnMoore57.D19LinearCharacterInput.reflection_adjacentMovedCount_int_eq
D19ActsOnMoore57.D19LinearCharacterInput.reflection_regular_fixedVertexCount_mul_eq
D19ActsOnMoore57.D19LinearCharacterInput.reflection_regular_fixedVertexCount_eq_degree_sq_add_one_int
D19ActsOnMoore57.D19LinearCharacterInput.reflection_regular_fixedInduced_degree_cubic
D19ActsOnMoore57.D19LinearCharacterInput.reflection_fixedInducedGraph_not_regular
D19ActsOnMoore57.D19LinearCharacterInput.involutionFixedSetStar56_of_raw_reflection
D19ActsOnMoore57.D19LinearCharacterInput.nonempty_involutionK155_of_raw_reflection
D19ActsOnMoore57.D19LinearCharacterInput.fixedVertexCount_reflection_eq_56_of_raw_reflection
D19ActsOnMoore57.D19LinearCharacterInput.adjacentMovedCount_reflection_eq_112_of_raw_reflection
D19ActsOnMoore57.D19LinearCharacterInput.nonempty_involutionFixedStar55_of_raw_reflection
PermutationRepresentationCharacter.trace_permutationRepresentation
PermutationRepresentationCharacter.character_permutationRepresentation
D19ActsOnMoore57.vertexPermutationRepresentation
D19ActsOnMoore57.vertexPermutationRepresentation_character_eq_fixedVertexCount
D19ActsOnMoore57.trace_permMatrix_smulEquiv_eq_vertexPermutationRepresentation_character
permMatrix_mul_apply
adjMatrix_mul_permMatrix_eq_permMatrix_mul_adjMatrix
allOnesMatrix_mul_permMatrix_eq_permMatrix_mul_allOnesMatrix
E7Matrix_mul_permMatrix_eq_permMatrix_mul_E7Matrix
LinearMap.trace_restrict_range_eq_trace_comp_of_isIdempotentElem
allOnesMatrix_mul_allOnesMatrix
adjMatrix_mul_allOnesMatrix_of_regular
allOnesMatrix_mul_adjMatrix_of_regular
adjMatrix_mul_allOnesMatrix
allOnesMatrix_mul_adjMatrix
allOnesMatrix_mul_allOnesMatrix_of_moore
E7Matrix_mul_E7Matrix_eq_E7Matrix
E7Matrix_isIdempotentElem
matrix_toLin'_mul
toMatrix'_comp_toLin'
trace_toLin'_eq_matrix_trace
toLin'_commute_of_mul_eq
mul_eq_of_toLin'_commute
E7Matrix_mul_permMatrix_toLin'
trace_E7Matrix_mul_permMatrix_toLin'_eq_matrix_trace
E7Matrix_toLin'_commute_permMatrix_toLin'
LinearMap.range_le_comap_of_commute
LinearMap.mapsTo_range_of_commute
Representation.onCommutingRange
LinearEquiv.restrictRangeOfCommute
D19ActsOnMoore57.vertexPermutationMatrixRepresentationOnPi
D19ActsOnMoore57.e7ProjectionRepresentation
E7Matrix_toLin'_isIdempotentElem
trace_restrict_E7Range_permMatrix_toLin'_eq_matrix_trace
D19ActsOnMoore57.trace_restrict_E7Range_smulEquiv_toLin'_eq_matrix_trace
D19ActsOnMoore57.e7ProjectionRepresentation_character_eq_matrix_trace
D19ActsOnMoore57.finrank_E7Range_eq_1729
D19ActsOnMoore57.finrank_e7ProjectionRepresentation_eq_1729
D19ActsOnMoore57.D19LinearCharacterInput.ofE7ProjectionCharacterClassBoundary
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7ProjectionCharacterClassBoundary
E57Matrix
minus8Matrix
E57Matrix_mul_E57Matrix_eq_E57Matrix
E57Matrix_mul_permMatrix_eq_permMatrix_mul_E57Matrix
E57Matrix_mul_E7Matrix_eq_zero
E7Matrix_mul_E57Matrix_eq_zero
minus8Matrix_mul_minus8Matrix_eq_minus8Matrix
minus8Matrix_mul_permMatrix_eq_permMatrix_mul_minus8Matrix
D19ActsOnMoore57.minus8ProjectionRepresentation
D19ActsOnMoore57.minus8ProjectionRepresentation_character_eq_matrix_trace
D19ActsOnMoore57.minus8_trace_eq_d19Linear_of_characterValueBoundary
D19ActsOnMoore57.e7_trace_eq_d19Linear_of_characterClassBoundary
D19ActsOnMoore57.alpha_beta_gamma_le_of_E7_minus8_characterBoundaries
D19ActsOnMoore57.D19LinearCharacterInput.ofE7AndMinus8CharacterBoundaries
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

There is also now a direct Higman-arithmetic bridge from the reflection
fixed-count bounds `52 ≤ a₀ ≤ 56` to `InvolutionFixedSetStar56`.  The E7 trace
integrality assumption has been removed for reflections: a general mathlib
linear-algebra lemma proves that any involutive endomorphism over `ℚ` has
integer trace, and the E7 projection representation turns this into concrete
matrix trace integrality.  The bounds alone exclude the regular fixed-induced
branch by the SRG parameter equation `k^2 = a₀ - 1`, since no square lies
between `51` and `55`; the non-regular strong `(0,1)` branch supplies the
star, and the raw involution edge-count formula supplies the star-edge
formula.  The fixed-induced edge-count formula itself is now formalized for
any involutive automorphism of a Moore57 graph:
`a₁ = 3250 - 58*a₀ + 2*e`, where `e` is the fixed-induced edge count.  The
star specialization is also formalized: if the fixed-induced graph is a star,
then `e = a₀ - 1`, and the packaged character bridge reaches
`InvolutionFixedSetStar56` from that star plus the `52..56` bounds.

With the full D19 linear-character value at reflections, the bounds are no
longer needed once the fixed-induced graph is known to be a star:
star-edge formula plus `α - β = 33` directly forces `a₀ = 56`.  The regular
fixed-induced branch is now excluded under `D19LinearCharacterInput` as well:
the trace equation and the raw involution edge-count formula give
`a₀ * (50 - d) = 2690`, regular strong `(0,1)` parameters give
`a₀ = d^2 + 1`, and the resulting cubic has no root for `d ≤ 57`.  Therefore
the trace-assisted raw-reflection bridge is now closed:
`D19LinearCharacterInput.involutionFixedSetStar56_of_raw_reflection`.  Thin
downstream aliases also expose this as `Nonempty (InvolutionK155 ...)`, the
exact reflection fixed count, `a₁ = 112`, and `InvolutionFixedStar55`.

The remaining raw-reflection-to-star gap is now sharply the Macaj-Siran/Higman
fixed-count range for reflections:

```lean
D19ActsOnMoore57.ReflectionFixedCountBounds
```

Once `52 ≤ fixedVertexCount (sr k) ≤ 56` is available for every reflection,
Lean now produces `InvolutionFixedSetStar56` and `Nonempty (InvolutionK155 ...)`
for every reflection without any additional trace-integrality assumption.

The raw-reflection side has also been tightened without using
`D19LinearCharacterInput`.  The local action on the three rotation orbits of
neighbors of `rotationFixedCenter` now bounds the fixed-induced degree at that
vertex by `3`:

```lean
D19ActsOnMoore57.fixedInducedGraph_reflection_rotationFixedCenter_degree_le_three
```

The regular fixed-induced branch is correspondingly reduced to only
`fixedVertexCount = 2` or `10`, while the non-regular branch is a star and the
Higman/involution arithmetic reduces it to `6, 16, 26, 36, 46, 56`.  The public
combined candidate theorem is:

```lean
D19ActsOnMoore57.fixedVertexCount_reflection_raw_candidates
```

So the active raw-reflection gap has narrowed from proving the full `52..56`
range from scratch to excluding the residual small candidates
`2, 6, 10, 16, 26, 36, 46`, or equivalently proving a lower bound strong
enough to force the final candidate `56`.

The residual candidates are now structurally separated further.  For the
regular branch, Lean proves the constant fixed-induced degree is exactly `1`
or `3`, corresponding to fixed counts `2` or `10`:

```lean
D19ActsOnMoore57.reflection_regular_degree_fixedVertexCount_candidates
```

The `2` case is packaged as a `K₂`-shaped fixed-induced graph at
`rotationFixedCenter`, with one preserved center-neighbor orbit and one moved
pair of center-neighbor orbits.  The `10` case is packaged as the degree-`3`
case where all three center-neighbor rotation orbits are preserved and each
contains exactly one reflection-fixed vertex:

```lean
D19ActsOnMoore57.reflection_regular_fixedVertexCount_eq_two_K2_consequences
D19ActsOnMoore57.reflection_regular_fixedVertexCount_eq_ten_center_orbits_preserved
```

For the non-regular star branch, every candidate star has at least six fixed
vertices, so `rotationFixedCenter` cannot be the star center; it is a leaf and
has exactly one fixed neighbor:

```lean
D19ActsOnMoore57.fixedInducedGraph_reflection_rotationFixedCenter_degree_eq_one_of_fixedInduced_isStarWithCenter
D19ActsOnMoore57.reflectionFixedNeighborFinset_rotationFixedCenter_card_eq_one_of_fixedInduced_isStarWithCenter
```

These refinements show that the current local parity, fixed-induced
strong `(0,1)`, center-degree, and center-neighbor orbit lemmas do not by
themselves contradict the small candidates.  The next genuinely needed input
is a global count/character/Burnside constraint, or a stronger geometric
argument that forces a lower bound past `46`.

Adding the automatic E7 involution trace parity/range constraints gives one
more reduction.  The regular `fixedVertexCount = 2` candidate is impossible
because its Higman numerator is not divisible by `15`; the regular branch
therefore collapses to `fixedVertexCount = 10`:

```lean
D19ActsOnMoore57.reflection_regular_fixedVertexCount_ne_two
D19ActsOnMoore57.fixedVertexCount_reflection_regular_eq_ten
D19ActsOnMoore57.fixedVertexCount_reflection_trace_refined_raw_candidates
```

The same trace constraints do not eliminate the star candidates or the
regular `10` candidate.  Lean records this arithmetic outcome explicitly in
`ReflectionSmallCandidateCharacterConstraints`: star candidates
`6,16,26,36,46,56` survive with E7 traces `193,161,129,97,65,33`, and the
regular `10` case survives with E7 trace `181`.

As a result, the fixed-count lower-bound target is also weaker than the
earlier paper range.  A lower bound of `47` already forces the exact count
`56` and hence `InvolutionFixedSetStar56`:

```lean
D19ActsOnMoore57.fixedVertexCount_reflection_eq_56_of_ge_fortySeven
D19ActsOnMoore57.involutionFixedSetStar56_of_reflection_fixedVertexCount_ge_fortySeven
D19ActsOnMoore57.ReflectionFixedCountLower47
```

So the current raw-reflection-to-star gap can be stated as: prove, from the
raw D19 action and Moore57 axioms alone, that every reflection fixes at least
`47` vertices; equivalently, exclude the remaining trace-compatible candidates
`6,10,16,26,36,46`.

Burnside's lemma has also been checked in Lean.  Using the exact nontrivial
rotation fixed count and the fact that all reflections are conjugate, the
Burnside sum reduces to a divisibility condition
`38 ∣ 3268 + 19 * c`, where `c` is the common reflection fixed count.  This is
exactly the statement that `c` is even:

```lean
D19ActsOnMoore57.thirtyEight_dvd_3268_add_nineteen_mul_reflection_zero
D19ActsOnMoore57.reflection_zero_fixedVertexCount_even
burnside_constraint_all_raw_small_candidates
```

Since all remaining candidates are even, Burnside gives no additional
exclusion beyond already-known involution parity.

The remaining candidate geometry is now routed through a stronger raw split.
For a single reflection, the trace-compatible non-`56` candidates give either
a local fixed-center leaf condition or the regular-`10`
all-center-neighbor-orbits preserved boundary:

```lean
ReflectionTraceRemainingNon56Candidate
ReflectionFixedCenterLeafAt
ReflectionRegularTenAllCenterNeighborOrbitsPreserved
D19ActsOnMoore57.reflection_remaining_non56_candidate_geometry
```

The `56` candidate also lands on the leaf side, because the existing
fixed-count-`56` bridge makes the fixed-induced graph a star and shows
`rotationFixedCenter` is a leaf.  Therefore every raw reflection now satisfies
a uniform split:

```lean
D19ActsOnMoore57.reflectionFixedCenterLeafAt_of_fixedVertexCount_eq_56
D19ActsOnMoore57.reflectionFixedCenterLeafAt_or_regularTenAllCenterNeighborOrbitsPreserved
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_or_exists_regularTenAllCenterNeighborOrbitsPreserved
D19ActsOnMoore57.exists_regularTenAllCenterNeighborOrbitsPreserved_of_not_reflectionFixedCenterLeafBoundary
```

The leaf side now has canonical local connectors from
`ReflectionFixedCenterLeafAt h k` to the existing reflected-index
matching-equation no-go frontier, with reference-matching/disjointness,
midpoint-disjointness, and local-obstruction variants:

```lean
ReflectionFixedCenterLeafAt.remainingCenterNeighborBaseMovedIndex
ReflectionFixedCenterLeafAt.remainingCenterNeighborBasePair
RemainingNon56FixedCenterLeafReferenceConnector
RemainingNon56FixedCenterLeafMidpointDisjointnessConnector
RemainingNon56FixedCenterLeafLocalObstructionConnector
no_remainingNon56FixedCenterLeafReferenceConnector_of_components
no_remainingNon56FixedCenterLeafMidpointDisjointnessConnector_of_components
no_remainingNon56FixedCenterLeafLocalObstructionConnector_of_components
```

The regular-`10` all-preserved boundary has also been sharpened on the default
center-neighbor base.  It fixes one vertex in each of the three default
rotation orbits and proves that no default-base reflected index is moved:

```lean
ReflectionRegularTenAllCenterNeighborOrbitsPreserved.remainingCenterNeighborOrbitBase_orbit_fixed_card_eq_one
ReflectionRegularTenAllCenterNeighborOrbitsPreserved.remainingCenterNeighborOrbitBase_reflectionCenterNeighborOrbitIndex_eq_self
ReflectionRegularTenAllCenterNeighborOrbitsPreserved.not_exists_remainingCenterNeighborOrbitBase_reflectionCenterNeighborOrbitIndex_ne
```

The raw split is also available directly as a default-base index dichotomy:

```lean
D19ActsOnMoore57.exists_moved_defaultBase_index_or_forall_defaultBase_index_fixed
D19ActsOnMoore57.forall_defaultBase_index_fixed_of_not_exists_moved_defaultBase_index
D19ActsOnMoore57.exists_reflection_forall_defaultBase_index_fixed_of_not_reflectionFixedCenterLeafBoundary
```

This confirms that the regular-`10` branch cannot feed the labeled-reflection
matching-equation route via a moved default index.  It remains the cleanest
geometric obstruction to attack next.

The regular-`10` branch has now been numerically evaluated:

```lean
ReflectionRegularTenAllCenterNeighborOrbitsPreserved.fixedInducedGraph_edgeFinset_card_eq_fifteen
ReflectionRegularTenAllCenterNeighborOrbitsPreserved.adjacentMovedCount_eq_2700
ReflectionRegularTenAllCenterNeighborOrbitsPreserved.trace_E7Matrix_mul_permMatrix_eq_181
D19ActsOnMoore57.reflectionRegularTen_trace_E7Matrix_mul_permMatrix_eq_181
```

Thus a regular-`10` obstruction is now equivalent to a reflection whose fixed
induced graph is cubic on 10 vertices, with adjacent-moved count `2700` and
E7 trace `181`.  This survives the earlier parity/range checks, so the next
regular-branch target is a stronger representation-theoretic or geometric
contradiction with trace `181` or with all default center-neighbor orbits
preserved.

The representation-theoretic side of that obstruction is now explicit: if the
E7 trace is packaged as a full D19 linear character, regular-`10` forces
`alpha - beta = 181`, contradicting the packaged reflection equation
`alpha - beta = 33`.

```lean
ReflectionRegularTenAllCenterNeighborOrbitsPreserved.alpha_sub_beta_eq_181_of_e7_linear_character
ReflectionRegularTenAllCenterNeighborOrbitsPreserved.not_d19LinearCharacterInput
D19ActsOnMoore57.reflectionRegularTen_not_d19LinearCharacterInput
D19ActsOnMoore57.D19LinearCharacterInput.no_reflectionRegularTenAllCenterNeighborOrbitsPreserved
D19ActsOnMoore57.D19LinearCharacterInput.reflectionFixedCenterLeafBoundary
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_nonempty_linearCharacterInput
```

So once the raw action supplies `D19LinearCharacterInput` from mathlib
representation theory, the regular-`10` boundary is eliminated automatically,
and the raw split lands in `ReflectionFixedCenterLeafBoundary`.
Lean also records the fixed-induced graph shape of the branch as the
strongly-regular `(10,3,0,1)` graph, with triangle-free and unique common
neighbor consequences:

```lean
ReflectionRegularTenAllCenterNeighborOrbitsPreserved.fixedInducedGraph_isSRGWith_10_3_0_1
ReflectionRegularTenAllCenterNeighborOrbitsPreserved.fixedInducedGraph_triangleFree
ReflectionRegularTenAllCenterNeighborOrbitsPreserved.fixedInducedGraph_existsUnique_commonNeighbor_of_not_adj
```

The remaining main gap for the no-assumptions final theorem is also the
representation/character input itself: derive `D19LinearCharacterInput` (or a
stronger `D19RepresentationCharacterInput`) from the raw D19 action using
mathlib, rather than taking the character decomposition as an assumption.
The first reusable mathlib-side trace lemma is now available for ordinary
permutation representations: `Representation.ofMulAction` has character equal
to the number of fixed points.  The concrete `D19ActsOnMoore57` vertex action
is also packaged as a mathlib permutation representation, and its character is
identified with both `fixedVertexCount` and the local `permMatrix` trace.
The Moore57 trace matrices are now known to commute with graph automorphism
permutation matrices, in particular `E7Matrix Γ * Pσ = Pσ * E7Matrix Γ`.
The core mathlib linear-algebra bridge for a commuting idempotent projection
is also available: the trace of `f` restricted to `range p` equals the ambient
trace of `p ∘ f`.  The `E7Matrix Γ` matrix has now been proved idempotent
from the Moore57 adjacency identities, transported through mathlib's
`Matrix.toLin'`, and used to construct a concrete mathlib representation on
`LinearMap.range (E7Matrix Γ).toLin'`.  Its character is exactly the Higman
matrix trace:
`D19ActsOnMoore57.e7ProjectionRepresentation_character_eq_matrix_trace`.
The same representation now has finrank `1729` by `Representation.char_one`,
and an E7-specific constructor routes any class-boundary decomposition of
`h.e7ProjectionRepresentation` directly to `D19LinearCharacterInput`.
The E7 class-boundary can also be built from the older `a1` arithmetic
surface: `TraceRepresentationData h.a1`, nontrivial rotation fixed count `1`,
and the reflection representative trace now give
`D19CharacterClassBoundary h.e7ProjectionRepresentation`.
The complementary `(-8)` projection has also been constructed as
`minus8Matrix Γ = I - E57 - E7`, where `E57` is the rank-one all-ones
projection.  Lean now proves its idempotence, its commutation with graph
automorphism permutation matrices, the corresponding range representation, and
the expected character formula
`trace(P_g) - 1 - trace(E7 * P_g)`.  A combined bridge now turns an E7
class-boundary and a `(-8)` value-boundary into the concrete
`D19LinearCharacterInput`, with the `α ≤ 113`, `β ≤ 58`, and
`α - β = 33` fields derived by the existing character arithmetic.  The latest
bridge also builds the packaged E7/minus-8 reflection-count boundary directly
from `TraceRepresentationData h.a1`.  The concrete `(-8)` value-boundary is
now derived as the complementary character with multiplicities
`113 - α`, `58 - β`, and `171 - γ`, using the existing projection character
formula; explicit and inverse-pair trace variants remain available as lower
level surfaces.  There are also constructors one step further upstream from
`D19TraceInput h`.  From there it exposes the bare `D19LinearCharacterInput`,
raw-reflection fixed-star/K155 outputs, the fixed-center leaf split,
representation component boundary, and current final-gap no-go.  The
paper-star and explicit `K_{1,55}` downstream connectors are also now exposed:

```lean
D19ActsOnMoore57.D19LinearCharacterInput.nonempty_ofE7ProjectionCharacterClassBoundary
D19ActsOnMoore57.e7_rotation_trace_eq_of_fixed_one_and_a1_trace
D19ActsOnMoore57.e7_rotation_trace_eq_of_traceRepresentationData
D19ActsOnMoore57.E7ProjectionCharacterClassBoundary.ofTraceRepresentationData
D19ActsOnMoore57.E7ProjectionCharacterClassBoundary.reflection_zero_trace_eq_of_traceRepresentationData_and_counts
D19ActsOnMoore57.E7ProjectionCharacterClassBoundary.ofTraceRepresentationDataAndReflectionCounts
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationData
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndReflectionStar
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8ProjectionTraceBoundaryAndReflectionStar
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8InversePairTraceBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataAndMinus8InversePairTraceBoundaryAndReflectionStar
D19ActsOnMoore57.minus8ProjectionRepresentation_characterValueBoundary_of_traceRepresentationDataComplement
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofTraceRepresentationDataComplement
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_traceRepresentationDataComplement
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplement
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputComplementAndReflectionStar
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplement
D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplement_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplement_raw_reflection
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplement
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplement
D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplement
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputComplementAndReflectionStar
D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputComplementAndReflectionStar_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputComplementAndReflectionStar_raw_reflection
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputComplementAndReflectionStar
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputComplementAndReflectionStar
D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputComplementAndReflectionStar
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplement
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofD19CharacterInputComplementAndReflectionStar
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofD19RepresentationCharacterInputComplement
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19CharacterInputComplement
D19ActsOnMoore57.involutionFixedSetStar56_of_d19CharacterInputComplement_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_d19CharacterInputComplement_raw_reflection
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19CharacterInputComplement
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19CharacterInputComplement
D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19CharacterInputComplement
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19CharacterInputComplementAndReflectionStar
D19ActsOnMoore57.involutionFixedSetStar56_of_d19CharacterInputComplementAndReflectionStar_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_d19CharacterInputComplementAndReflectionStar_raw_reflection
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19CharacterInputComplementAndReflectionStar
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19CharacterInputComplementAndReflectionStar
D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19CharacterInputComplementAndReflectionStar
D19FinalCharacterInputs.toD19TraceInput
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplement
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofD19FinalCharacterInputsComplementAndReflectionStar
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19FinalCharacterInputsComplement
D19ActsOnMoore57.involutionFixedSetStar56_of_d19FinalCharacterInputsComplement_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_d19FinalCharacterInputsComplement_raw_reflection
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19FinalCharacterInputsComplement
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19FinalCharacterInputsComplement
D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19FinalCharacterInputsComplement
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19FinalCharacterInputsComplementAndReflectionStar
D19ActsOnMoore57.involutionFixedSetStar56_of_d19FinalCharacterInputsComplementAndReflectionStar_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_d19FinalCharacterInputsComplementAndReflectionStar_raw_reflection
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19FinalCharacterInputsComplementAndReflectionStar
D19ActsOnMoore57.D19FinalInputs.nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
D19ActsOnMoore57.D19FinalInputs.involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
D19ActsOnMoore57.D19FinalInputs.nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
D19ActsOnMoore57.D19FinalInputs.reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
D19ActsOnMoore57.D19FinalInputs.no_currentFinalGapBoundary_of_complementAndReflectionStar
D19ActsOnMoore57.D19ConstructiveFinalInputs.no_currentFinalGapBoundary_of_complementAndReflectionStar
D19ActsOnMoore57.no_actionLevelFinalBoundary_of_d19CharacterInputComplement
D19ActsOnMoore57.no_actionLevelLocalObstructionBoundary_of_d19CharacterInputComplement
D19ActsOnMoore57.no_actionLevelReducedCoordinateWitnessBoundary_of_d19CharacterInputComplement
D19ActsOnMoore57.no_actionLevelSetInvariantWitnessBoundary_of_d19CharacterInputComplement
D19ActsOnMoore57.no_actionLevelCommonNeighborReducedBoundary_of_d19CharacterInputComplement
D19ActsOnMoore57.no_actionLevelMinimalRemainingBoundary_of_d19CharacterInputComplement
D19ActsOnMoore57.no_actionLevelMinimalRemainingRefinedBoundary_of_d19CharacterInputComplement
D19ActsOnMoore57.no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_d19CharacterInputComplement
D19ActsOnMoore57.no_actionLevelFinalBoundary_of_d19CharacterInputComplementAndReflectionStar
D19ActsOnMoore57.no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_d19CharacterInputComplementAndReflectionStar
D19ReducedHypotheses.nonempty_d19LinearCharacterInput_of_complement
D19ReducedHypotheses.involutionFixedSetStar56_of_complement_raw_reflection
D19ReducedHypotheses.nonempty_involutionK155_of_complement_raw_reflection
D19ReducedHypotheses.reflectionFixedCenterLeafBoundary_of_complement
D19ReducedHypotheses.representationCharacterComponentsBoundary_of_complement
D19ReducedHypotheses.no_currentFinalGapBoundary_of_complement
D19ReducedHypotheses.nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
D19ReducedHypotheses.involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
D19ReducedHypotheses.nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
D19ReducedHypotheses.reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
D19ReducedHypotheses.representationCharacterComponentsBoundary_of_complementAndReflectionStar
D19ReducedHypotheses.no_currentFinalGapBoundary_of_complementAndReflectionStar
D19GeometricInputs.nonempty_d19LinearCharacterInput_of_complement
D19GeometricInputs.involutionFixedSetStar56_of_complement_raw_reflection
D19GeometricInputs.nonempty_involutionK155_of_complement_raw_reflection
D19GeometricInputs.reflectionFixedCenterLeafBoundary_of_complement
D19GeometricInputs.representationCharacterComponentsBoundary_of_complement
D19GeometricInputs.no_currentFinalGapBoundary_of_complement
D19GeometricInputs.nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
D19GeometricInputs.involutionFixedSetStar56_of_complementAndReflectionStar_raw_reflection
D19GeometricInputs.nonempty_involutionK155_of_complementAndReflectionStar_raw_reflection
D19GeometricInputs.reflectionFixedCenterLeafBoundary_of_complementAndReflectionStar
D19GeometricInputs.representationCharacterComponentsBoundary_of_complementAndReflectionStar
D19GeometricInputs.no_currentFinalGapBoundary_of_complementAndReflectionStar
D19ActionConcreteData.nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
D19ActionOrbitConcreteData.nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
D19OrbitContributionData.nonempty_d19LinearCharacterInput_of_complementAndReflectionStar
D19OrbitContributionData.no_currentFinalGapBoundary_of_complementAndReflectionStar
D19ActsOnMoore57.D19RepresentationCharacterInput.toD19FinalCharacterInputs_autoFixedBound
D19ActsOnMoore57.TraceCoreCharacterBoundary.toD19FinalCharacterInputs_autoFixedBound
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_representationCharacterInputComplementAndReflectionStar
D19ActsOnMoore57.involutionFixedSetStar56_of_representationCharacterInputComplementAndReflectionStar_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_representationCharacterInputComplementAndReflectionStar_raw_reflection
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_representationCharacterInputComplementAndReflectionStar
D19ActsOnMoore57.no_currentFinalGapBoundary_of_representationCharacterInputComplementAndReflectionStar
D19ActsOnMoore57.no_actionLevelFinalBoundary_of_representationCharacterInputComplementAndReflectionStar
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_traceCoreCharacterBoundaryComplementAndReflectionStar
D19ActsOnMoore57.involutionFixedSetStar56_of_traceCoreCharacterBoundaryComplementAndReflectionStar_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_traceCoreCharacterBoundaryComplementAndReflectionStar_raw_reflection
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_traceCoreCharacterBoundaryComplementAndReflectionStar
D19ActsOnMoore57.no_currentFinalGapBoundary_of_traceCoreCharacterBoundaryComplementAndReflectionStar
D19ActsOnMoore57.no_actionLevelFinalBoundary_of_traceCoreCharacterBoundaryComplementAndReflectionStar
D19ActsOnMoore57.involutionFixedSetStar56_of_traceRepresentationDataComplement
D19ActsOnMoore57.nonempty_involutionK155_of_traceRepresentationDataComplement
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_traceRepresentationDataComplement
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_traceRepresentationDataComplement
D19ActsOnMoore57.no_currentFinalGapBoundary_of_traceRepresentationDataComplement
D19ActsOnMoore57.no_actionLevelFinalBoundary_of_traceRepresentationDataComplement
D19ActsOnMoore57.no_actionLevelLocalObstructionBoundary_of_traceRepresentationDataComplement
D19ActsOnMoore57.no_actionLevelReducedCoordinateWitnessBoundary_of_traceRepresentationDataComplement
D19ActsOnMoore57.no_actionLevelSetInvariantWitnessBoundary_of_traceRepresentationDataComplement
D19ActsOnMoore57.no_actionLevelCommonNeighborReducedBoundary_of_traceRepresentationDataComplement
D19ActsOnMoore57.no_actionLevelMinimalRemainingBoundary_of_traceRepresentationDataComplement
D19ActsOnMoore57.no_actionLevelMinimalRemainingRefinedBoundary_of_traceRepresentationDataComplement
D19ActsOnMoore57.no_actionLevelMinimalRemainingRefinedMatchingBoundary_of_traceRepresentationDataComplement
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8Values
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8ValuesAndReflectionStar
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8ProjectionTraceBoundaryAndReflectionStar
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8InversePairTraceBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.ofD19TraceInputAndMinus8InversePairTraceBoundaryAndReflectionStar
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8Values
D19ActsOnMoore57.involutionFixedSetStar56_of_traceRepresentationDataAndMinus8Values
D19ActsOnMoore57.nonempty_involutionK155_of_traceRepresentationDataAndMinus8Values
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_traceRepresentationDataAndMinus8Values
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_traceRepresentationDataAndMinus8Values
D19ActsOnMoore57.no_currentFinalGapBoundary_of_traceRepresentationDataAndMinus8Values
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.involutionFixedSetStar56_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.nonempty_involutionK155_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.no_currentFinalGapBoundary_of_traceRepresentationDataAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8InversePairTraceBoundary
D19ActsOnMoore57.involutionFixedSetStar56_of_traceRepresentationDataAndMinus8InversePairTraceBoundary_raw_reflection
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputAndMinus8Values
D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputAndMinus8Values
D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputAndMinus8Values
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputAndMinus8Values
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputAndMinus8Values
D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputAndMinus8Values
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.reflectionFixedCenterLeafBoundary_of_d19TraceInputAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_d19TraceInputAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputAndMinus8ProjectionTraceBoundary
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_d19TraceInputAndMinus8InversePairTraceBoundary
D19ActsOnMoore57.involutionFixedSetStar56_of_d19TraceInputAndMinus8InversePairTraceBoundary_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_d19TraceInputAndMinus8InversePairTraceBoundary_raw_reflection
D19ActsOnMoore57.no_currentFinalGapBoundary_of_d19TraceInputAndMinus8InversePairTraceBoundary
D19ActsOnMoore57.nonempty_d19LinearCharacterInput_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
D19ActsOnMoore57.involutionFixedSetStar56_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
D19ActsOnMoore57.nonempty_involutionK155_of_traceRepresentationDataAndMinus8ValuesAndReflectionStar
D19ActsOnMoore57.D19LinearCharacterInput.nonempty_ofE7AndMinus8CharacterBoundaries
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundaries
D19ActsOnMoore57.D19LinearCharacterInput.nonempty_ofE7AndMinus8InversePairTraceBoundaries
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8InversePairTraceBoundaries
D19ActsOnMoore57.involutionFixedSetStar56_of_E7AndMinus8CharacterBoundariesAndReflectionCounts_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_E7AndMinus8CharacterBoundariesAndReflectionCounts_raw_reflection
D19ActsOnMoore57.involutionFixedSetStar56_of_E7AndMinus8InversePairTraceBoundariesAndReflectionCounts_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_E7AndMinus8InversePairTraceBoundariesAndReflectionCounts_raw_reflection
D19ActsOnMoore57.involutionFixedSetStar56_of_nonempty_linearCharacterInput_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_nonempty_linearCharacterInput_raw_reflection
D19ActsOnMoore57.fixedVertexCount_reflection_eq_56_of_nonempty_linearCharacterInput_raw_reflection
D19ActsOnMoore57.adjacentMovedCount_reflection_eq_112_of_nonempty_linearCharacterInput_raw_reflection
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_nonempty_linearCharacterInput
no_D19_fixedStarLocalObstructionBoundary_of_nonempty_linearCharacterInput
no_D19_fixedStarWitnessBoundary_of_nonempty_linearCharacterInput
no_D19_fixedStarCoordinateWitnessBoundary_of_nonempty_linearCharacterInput
no_D19_currentFinalGapBoundary_of_nonempty_linearCharacterInput
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.nonempty_d19LinearCharacterInput
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.involutionFixedSetStar56_raw_reflection
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.nonempty_involutionK155_raw_reflection
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.fixedVertexCount_reflection_eq_56_raw_reflection
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.adjacentMovedCount_reflection_eq_112_raw_reflection
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.reflectionFixedCenterLeafBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.no_currentFinalGapBoundary
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.nonempty_d19LinearCharacterInput
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.involutionFixedSetStar56_raw_reflection
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.nonempty_involutionK155_raw_reflection
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.fixedVertexCount_reflection_eq_56_raw_reflection
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.adjacentMovedCount_reflection_eq_112_raw_reflection
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.reflectionFixedCenterLeafBoundary
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.representationCharacterComponentsBoundary
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.no_currentFinalGapBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.no_fixedStarReferenceMatchingCardinalityPipeline
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.no_fixedStarLocalObstruction
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.no_fixedStarWitness
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.no_fixedStarCoordinateWitness
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.no_actionLevelCommonNeighborReducedBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.no_actionLevelMinimalRemainingBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.no_actionLevelMinimalRemainingRefinedBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.no_actionLevelMinimalRemainingRefinedMatchingBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.no_actionLevelFinalBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.no_actionLevelLocalObstructionBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.no_actionLevelReducedCoordinateWitnessBoundary
D19ActsOnMoore57.E7Minus8CharacterReflectionCountBoundary.no_actionLevelSetInvariantWitnessBoundary
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.no_fixedStarReferenceMatchingCardinalityPipeline
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.no_fixedStarLocalObstruction
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.no_fixedStarWitness
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.no_fixedStarCoordinateWitness
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.no_actionLevelCommonNeighborReducedBoundary
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.no_actionLevelMinimalRemainingBoundary
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.no_actionLevelMinimalRemainingRefinedBoundary
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.no_actionLevelMinimalRemainingRefinedMatchingBoundary
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.no_actionLevelFinalBoundary
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.no_actionLevelLocalObstructionBoundary
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.no_actionLevelReducedCoordinateWitnessBoundary
D19ActsOnMoore57.E7Minus8InversePairTraceReflectionCountBoundary.no_actionLevelSetInvariantWitnessBoundary
no_D19_actionLevelCommonNeighborReducedBoundary_of_nonempty_linearCharacterInput
no_D19_actionLevelMinimalRemainingBoundary_of_nonempty_linearCharacterInput
no_D19_actionLevelMinimalRemainingRefinedBoundary_of_nonempty_linearCharacterInput
no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_nonempty_linearCharacterInput
no_D19_actionLevelCaseBoundary_of_nonempty_linearCharacterInput
no_D19_actionLevelWitnessBoundary_of_nonempty_linearCharacterInput
no_D19_actionLevelCoordinateWitnessBoundary_of_nonempty_linearCharacterInput
no_D19_actionLevelFinalBoundary_of_nonempty_linearCharacterInput
no_D19_actionLevelLocalObstructionBoundary_of_nonempty_linearCharacterInput
no_D19_actionLevelDoublingEquationSupportBoundary_of_nonempty_linearCharacterInput
no_D19_actionLevelSetInvariantWitnessBoundary_of_nonempty_linearCharacterInput
no_D19_actionLevelReducedCoordinateWitnessBoundary_of_nonempty_linearCharacterInput
D19ActsOnMoore57.D19LinearCharacterInput.ofE7AndMinus8CharacterBoundariesAndPaperFixedStar56
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
D19ActsOnMoore57.D19LinearCharacterInput.ofE7AndMinus8CharacterBoundariesAndInvolutionK155
D19ActsOnMoore57.representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
D19ActsOnMoore57.involutionFixedSetStar56_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56_raw_reflection
D19ActsOnMoore57.involutionFixedSetStar56_of_E7AndMinus8CharacterBoundariesAndInvolutionK155_raw_reflection
D19CharacterClassBoundary.ofE7ProjectionTraceBoundary
D19CharacterValueBoundary.ofMinus8ProjectionTraceBoundary
E7ProjectionInversePairTraceBoundary.toCharacterClassBoundary
Minus8ProjectionInversePairTraceBoundary.toCharacterValueBoundary
D19ActsOnMoore57.involutionFixedSetStar56_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56_raw_reflection
D19ActsOnMoore57.involutionFixedSetStar56_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155_raw_reflection
D19ActsOnMoore57.nonempty_involutionK155_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155_raw_reflection
no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8TraceBoundariesAndPaperFixedStar56
no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8TraceBoundariesAndInvolutionK155
no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56
no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155
```

These are thin wrappers around existing mathlib-facing `Representation.character`
bridges and the existing fixed-star/no-go APIs; they add no new linear-algebra
or representation-theory assumptions beyond concrete trace/value boundaries
for the two projection representations and the explicit reflection-side
paper-star/K155/count input needed to build `D19LinearCharacterInput`.  The
latest wrappers also expose the bare `Nonempty (D19LinearCharacterInput h)`
consequence of the E7 and E7/minus-8 boundary packages, so later modules can
consume the representation input without choosing the concrete record
manually.  That `Nonempty` boundary now has direct reflection consumers for
fixed-star, `K_{1,55}`, fixed-count, adjacent-moved count, and the
fixed-center leaf split, plus no-go consumers for the fixed-star and current
final-gap frontiers.  The same data is also packaged in Type-valued boundary
records for both the direct character-boundary and inverse-pair trace-boundary
surfaces, so downstream code can carry the finite representation obligations
as one object; those packages now expose direct fixed-star no-go wrappers as
methods, and direct current-gap/action-level no-go wrappers for both package
surfaces.  The `Nonempty (D19LinearCharacterInput h)` boundary also now routes
directly to the action-level and current-gap no-go frontiers.  The
rotation obligations have also been reduced conservatively to one
representative from each inverse pair, using only the group-theoretic fact that
`r d` is conjugate to `r (-d)` in `D19`; nonzero rotations are not all conjugate.
A direct route from the two concrete
character boundaries alone to raw-reflection fixed stars would currently be
circular, because the raw-reflection fixed-star theorem itself consumes the
resulting `D19LinearCharacterInput`.  The remaining representation-theoretic
gap is therefore sharply isolated: derive the existing `D19TraceInput h`,
`D19CharacterInput h`, `D19FinalCharacterInputs h`, or
`TraceRepresentationData h.a1` surfaces from the raw action, together with the
standard reflection count inputs.  From `D19TraceInput h` and its coarser
character/final-character packages, and the reduced/geometric/action data
records that carry those packages, the complementary route now goes straight to
fixed-star, `K_{1,55}`, fixed-center leaf, representation-component,
current-gap, and action-level no-go frontiers.  The complementary `(-8)`
character values follow automatically from the E7 data and no longer need to be
supplied as a separate representation decomposition hypothesis.  The
rotation fixed-count upper bound used by `D19FinalCharacterInputs` is also no
longer a separate input on the representation side: the raw action's proved
rotation fixed-count-one theorem now fills that field automatically for
`D19RepresentationCharacterInput` and `TraceCoreCharacterBoundary`.

The domain split has also started.  Pure D19 character functions and
inverse-pair conjugacy reductions live under `Moore57/GroupTheory/`, generic
fixed-point counting for group actions lives under `Moore57/GroupAction/`,
and the strong `(λ, μ) = (0, 1)` graph/star classification lives under
`Moore57/GraphTheory/`:

```lean
Moore57.GroupTheory.Dihedral19LinearCharacter
Moore57.GroupTheory.Dihedral19CharacterValueReduction
Moore57.GroupAction.FixedPoints
Moore57.GroupAction.InvolutionParity
Moore57.GraphTheory.AdjacentMovedCount
Moore57.GraphTheory.StrongZeroOne
Moore57.LinearAlgebra.InvolutionTrace
```

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
