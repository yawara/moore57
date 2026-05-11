import Moore57.Phases.Phase7
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCResidualContribution
import Moore57.D19OnMoore57.AFiber.AFiberCardinality38FromClosures
import Moore57.D19OnMoore57.Reflection.ReflectionRawActionFixedCenterLeaf

/-!
# Final assembly: closing the geometric witness from raw action

Discovery: the codebase already provides
`BranchOrbitABCFromCenter.toComplementResidualSplit38WitnessFromBFibersOfReflection`
which builds the split compact witness from:

* a fixed-center A/B/C branch decomposition (`BranchOrbitABCFromCenter h`,
  available via `ofExistsThreeRotationOrbitFinsetNeighbors h`),
* the all-A-fiber cardinality `38` boundary
  (`AFiberCardinality38Boundary h data.toAFiberCoordinates univ`,
  available via Option A: `aFiberCardinality38Boundary_of_closures`),
* an exact reflection swap `sr k · b0 = c0`
  (available via `fixedCenterLeafDefaultBasePair_of_raw_action`).

Forgetting the split to the plain compact form gives
`AdjacentMovedReflectionComplementResidual38Witness h
(data.toOrbitBaseSelectionInputFromBFibers)`.

This file assembles all the pieces into the final non-existence theorem
`no_D19_acts_on_Moore57_unconditional`.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The compact adjacent-moved witness over the B-fiber selected input,
constructed entirely from raw action. -/
noncomputable def adjacentMovedReflectionComplementResidual38Witness_of_raw_action
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    AdjacentMovedReflectionComplementResidual38Witness h
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action
        k).data.toOrbitBaseSelectionInputFromBFibers := by
  classical
  let labeling := h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k
  let data := labeling.data
  -- AFiberCardinality38Boundary from raw action via Option A.
  have boundary :
      AFiberCardinality38Boundary h data.toAFiberCoordinates
        (Finset.univ : Finset (ZMod 19)) :=
    labeling.aFiberCardinality38Boundary_of_closures
  -- reflection swap from labeling.
  have href : h.smul (DihedralGroup.sr labeling.k) data.b0 = data.c0 :=
    labeling.reflection_b0_eq_c0
  -- Build the split witness using the existing infrastructure.
  exact
    (data.toComplementResidualSplit38WitnessFromBFibersOfReflection
      boundary href).toComplementResidual38Witness

/-- Generic Phase 6 (compact form) parametrized by any orbit base input:
combine Phase 5 RotationCharacterConstancy with a compact adjacent-moved
witness over any orbit base to get `False`. -/
theorem false_of_RotationCharacterConstancy_and_compactAdjacentMoved_generic
    (h : D19ActsOnMoore57 V Γ)
    (rcc : RotationCharacterConstancy h)
    (intval : rcc.IntegerValue)
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (rotation_int : (alpha : ℤ) + (beta : ℤ) - (gamma : ℤ) = intval.intValue)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (orbitBase : OrbitBaseSelectionInput h)
    (adjacentMoved :
      AdjacentMovedReflectionComplementResidual38Witness h orbitBase) :
    False := by
  classical
  have hrep : D19ActsOnMoore57.D19RepresentationCharacterInput h :=
    (D19LinearCharacterInput.ofE7ProjectionCharacterClassBoundary h
        alpha beta gamma
        (d19CharacterClassBoundary_of_RotationCharacterConstancy rcc intval
          alpha beta gamma reflection dimension rotation_int)
        reflection minus8_trivial_nonneg minus8_sign_nonneg).toD19RepresentationCharacterInput
  have hfix : fixedVertexCount (h.rotation 1) = 1 := by
    have h1 : fixedVertexCount (h.smulEquiv (DihedralGroup.r 1)) = 1 :=
      h.rotationFixedCountOne_smulEquiv 1 (by decide)
    simpa [D19ActsOnMoore57.rotation] using h1
  exact
    D19FinalRepresentationCountCompactInputs.not_nonempty h
      ⟨{ representation := hrep
         rotationOne_fixed_count := hfix
         orbitBase := orbitBase
         adjacentMoved := adjacentMoved }⟩

/-- Unconditional False from `h : D19ActsOnMoore57 V Γ` alone: combining
Phase 7's RotationCharacterConstancy package (closed in Phase 7) with the
geometric witness constructed in this file. -/
theorem false_of_raw_action (h : D19ActsOnMoore57 V Γ) : False := by
  classical
  let pkg := h.rotationCharacterConstancyPackage_of_raw_action
  let labeling := h.fixedCenterLeafDefaultBaseLabeling_of_raw_action (0 : ZMod 19)
  exact
    false_of_RotationCharacterConstancy_and_compactAdjacentMoved_generic
      h pkg.toRotationCharacterConstancy pkg.toIntegerValue
      pkg.alpha pkg.beta pkg.gamma pkg.reflection pkg.dimension pkg.rotation_int
      pkg.minus8_trivial_nonneg pkg.minus8_sign_nonneg
      labeling.data.toOrbitBaseSelectionInputFromBFibers
      (h.adjacentMovedReflectionComplementResidual38Witness_of_raw_action (0 : ZMod 19))

end D19ActsOnMoore57

/-- **Main theorem**: `D19ActsOnMoore57 V Γ` is uninhabited.

The Moore graph of degree `57` (SRG(3250, 57, 0, 1)) does not admit `D₁₉`
as a subgroup of its automorphism group. -/
theorem no_D19_acts_on_Moore57_unconditional
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] :
    ¬ Nonempty (D19ActsOnMoore57 V Γ) := by
  rintro ⟨h⟩
  exact h.false_of_raw_action

end Moore57
