import Moore57.D19FinalInputs
import Moore57.OrbitBaseSelectionInputBridge
import Moore57.AFiberHybridBoundaryFromCriteria
import Moore57.AFiberOrbitMovingResidual
import Moore57.AFiberMatchingSupportEquations
import Moore57.AFiberResidualSplitBridge

/-!
# Final D19 inputs from direct character and A-fiber boundary data

This file gives a thinner final entry point than
`D19FinalCharacterCriterionBoundaryInputs`: the adjacent-moved side is supplied
by reflected-base avoidance, the moving/A-fiber inclusions, and the direct
`AFiberCardinality38Boundary`, rather than by a criterion that already contains
the full residual-contribution equation.
-/

namespace Moore57

open Finset

noncomputable section

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instD19FinalCharacterAFiberBoundaryPFintype
    (coords : AFiberCoordinates.{u, uP} Γ) : Fintype coords.P :=
  coords.P_fintype

local instance instD19FinalCharacterAFiberBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Final direct-character/A-fiber boundary inputs.

The adjacent-moved side keeps only reflected avoidance, the canonical
moving/A-fiber inclusions, and the direct A-fiber cardinality boundary. -/
structure D19FinalCharacterAFiberBoundaryInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Split final character input: representation data plus fixed-count bound. -/
  character : D19FinalCharacterInputs h
  /-- Downstream orbit-base selection input. -/
  orbitInput : OrbitBaseSelectionInput h
  /-- Reflected-copy parameter. -/
  k : ZMod 19
  /-- Reflected selected bases avoid the selected orbit-family union. -/
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (orbitInput.base r) ∉
        orbitInput.orbitFamilyUnion
  /-- A coordinate system for the A-side fibers. -/
  coords : AFiberCoordinates.{u, uP} Γ
  /-- The A-side fiber indices used in the moving residual. -/
  indices : Finset (ZMod 19)
  /-- The moving residual complement is contained in the selected A-fiber union. -/
  moving_subset_aFiber :
    rotationOneMovingResidualPart h orbitInput k ⊆
      coords.fiberUnion indices
  /-- The selected A-fiber union is contained in the moving residual complement. -/
  aFiber_subset_moving :
    coords.fiberUnion indices ⊆
      rotationOneMovingResidualPart h orbitInput k
  /-- Packaged final-boundary A-fiber-side filtered cardinality statement. -/
  aFiberCardinality :
    AFiberCardinality38Boundary h coords indices

namespace D19FinalCharacterAFiberBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- The inclusion-form hypotheses recover the canonical moving/A-fiber
equality. -/
theorem moving_eq_aFiber
    (data : D19FinalCharacterAFiberBoundaryInputs h) :
    rotationOneMovingResidualPart h data.orbitInput data.k =
      data.coords.fiberUnion data.indices :=
  Finset.Subset.antisymm
    data.moving_subset_aFiber
    data.aFiber_subset_moving

/-- Build the existing split-avoidance witness from the thin A-fiber boundary.

The residual contribution is derived here from the fixed-residual zero theorem
and the direct `AFiberCardinality38Boundary` field. -/
noncomputable def toAvoidanceSplit38Witness
    (data : D19FinalCharacterAFiberBoundaryInputs h) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h data.orbitInput where
  k := data.k
  reflection_not_mem_orbitFamilyUnion :=
    data.reflection_not_mem_orbitFamilyUnion
  fixedPart := rotationOneFixedResidualPart h data.orbitInput data.k
  aPart := data.coords.fiberUnion data.indices
  parts_disjoint := by
    rw [Finset.disjoint_left]
    intro y hyFixed hyAFiber
    exact Finset.disjoint_left.mp
      (rotationOneFixedResidualPart_disjoint_movingResidualPart
        h data.orbitInput data.k)
      hyFixed
      (data.aFiber_subset_moving hyAFiber)
  residual_eq := by
    rw [reflectionCopyResidual_eq_rotationOneFixed_union_moving
      h data.orbitInput data.k, data.moving_eq_aFiber]
  residual_contribution := by
    intro d hd
    have hfixed :
        ((rotationOneFixedResidualPart h data.orbitInput data.k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card = 0 :=
      rotationOneFixedResidualPart_filter_adjacent_rotation_card_eq_zero
        h data.orbitInput data.k d hd
    have haFiber :
        ((data.coords.fiberUnion data.indices).filter fun y =>
          Γ.Adj y (h.rotation d y)).card = 38 := by
      simpa [fixedAFiberAFiberCard] using
        data.aFiberCardinality.card_eq_thirtyEight d hd
    simp [hfixed, haFiber]

/-- Forget the direct-character/A-fiber boundary presentation down to the
final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalCharacterAFiberBoundaryInputs h) :
    D19FinalInputs h where
  character := data.character
  orbitBase := data.orbitInput.toWitness
  fixedOrAContribution := fixedOrAContribution38
  fixed_or_A_contribution := by
    intro d hd
    rfl
  adjacentMovedDecomposition := by
    simpa [OrbitBaseSelectionInput.toWitness] using
      data.toAvoidanceSplit38Witness.toDecomposition

/-- Direct-character/A-fiber boundary final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
      (D19FinalCharacterAFiberBoundaryInputs.{u, uP} h) := by
  rintro ⟨data⟩
  exact D19FinalInputs.not_nonempty h ⟨data.toD19FinalInputs⟩

/-- Constructor from residual containment for rotation-equivariant A-fiber
coordinates.  Equivariance supplies the moving-side inclusion. -/
noncomputable def of_equivariantAFiberResidual
    (character : D19FinalCharacterInputs h)
    (orbitInput : OrbitBaseSelectionInput h)
    (k : ZMod 19)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (orbitInput.base r) ∉
          orbitInput.orbitFamilyUnion)
    (coords : AFiberCoordinates.{u, uP} Γ)
    (indices : Finset (ZMod 19))
    (rot : AFiberRotationEquivariance h coords)
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h orbitInput k ⊆
        coords.fiberUnion indices)
    (aFiber_subset_residual :
      coords.fiberUnion indices ⊆
        reflectionCopyResidual h orbitInput.base k)
    (aFiberCardinality : AFiberCardinality38Boundary h coords indices) :
    D19FinalCharacterAFiberBoundaryInputs h where
  character := character
  orbitInput := orbitInput
  k := k
  reflection_not_mem_orbitFamilyUnion :=
    reflection_not_mem_orbitFamilyUnion
  coords := coords
  indices := indices
  moving_subset_aFiber := moving_subset_aFiber
  aFiber_subset_moving :=
    rot.fiberUnion_subset_movingResidual_of_subset_residual
      orbitInput k indices aFiber_subset_residual
  aFiberCardinality := aFiberCardinality

/-- Constructor from residual containment and explicit matching-equation
filter sums for rotation-equivariant A-fiber coordinates.  The matching sums
build the A-fiber cardinality boundary, and equivariance supplies the
moving-side inclusion. -/
noncomputable def of_equivariantAFiberResidualMatchingEquationSum
    (character : D19FinalCharacterInputs h)
    (orbitInput : OrbitBaseSelectionInput h)
    (k : ZMod 19)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (orbitInput.base r) ∉
          orbitInput.orbitFamilyUnion)
    (coords : AFiberCoordinates.{u, uP} Γ)
    (indices : Finset (ZMod 19))
    (rot : AFiberRotationEquivariance h coords)
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h orbitInput k ⊆
        coords.fiberUnion indices)
    (aFiber_subset_residual :
      coords.fiberUnion indices ⊆
        reflectionCopyResidual h orbitInput.base k)
    (matchingEquationSum :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∑ i ∈ indices,
          ((Finset.univ : Finset coords.P).filter fun p =>
            AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
                (index_ne_add_of_ne_zero hd) p =
              rot.coordPerm d i p).card = 38) :
    D19FinalCharacterAFiberBoundaryInputs h :=
  of_equivariantAFiberResidual
    character orbitInput k reflection_not_mem_orbitFamilyUnion
    coords indices rot moving_subset_aFiber aFiber_subset_residual
    (AFiberCardinality38Boundary.of_matchingEquationFilterCardSum
      rot matchingEquationSum)

/-- Constructor from a residual split equality, rotation equivariance, and
explicit matching-equation filter sums.  The split equality supplies the
forward moving/A-fiber inclusion, equivariance supplies the reverse inclusion,
and the matching sums supply the A-fiber cardinality boundary. -/
noncomputable def of_residualSplitMatchingEquationSum
    (character : D19FinalCharacterInputs h)
    (orbitInput : OrbitBaseSelectionInput h)
    (k : ZMod 19)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (orbitInput.base r) ∉
          orbitInput.orbitFamilyUnion)
    (coords : AFiberCoordinates.{u, uP} Γ)
    (indices : Finset (ZMod 19))
    (rot : AFiberRotationEquivariance h coords)
    (residual_eq_fixed_union :
      reflectionCopyResidual h orbitInput.base k =
        rotationOneFixedResidualPart h orbitInput k ∪
          coords.fiberUnion indices)
    (matchingEquationSum :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∑ i ∈ indices,
          ((Finset.univ : Finset coords.P).filter fun p =>
            AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
                (index_ne_add_of_ne_zero hd) p =
              rot.coordPerm d i p).card = 38) :
    D19FinalCharacterAFiberBoundaryInputs h :=
  of_equivariantAFiberResidualMatchingEquationSum
    character orbitInput k reflection_not_mem_orbitFamilyUnion
    coords indices rot
    (rotationOneMovingResidualPart_subset_of_residual_eq_fixed_union
      residual_eq_fixed_union)
    (aFiber_subset_residual_of_residual_eq_fixed_union
      residual_eq_fixed_union)
    matchingEquationSum

/-- Constructor from a residual split equality, rotation equivariance, and the
local statement that each selected matching equation has exactly two
solutions. -/
noncomputable def of_residualSplitMatchingEquationTwo
    (character : D19FinalCharacterInputs h)
    (orbitInput : OrbitBaseSelectionInput h)
    (k : ZMod 19)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (orbitInput.base r) ∉
          orbitInput.orbitFamilyUnion)
    (coords : AFiberCoordinates.{u, uP} Γ)
    (indices : Finset (ZMod 19))
    (rot : AFiberRotationEquivariance h coords)
    (residual_eq_fixed_union :
      reflectionCopyResidual h orbitInput.base k =
        rotationOneFixedResidualPart h orbitInput k ∪
          coords.fiberUnion indices)
    (indices_card : indices.card = 19)
    (matchingEquationCardTwo :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        i ∈ indices →
          ((Finset.univ : Finset coords.P).filter fun p =>
            AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
                (index_ne_add_of_ne_zero hd) p =
              rot.coordPerm d i p).card = 2) :
    D19FinalCharacterAFiberBoundaryInputs h :=
  of_equivariantAFiberResidual
    character orbitInput k reflection_not_mem_orbitFamilyUnion
    coords indices rot
    (rotationOneMovingResidualPart_subset_of_residual_eq_fixed_union
      residual_eq_fixed_union)
    (aFiber_subset_residual_of_residual_eq_fixed_union
      residual_eq_fixed_union)
    (AFiberCardinality38Boundary.of_matchingEquationFilterCard_eq_two
      rot indices_card matchingEquationCardTwo)

/-- Constructor specialized to moved-branch rotation-orbit A-fiber
coordinates.  The moved-branch constructor gives the required equivariance. -/
noncomputable def of_rotationOrbitOfMovedAFiberResidual
    (character : D19FinalCharacterInputs h)
    (orbitInput : OrbitBaseSelectionInput h)
    (k : ZMod 19)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (orbitInput.base r) ∉
          orbitInput.orbitFamilyUnion)
    (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d0 : ZMod 19} (hd0 : d0 ≠ 0)
    (hmove : h.rotation d0 a0 ≠ a0)
    (indices : Finset (ZMod 19))
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h orbitInput k ⊆
        (AFiberCoordinates.ofRotationOrbitOfMoved
          h u a0 hu hub0 hd0 hmove).fiberUnion indices)
    (aFiber_subset_residual :
      (AFiberCoordinates.ofRotationOrbitOfMoved
          h u a0 hu hub0 hd0 hmove).fiberUnion indices ⊆
        reflectionCopyResidual h orbitInput.base k)
    (aFiberCardinality :
      AFiberCardinality38Boundary h
        (AFiberCoordinates.ofRotationOrbitOfMoved
          h u a0 hu hub0 hd0 hmove)
        indices) :
    D19FinalCharacterAFiberBoundaryInputs.{u, u} h where
  character := character
  orbitInput := orbitInput
  k := k
  reflection_not_mem_orbitFamilyUnion :=
    reflection_not_mem_orbitFamilyUnion
  coords :=
    AFiberCoordinates.ofRotationOrbitOfMoved
      h u a0 hu hub0 hd0 hmove
  indices := indices
  moving_subset_aFiber := moving_subset_aFiber
  aFiber_subset_moving :=
    AFiberCoordinates.ofRotationOrbitOfMoved_fiberUnion_subset_movingResidual_of_subset_residual
      h u a0 hu hub0 hd0 hmove orbitInput k indices
      aFiber_subset_residual
  aFiberCardinality := aFiberCardinality

/-- Moved-branch rotation-orbit constructor from residual containment and
explicit matching-equation filter sums. -/
noncomputable def of_rotationOrbitOfMovedAFiberResidualMatchingEquationSum
    (character : D19FinalCharacterInputs h)
    (orbitInput : OrbitBaseSelectionInput h)
    (k : ZMod 19)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (orbitInput.base r) ∉
          orbitInput.orbitFamilyUnion)
    (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d0 : ZMod 19} (hd0 : d0 ≠ 0)
    (hmove : h.rotation d0 a0 ≠ a0)
    (indices : Finset (ZMod 19))
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h orbitInput k ⊆
        (AFiberCoordinates.ofRotationOrbitOfMoved
          h u a0 hu hub0 hd0 hmove).fiberUnion indices)
    (aFiber_subset_residual :
      (AFiberCoordinates.ofRotationOrbitOfMoved
          h u a0 hu hub0 hd0 hmove).fiberUnion indices ⊆
        reflectionCopyResidual h orbitInput.base k)
    (matchingEquationSum :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∑ i ∈ indices,
          ((Finset.univ :
              Finset
                (AFiberCoordinates.ofRotationOrbitOfMoved
                  h u a0 hu hub0 hd0 hmove).P).filter fun p =>
            AFiberCoordinates.matchingEquiv h.isMoore
                (AFiberCoordinates.ofRotationOrbitOfMoved
                  h u a0 hu hub0 hd0 hmove)
                i (i + d) (index_ne_add_of_ne_zero hd) p =
              (AFiberCoordinates.ofRotationOrbitOfMoved_rotationEquivariance
                h u a0 hu hub0 hd0 hmove).coordPerm d i p).card = 38) :
    D19FinalCharacterAFiberBoundaryInputs.{u, u} h :=
  of_equivariantAFiberResidualMatchingEquationSum
    character orbitInput k reflection_not_mem_orbitFamilyUnion
    (AFiberCoordinates.ofRotationOrbitOfMoved h u a0 hu hub0 hd0 hmove)
    indices
    (AFiberCoordinates.ofRotationOrbitOfMoved_rotationEquivariance
      h u a0 hu hub0 hd0 hmove)
    moving_subset_aFiber aFiber_subset_residual matchingEquationSum

/-- Constructor from the equality-form canonical A-fiber criterion. -/
noncomputable def of_canonicalAFiberCriteria
    (character : D19FinalCharacterInputs h)
    (orbitInput : OrbitBaseSelectionInput h)
    (adjacentMoved :
      AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
        h orbitInput) :
    D19FinalCharacterAFiberBoundaryInputs h where
  character := character
  orbitInput := orbitInput
  k := adjacentMoved.k
  reflection_not_mem_orbitFamilyUnion :=
    adjacentMoved.reflection_not_mem_orbitFamilyUnion
  coords := adjacentMoved.coords
  indices := adjacentMoved.indices
  moving_subset_aFiber := adjacentMoved.moving_subset_aFiber
  aFiber_subset_moving := adjacentMoved.aFiber_subset_moving
  aFiberCardinality :=
    adjacentMoved.toAFiberCardinality38Boundary

/-- Constructor from the inclusion-form canonical A-fiber criterion. -/
noncomputable def of_canonicalAFiberInclusionCriteria
    (character : D19FinalCharacterInputs h)
    (orbitInput : OrbitBaseSelectionInput h)
    (adjacentMoved :
      AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness.{u, uP}
        h orbitInput) :
    D19FinalCharacterAFiberBoundaryInputs h where
  character := character
  orbitInput := orbitInput
  k := adjacentMoved.k
  reflection_not_mem_orbitFamilyUnion :=
    adjacentMoved.reflection_not_mem_orbitFamilyUnion
  coords := adjacentMoved.coords
  indices := adjacentMoved.indices
  moving_subset_aFiber := adjacentMoved.moving_subset_aFiber
  aFiber_subset_moving := adjacentMoved.aFiber_subset_moving
  aFiberCardinality :=
    adjacentMoved.toAFiberCardinality38Boundary

end D19FinalCharacterAFiberBoundaryInputs

end

end Moore57
