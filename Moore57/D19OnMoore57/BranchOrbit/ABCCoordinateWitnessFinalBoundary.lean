import Moore57.D19OnMoore57.BranchOrbit.ABCSetInvariantWitnessBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionEquationInvariantBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionEndpointPointwiseBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionDoublingVertexPullbackBoundary

/-!
# Coordinate witness final boundary

This file packages the current coordinate-level midpoint-exception inputs and
wires them through the existing action-level set-invariant witness boundary to
the final contradiction.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instCoordinateWitnessFinalBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instCoordinateWitnessFinalBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Action-level package of the smaller coordinate-level inputs sufficient for
the existing finite midpoint-exception contradiction boundary. -/
structure BranchOrbitABCActionLevelCoordinateWitnessBoundary
    (h : D19ActsOnMoore57 V Γ) where
  starCounts : ReflectionFixedNeighborStarCounts h
  labeling : BranchOrbitABCReflectionLabeling h
  middle :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarMiddleBoundary
      starCounts.toReflectionFixedStarBoundary labeling
  aFixing :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
      starCounts.toReflectionFixedStarBoundary labeling
  referenceMatching :
    BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary labeling
  doublingVertexPullback :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingMiddleVertexFixedPullbackBoundary
      labeling
  equationInvariant :
    BranchOrbitABCReflectionLabeling.MidpointEquationSetAFixingInvariantBoundary
      labeling
  endpointPointwiseNonadj :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
      labeling

namespace BranchOrbitABCActionLevelCoordinateWitnessBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Promote the coordinate-level witness package to the existing set-invariant
action-level package. -/
def toActionLevelSetInvariantWitnessBoundary
    (boundary : BranchOrbitABCActionLevelCoordinateWitnessBoundary h) :
    BranchOrbitABCActionLevelSetInvariantWitnessBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  doublingFixedPullback :=
    boundary.doublingVertexPullback
      |>.toMidpointExceptionDoublingMiddleFixedPullbackBoundary
  exceptionSetInvariant :=
    boundary.equationInvariant
      |>.toMidpointExceptionSetAFixingInvariantBoundary
        boundary.referenceMatching.criterion
  endpointNonadjWitness :=
    boundary.endpointPointwiseNonadj
      |>.toMidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary
        boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary

/-- Promote the coordinate-level witness package to the existing witness
package with intersection invariance. -/
def toActionLevelWitnessBoundary
    (boundary : BranchOrbitABCActionLevelCoordinateWitnessBoundary h) :
    BranchOrbitABCActionLevelWitnessBoundary h :=
  boundary.toActionLevelSetInvariantWitnessBoundary
    |>.toActionLevelWitnessBoundary

/-- Convert the coordinate-level package to the Lean-aware fixed-star final
boundary consumed by the final contradiction. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : BranchOrbitABCActionLevelCoordinateWitnessBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelSetInvariantWitnessBoundary
    |>.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCActionLevelCoordinateWitnessBoundary

/-- No action-level coordinate witness package can coexist with the
representation component boundary. -/
theorem no_D19_actionLevelCoordinateWitnessBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty (BranchOrbitABCActionLevelCoordinateWitnessBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨representationComponents,
      boundary.starCounts.toReflectionFixedStarBoundary,
      boundary.labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

/-- Character-class version of
`no_D19_actionLevelCoordinateWitnessBoundary`. -/
theorem no_D19_characterClassBoundary_actionLevelCoordinateWitnessBoundary
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (characterClass : D19CharacterClassBoundary ρ alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    ¬ Nonempty (BranchOrbitABCActionLevelCoordinateWitnessBoundary h) := by
  rintro ⟨boundary⟩
  exact no_D19_characterClassBoundary_leanAwareFixedStarFinalBoundary
    h ρ alpha beta gamma finrank_eq trace_eq_character characterClass
    reflection minus8_trivial_nonneg minus8_sign_nonneg
    ⟨boundary.starCounts.toReflectionFixedStarBoundary,
      boundary.labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

end

end Moore57
