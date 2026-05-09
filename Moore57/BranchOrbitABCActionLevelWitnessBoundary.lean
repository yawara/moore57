import Moore57.BranchOrbitABCActionLevelCaseBoundary
import Moore57.BranchOrbitABCExceptionCaseWitnessBoundary
import Moore57.BranchOrbitABCExceptionDoublingCoordinateBoundary
import Moore57.ReflectionFixedStarFromActionBoundary

/-!
# Action-level witness boundary

This file packages the current witness-level midpoint-exception inputs at the
action level and wires them to the existing case-level final contradiction.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instActionLevelWitnessBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instActionLevelWitnessBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Action-level package of the newest witness/pullback inputs sufficient for
the existing finite midpoint-exception case boundary. -/
structure BranchOrbitABCActionLevelWitnessBoundary
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
  doublingFixedPullback :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingMiddleFixedPullbackBoundary
      labeling
  intersectionInvariant :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportIntersectionInvariantBoundary
      labeling
  endpointNonadjWitness :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary
      labeling

namespace BranchOrbitABCActionLevelWitnessBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The coordinate fixedness-pullback field supplies the existing finite-set
doubling boundary. -/
def toMidpointExceptionDoublingBoundary
    (boundary : BranchOrbitABCActionLevelWitnessBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingBoundary
      boundary.labeling :=
  boundary.doublingFixedPullback.toMidpointExceptionDoublingBoundary

/-- Forget the action-level fields not needed for the witness-level positive
cardinality case package. -/
def toMidpointExceptionAFixingSupportCaseWitnessBoundary
    (boundary : BranchOrbitABCActionLevelWitnessBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportCaseWitnessBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling where
  aFixing := boundary.aFixing
  intersectionInvariant := boundary.intersectionInvariant
  endpointNonadjWitness := boundary.endpointNonadjWitness

/-- Convert the witness-level package to the case-level action package. -/
noncomputable def toActionLevelCaseBoundary
    (boundary : BranchOrbitABCActionLevelWitnessBoundary h) :
    BranchOrbitABCActionLevelCaseBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  caseBoundary :=
    boundary.toMidpointExceptionAFixingSupportCaseWitnessBoundary
      |>.toMidpointExceptionAFixingSupportCaseBoundary

/-- Convert the witness-level action package to the Lean-aware fixed-star final
package consumed by the final contradiction. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : BranchOrbitABCActionLevelWitnessBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelCaseBoundary.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCActionLevelWitnessBoundary

/-- No action-level witness package can coexist with the representation
component boundary. -/
theorem no_D19_actionLevelWitnessBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty (BranchOrbitABCActionLevelWitnessBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨representationComponents,
      boundary.starCounts.toReflectionFixedStarBoundary,
      boundary.labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

/-- Character-class version of `no_D19_actionLevelWitnessBoundary`. -/
theorem no_D19_characterClassBoundary_actionLevelWitnessBoundary
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
    ¬ Nonempty (BranchOrbitABCActionLevelWitnessBoundary h) := by
  rintro ⟨boundary⟩
  exact no_D19_characterClassBoundary_leanAwareFixedStarFinalBoundary
    h ρ alpha beta gamma finrank_eq trace_eq_character characterClass
    reflection minus8_trivial_nonneg minus8_sign_nonneg
    ⟨boundary.starCounts.toReflectionFixedStarBoundary,
      boundary.labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

end

end Moore57
