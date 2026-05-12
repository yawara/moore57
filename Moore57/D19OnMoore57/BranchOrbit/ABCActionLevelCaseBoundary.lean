import Moore57.D19OnMoore57.BranchOrbit.ABCLeanAwareFinalBoundary
import Moore57.D19OnMoore57.Reflection.FixedStarFromActionBoundary

/-!
# Action-level boundary using the midpoint exception case package

This file records the action-level endpoint reached once the finite
`S_(d/2) ∩ E` case analysis has been completed.  Compared with
`BranchOrbitABCActionLevelFinalBoundary`, this package takes the already
assembled `MidpointExceptionAFixingSupportCaseBoundary` directly, so lower
geometric inputs can feed the final contradiction without carrying the
intermediate doubling/card-one/card-two witnesses again.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instActionLevelCaseBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instActionLevelCaseBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Action-level package after the midpoint-exception cardinality case
analysis has been assembled. -/
structure BranchOrbitABCActionLevelCaseBoundary
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
  caseBoundary :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportCaseBoundary
      labeling

namespace BranchOrbitABCActionLevelCaseBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the case-level action package to the lean-aware fixed-star final
package. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : BranchOrbitABCActionLevelCaseBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary.of_referenceMatching_aFixingCenter_cases
    boundary.middle boundary.aFixing boundary.referenceMatching
    boundary.caseBoundary

end BranchOrbitABCActionLevelCaseBoundary

/-- No case-level action package can coexist with the representation component
boundary. -/
theorem no_D19_actionLevelCaseBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty (BranchOrbitABCActionLevelCaseBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨representationComponents,
      boundary.starCounts.toReflectionFixedStarBoundary,
      boundary.labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

/-- Character-class version of `no_D19_actionLevelCaseBoundary`. -/
theorem no_D19_characterClassBoundary_actionLevelCaseBoundary
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
    ¬ Nonempty (BranchOrbitABCActionLevelCaseBoundary h) := by
  rintro ⟨boundary⟩
  exact no_D19_characterClassBoundary_leanAwareFixedStarFinalBoundary
    h ρ alpha beta gamma finrank_eq trace_eq_character characterClass
    reflection minus8_trivial_nonneg minus8_sign_nonneg
    ⟨boundary.starCounts.toReflectionFixedStarBoundary,
      boundary.labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

end

end Moore57
