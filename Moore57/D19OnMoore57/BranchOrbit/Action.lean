import Moore57.D19OnMoore57.BranchOrbit.ABCLeanAwareFinalBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCaseLocalObstruction
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionDoublingGeometry
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCaseWitnessBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionDoublingCoordinateBoundary
import Moore57.D19OnMoore57.Reflection.FixedStarFromActionBoundary

/-!
# Action-level boundary refinement chain

This file unifies three thematic action-level packages and their no-go
theorems:

* **Case** (`BranchOrbitABCActionLevelCaseBoundary`): the action-level
  endpoint reached once the finite `S_(d/2) ∩ E` case analysis has been
  assembled, with the
  `MidpointExceptionAFixingSupportCaseBoundary` already provided.
* **Local obstruction** (`BranchOrbitABCActionLevelLocalObstructionBoundary`):
  the lower-level local obstruction inputs (doubling geometry,
  singleton-fixed, no-all-endpoint-adjacent) sufficient to assemble the
  case package and hence the existing Lean-aware final boundary.
* **Witness** (`BranchOrbitABCActionLevelWitnessBoundary`): the newest
  witness/pullback inputs (intersection invariance and endpoint
  non-adjacency witnesses, plus the doubling fixed-pullback) sufficient
  for the existing finite midpoint-exception case boundary.

Both `LocalObstruction` and `Witness` route through `Case` to reach the
existing Lean-aware fixed-star final boundary.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instActionLevelPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instActionLevelDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-! ## Case-level action package -/

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

/-! ## Local obstruction action package -/

/-- Action-level package of the local obstruction inputs that are sufficient
for the existing Lean-aware final boundary. -/
structure BranchOrbitABCActionLevelLocalObstructionBoundary
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
  exceptionDoublingGeometry :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingGeometryBoundary
      labeling
  singletonFixed :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
      labeling
  noAllEndpointAdj :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      labeling

namespace BranchOrbitABCActionLevelLocalObstructionBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The geometric doubling input in the local obstruction package supplies the
existing finite-set doubling boundary when needed by downstream APIs. -/
def toMidpointExceptionDoublingBoundary
    (boundary : BranchOrbitABCActionLevelLocalObstructionBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingBoundary
      boundary.labeling :=
  boundary.exceptionDoublingGeometry.toMidpointExceptionDoublingBoundary

/-- Forget the action-level fields not needed for the local midpoint-exception
case split. -/
def toMidpointExceptionAFixingSupportLocalObstructionBoundary
    (boundary : BranchOrbitABCActionLevelLocalObstructionBoundary h) :
    MidpointExceptionAFixingSupportLocalObstructionBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling where
  aFixing := boundary.aFixing
  singletonFixed := boundary.singletonFixed
  noAllEndpointAdj := boundary.noAllEndpointAdj

/-- Convert the local obstruction package to the case-level action package. -/
noncomputable def toActionLevelCaseBoundary
    (boundary : BranchOrbitABCActionLevelLocalObstructionBoundary h) :
    BranchOrbitABCActionLevelCaseBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  middle := boundary.middle
  aFixing := boundary.aFixing
  referenceMatching := boundary.referenceMatching
  caseBoundary :=
    boundary.toMidpointExceptionAFixingSupportLocalObstructionBoundary
      |>.toMidpointExceptionAFixingSupportCaseBoundary

/-- Convert the local obstruction package to the Lean-aware fixed-star final
package consumed by the final contradiction. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : BranchOrbitABCActionLevelLocalObstructionBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  boundary.toActionLevelCaseBoundary.toLeanAwareFixedStarFinalBoundary

end BranchOrbitABCActionLevelLocalObstructionBoundary

/-! ## Witness action package -/

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

/-! ## No-go theorems -/

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

/-- No action-level local obstruction package can coexist with the
representation component boundary. -/
theorem no_D19_actionLevelLocalObstructionBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨representationComponents,
      boundary.starCounts.toReflectionFixedStarBoundary,
      boundary.labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

/-- Character-class version of
`no_D19_actionLevelLocalObstructionBoundary`. -/
theorem no_D19_characterClassBoundary_actionLevelLocalObstructionBoundary
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
    ¬ Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) := by
  rintro ⟨boundary⟩
  exact no_D19_characterClassBoundary_leanAwareFixedStarFinalBoundary
    h ρ alpha beta gamma finrank_eq trace_eq_character characterClass
    reflection minus8_trivial_nonneg minus8_sign_nonneg
    ⟨boundary.starCounts.toReflectionFixedStarBoundary,
      boundary.labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

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
