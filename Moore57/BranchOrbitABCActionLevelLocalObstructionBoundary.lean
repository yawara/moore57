import Moore57.BranchOrbitABCActionLevelCaseBoundary
import Moore57.BranchOrbitABCExceptionCaseLocalObstruction
import Moore57.BranchOrbitABCExceptionDoublingGeometry
import Moore57.ReflectionFixedStarFromActionBoundary

/-!
# Action-level local obstruction boundary

This file packages the lower-level local obstruction inputs into the existing
Lean-aware final contradiction boundary.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instActionLevelLocalObstructionBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instActionLevelLocalObstructionBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

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

end

end Moore57
