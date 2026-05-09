import Moore57.BranchOrbitABCLeanAwareFinalBoundary
import Moore57.ReflectionFixedStarFromActionBoundary

/-!
# Action-level lean-aware final boundary

This file packages the current remaining inputs in an action-level form:
reflection fixed-neighbor star counts, the two center-identification inputs for
the chosen labeling, reference-solution fixedness, and the two positive
`S_h ∩ E` case exclusions.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instActionLevelFinalBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instActionLevelFinalBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Current action-level package of the remaining branch/midpoint inputs. -/
structure BranchOrbitABCActionLevelFinalBoundary
    (h : D19ActsOnMoore57 V Γ) where
  starCounts : ReflectionFixedNeighborStarCounts h
  labeling : BranchOrbitABCReflectionLabeling h
  middle :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarMiddleBoundary
      starCounts.toReflectionFixedStarBoundary labeling
  aFixing :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
      starCounts.toReflectionFixedStarBoundary labeling
  referenceSolutionSupportCompl :
    BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
      labeling
  exceptionDoubling :
    BranchOrbitABCReflectionLabeling.MidpointExceptionDoublingBoundary labeling
  cardOneBase : ZMod 19
  cardOneBase_ne_zero : cardOneBase ≠ 0
  cardOneBase_ne_one :
    (labeling.midpointExceptionAFixingSupportIntersection
      cardOneBase cardOneBase_ne_zero).card ≠ 1
  not_all_support_subset_exception :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ¬ labeling.aFiberReflectionSupport ⊆
        labeling.midpointExceptionSet (midpointOf d) (midpointOf_ne_zero hd)

namespace BranchOrbitABCActionLevelFinalBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the action-level package to the lean-aware fixed-star final package. -/
noncomputable def toLeanAwareFixedStarFinalBoundary
    (boundary : BranchOrbitABCActionLevelFinalBoundary h) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      boundary.starCounts.toReflectionFixedStarBoundary boundary.labeling :=
  BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary.of_aFixingCenter_doubling_notAllSupport
    boundary.middle boundary.aFixing
    boundary.referenceSolutionSupportCompl
    boundary.exceptionDoubling
    boundary.cardOneBase_ne_zero boundary.cardOneBase_ne_one
    boundary.not_all_support_subset_exception

end BranchOrbitABCActionLevelFinalBoundary

/-- No action-level final package can coexist with the representation component
boundary. -/
theorem no_D19_actionLevelFinalBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        Nonempty (BranchOrbitABCActionLevelFinalBoundary h) := by
  rintro ⟨representationComponents, ⟨boundary⟩⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨representationComponents,
      boundary.starCounts.toReflectionFixedStarBoundary,
      boundary.labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

/-- Character-class version of `no_D19_actionLevelFinalBoundary`. -/
theorem no_D19_characterClassBoundary_actionLevelFinalBoundary
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
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) := by
  rintro ⟨boundary⟩
  exact no_D19_characterClassBoundary_leanAwareFixedStarFinalBoundary
    h ρ alpha beta gamma finrank_eq trace_eq_character characterClass
    reflection minus8_trivial_nonneg minus8_sign_nonneg
    ⟨boundary.starCounts.toReflectionFixedStarBoundary,
      boundary.labeling,
      boundary.toLeanAwareFixedStarFinalBoundary⟩

end

end Moore57
