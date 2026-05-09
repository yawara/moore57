import Moore57.D19FinalCharacterAFiberBoundary
import Moore57.D19FinalCharacterCriterionBoundary

/-!
# Public final-criterion nonexistence aliases

This file exposes stable top-level names for the current final-boundary
interfaces, without mentioning the older concrete-hypothesis interface in the
theorem conclusions.
-/

namespace Moore57

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Public alias: exposed hybrid final-boundary inputs cannot exist. -/
theorem no_D19_final_exposed_hybrid_boundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalExposedHybridBoundaryInputs.{u, uP} h) :=
  D19FinalExposedHybridBoundaryInputs.not_nonempty h

/-- Public alias: low-level input-criterion final-boundary inputs cannot exist. -/
theorem no_D19_final_input_criterion_boundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalInputCriterionBoundaryInputs.{u, uP} h) :=
  D19FinalInputCriterionBoundaryInputs.not_nonempty h

/-- Public alias: direct-character criterion-boundary inputs cannot exist. -/
theorem no_D19_final_character_criterion_boundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalCharacterCriterionBoundaryInputs.{u, uP} h) :=
  D19FinalCharacterCriterionBoundaryInputs.not_nonempty h

/-- Public alias: direct-character/A-fiber final-boundary inputs cannot exist. -/
theorem no_D19_final_character_aFiber_boundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalCharacterAFiberBoundaryInputs.{u, uP} h) :=
  D19FinalCharacterAFiberBoundaryInputs.not_nonempty h

end Moore57
