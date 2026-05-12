import Moore57.D19OnMoore57.Final.InputCriterionBoundary
import Moore57.D19OnMoore57.Trace.CoreRepresentationBoundary

/-!
# Final D19 inputs from final character inputs and low-level criteria

This file removes the raw trace-core and rotation-one fixed-bound wrappers
from the low-level criterion boundary.  The character side is supplied directly
as the existing `D19FinalCharacterInputs`, while the orbit and adjacent-moved
sides remain in the downstream criterion form.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final criterion-boundary inputs whose character side is already the final
split character package. -/
structure D19FinalCharacterCriterionBoundaryInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Split final character input: representation data plus fixed-count bound. -/
  character : D19FinalCharacterInputs h
  /-- Downstream orbit-base selection input. -/
  orbitInput : OrbitBaseSelectionInput h
  /-- Canonical adjacent-moved A-fiber criterion over the selected orbit input. -/
  adjacentMoved :
    AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
      h orbitInput

namespace D19FinalCharacterCriterionBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Repackage the direct final character input as the older trace-core plus
rotation-one fixed-bound criterion-boundary input. -/
noncomputable def toD19FinalInputCriterionBoundaryInputs
    (data : D19FinalCharacterCriterionBoundaryInputs h) :
    D19FinalInputCriterionBoundaryInputs.{u, uP} h where
  traceCore :=
    D19ActsOnMoore57.TraceCoreCharacterBoundary.ofD19RepresentationCharacterInput
      data.character.representation
  fixedBound :=
    D19ActsOnMoore57.RotationOneFixedBoundBoundaryInput.ofRotationFixedUpperBoundInput
      data.character.fixedUpperBound
  orbitInput := data.orbitInput
  adjacentMoved := data.adjacentMoved

/-- Forget the direct-character criterion boundary down to the final input
record, preserving the supplied `character` field. -/
noncomputable def toD19FinalInputs
    (data : D19FinalCharacterCriterionBoundaryInputs h) :
    D19FinalInputs h where
  character := data.character
  orbitBase := data.orbitInput.toWitness
  fixedOrAContribution := fixedOrAContribution38
  fixed_or_A_contribution := by
    intro d hd
    rfl
  adjacentMovedDecomposition := by
    simpa [OrbitBaseSelectionInput.toWitness] using
      data.adjacentMoved.toAvoidanceSplit38Witness.toDecomposition

/-- Direct-character criterion-boundary final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
      (D19FinalCharacterCriterionBoundaryInputs.{u, uP} h) := by
  rintro ⟨data⟩
  exact D19FinalInputs.not_nonempty h ⟨data.toD19FinalInputs⟩

/-- Constructor from the older trace-core plus rotation-one fixed-bound
criterion-boundary input. -/
noncomputable def ofD19FinalInputCriterionBoundaryInputs
    (data : D19FinalInputCriterionBoundaryInputs.{u, uP} h) :
    D19FinalCharacterCriterionBoundaryInputs h where
  character := data.traceCore.toD19FinalCharacterInputs data.fixedBound
  orbitInput := data.orbitInput
  adjacentMoved := data.adjacentMoved

/-- Constructor from the explicit trace-core and fixed-bound wrappers, together
with the low-level orbit and adjacent-moved criteria. -/
noncomputable def of_traceCore_fixedBound
    (traceCore : D19ActsOnMoore57.TraceCoreCharacterBoundary h)
    (fixedBound : D19ActsOnMoore57.RotationOneFixedBoundBoundaryInput h)
    (orbitInput : OrbitBaseSelectionInput h)
    (adjacentMoved :
      AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
        h orbitInput) :
    D19FinalCharacterCriterionBoundaryInputs h where
  character := traceCore.toD19FinalCharacterInputs fixedBound
  orbitInput := orbitInput
  adjacentMoved := adjacentMoved

/-- Any direct-character criterion boundary can be viewed as the older
trace-core/fixed-bound criterion boundary. -/
theorem nonempty_to_inputCriterionBoundary :
    Nonempty (D19FinalCharacterCriterionBoundaryInputs.{u, uP} h) →
      Nonempty (D19FinalInputCriterionBoundaryInputs.{u, uP} h) := by
  rintro ⟨data⟩
  exact ⟨data.toD19FinalInputCriterionBoundaryInputs⟩

/-- Any older trace-core/fixed-bound criterion boundary can be repackaged as a
direct-character criterion boundary. -/
theorem nonempty_of_inputCriterionBoundary :
    Nonempty (D19FinalInputCriterionBoundaryInputs.{u, uP} h) →
      Nonempty (D19FinalCharacterCriterionBoundaryInputs.{u, uP} h) := by
  rintro ⟨data⟩
  exact ⟨ofD19FinalInputCriterionBoundaryInputs data⟩

/-- The direct-character and older trace-core/fixed-bound criterion boundaries
are equivalent at the `Nonempty` level. -/
theorem nonempty_iff_inputCriterionBoundary :
    Nonempty (D19FinalCharacterCriterionBoundaryInputs.{u, uP} h) ↔
      Nonempty (D19FinalInputCriterionBoundaryInputs.{u, uP} h) := by
  constructor
  · exact nonempty_to_inputCriterionBoundary
  · exact nonempty_of_inputCriterionBoundary

end D19FinalCharacterCriterionBoundaryInputs

end Moore57
