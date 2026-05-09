import Moore57.D19FinalExposedHybridBoundary
import Moore57.AFiberHybridBoundaryFromCriteria
import Moore57.OrbitBaseSelectionCanonicalCarrierCardinality

/-!
# Final D19 inputs from low-level input criteria

This file is a final entry point from the downstream orbit-base input and the
canonical adjacent-moved A-fiber criterion.  It fills the exposed hybrid
boundary fields by promoting the orbit input to the canonical carrier witness
and extracting the inclusion and A-fiber cardinality boundary data from the
canonical criterion.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final-boundary input package whose orbit-base and adjacent-moved sides are
given in the lower-level criterion forms. -/
structure D19FinalInputCriterionBoundaryInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Final-boundary trace core for the representation-character side. -/
  traceCore : D19ActsOnMoore57.TraceCoreCharacterBoundary h
  /-- Packaged final-boundary fixed-count assumption for rotation by `1`. -/
  fixedBound : D19ActsOnMoore57.RotationOneFixedBoundBoundaryInput h
  /-- Downstream orbit-base selection input. -/
  orbitInput : OrbitBaseSelectionInput h
  /-- Canonical adjacent-moved A-fiber criterion over the selected orbit input. -/
  adjacentMoved :
    AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
      h orbitInput

namespace D19FinalInputCriterionBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Promote the low-level orbit input to the canonical carrier expected by the
exposed hybrid boundary. -/
noncomputable def orbitBase
    (data : D19FinalInputCriterionBoundaryInputs h) :
    OrbitBaseSelectionCanonicalCarrierWitness h :=
  data.orbitInput.toCanonicalCarrierWitness

/-- The adjacent-moved reflection-avoidance field, restated for the canonical
carrier promoted from the low-level orbit input. -/
noncomputable def reflectedAvoidance
    (data : D19FinalInputCriterionBoundaryInputs h) :
    OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h data.orbitBase
    where
  k := data.adjacentMoved.k
  reflected_base_not_mem_orbitFamilyUnion := by
    intro r
    simpa [orbitBase, OrbitBaseSelectionInput.orbitFamilyUnion] using
      data.adjacentMoved.reflection_not_mem_orbitFamilyUnion r

/-- Fill the exposed hybrid final-boundary record from the low-level orbit
input and canonical adjacent-moved criterion. -/
noncomputable def toD19FinalExposedHybridBoundaryInputs
    (data : D19FinalInputCriterionBoundaryInputs h) :
    D19FinalExposedHybridBoundaryInputs.{u, uP} h where
  traceCore := data.traceCore
  fixedBound := data.fixedBound
  orbitBase := data.orbitBase
  reflectedAvoidance := data.reflectedAvoidance
  coords := data.adjacentMoved.coords
  indices := data.adjacentMoved.indices
  moving_subset_aFiber := by
    simpa [orbitBase, reflectedAvoidance, rotationOneMovingResidualPart,
      rotationOneFixedResidualPart] using
      data.adjacentMoved.moving_subset_aFiber
  aFiber_subset_moving := by
    simpa [orbitBase, reflectedAvoidance, rotationOneMovingResidualPart,
      rotationOneFixedResidualPart] using
      data.adjacentMoved.aFiber_subset_moving
  aFiberCardinality :=
    data.adjacentMoved.toAFiberCardinality38Boundary

/-- Forget the low-level criterion-boundary presentation down to the final
input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalInputCriterionBoundaryInputs h) :
    D19FinalInputs h :=
  data.toD19FinalExposedHybridBoundaryInputs.toD19FinalInputs

/-- Low-level criterion-boundary final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalInputCriterionBoundaryInputs.{u, uP} h) := by
  rintro ⟨data⟩
  exact D19FinalExposedHybridBoundaryInputs.not_nonempty h
    ⟨data.toD19FinalExposedHybridBoundaryInputs⟩

/-- Constructor from the inclusion-form canonical A-fiber criterion. -/
noncomputable def of_canonicalAFiberInclusionCriteria
    (traceCore : D19ActsOnMoore57.TraceCoreCharacterBoundary h)
    (fixedBound : D19ActsOnMoore57.RotationOneFixedBoundBoundaryInput h)
    (orbitInput : OrbitBaseSelectionInput h)
    (adjacentMoved :
      AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness.{u, uP}
        h orbitInput) :
    D19FinalInputCriterionBoundaryInputs h where
  traceCore := traceCore
  fixedBound := fixedBound
  orbitInput := orbitInput
  adjacentMoved := adjacentMoved.toCanonicalAFiberCriteria38Witness

end D19FinalInputCriterionBoundaryInputs

end Moore57
