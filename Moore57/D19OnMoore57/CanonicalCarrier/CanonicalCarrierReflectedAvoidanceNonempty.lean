import Moore57.D19OnMoore57.CanonicalCarrier.CanonicalCarrierReflectedAvoidanceFromCriteria

/-!
# Nonempty-level canonical carrier reflected avoidance

This file records that canonical carrier reflected avoidance is only a
presentation of the existing carrier reflected-avoidance condition.  It also
lifts the existing avoidance-criteria constructors to `Nonempty` statements.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace OrbitBaseSelectionCanonicalCarrierReflectedAvoidance

variable {h : D19ActsOnMoore57 V Γ}
variable {w : OrbitBaseSelectionCanonicalCarrierWitness h}

/-- A canonical carrier reflected-avoidance presentation gives the existing
carrier reflected-avoidance presentation. -/
theorem nonempty_to_carrierReflectedAvoidance :
    Nonempty (OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w) →
      Nonempty
        (OrbitBaseSelectionCarrierReflectedAvoidance h w.toCarrierWitness) := by
  rintro ⟨a⟩
  exact ⟨a.toCarrierReflectedAvoidance⟩

/-- Carrier reflected avoidance for the induced carrier can be restated as
canonical carrier reflected avoidance. -/
theorem nonempty_of_carrierReflectedAvoidance :
    Nonempty
        (OrbitBaseSelectionCarrierReflectedAvoidance h w.toCarrierWitness) →
      Nonempty (OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w) := by
  rintro ⟨a⟩
  exact ⟨ofCarrierReflectedAvoidance a⟩

/-- Canonical carrier reflected avoidance is equivalent, at the `Nonempty`
level, to carrier reflected avoidance for the induced carrier witness. -/
theorem nonempty_iff_carrierReflectedAvoidance :
    Nonempty (OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w) ↔
      Nonempty
        (OrbitBaseSelectionCarrierReflectedAvoidance h w.toCarrierWitness) := by
  constructor
  · exact nonempty_to_carrierReflectedAvoidance
  · exact nonempty_of_carrierReflectedAvoidance

/-- The compact avoidance criterion over the induced input gives canonical
carrier reflected avoidance at the `Nonempty` level. -/
theorem nonempty_of_avoidanceComplementResidual38Witness :
    Nonempty
        (AdjacentMovedReflectionAvoidanceComplementResidual38Witness
          h w.toCarrierWitness.toInput) →
      Nonempty (OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w) := by
  rintro ⟨a⟩
  exact ⟨ofAvoidanceComplementResidual38Witness a⟩

/-- The split avoidance criterion over the induced input gives canonical
carrier reflected avoidance at the `Nonempty` level. -/
theorem nonempty_of_avoidanceSplit38Witness :
    Nonempty
        (AdjacentMovedReflectionAvoidanceSplit38Witness
          h w.toCarrierWitness.toInput) →
      Nonempty (OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w) := by
  rintro ⟨a⟩
  exact ⟨ofAvoidanceSplit38Witness a⟩

/-- A semantic avoidance witness for the induced carrier gives canonical
carrier reflected avoidance at the `Nonempty` level. -/
theorem nonempty_of_semanticAvoidance :
    Nonempty
        (AdjacentMovedReflectionAvoidanceSemanticWitness h
          (OrbitBaseSelectionCarrierSemanticWitness.ofCarrierWitness
            w.toCarrierWitness)) →
      Nonempty (OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w) := by
  rintro ⟨a⟩
  exact ⟨ofSemanticAvoidance a⟩

end OrbitBaseSelectionCanonicalCarrierReflectedAvoidance

end Moore57
