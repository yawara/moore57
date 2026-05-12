import Moore57.D19OnMoore57.CanonicalCarrier.CanonicalCarrierReflectedAvoidance
import Moore57.D19OnMoore57.Final.D19FinalRepresentationUpperBoundAvoidanceSemantic

/-!
# Canonical carrier reflected avoidance from criteria

This file turns existing reflected-avoidance criteria back into the canonical
carrier reflected-avoidance boundary.  The conversions only use criteria that
already carry the reflection parameter `k`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace OrbitBaseSelectionCanonicalCarrierReflectedAvoidance

variable {h : D19ActsOnMoore57 V Γ}
variable {w : OrbitBaseSelectionCanonicalCarrierWitness h}

/-- Carrier-form reflected avoidance for the induced carrier is the same
canonical reflected avoidance, with the induced carrier normalized by `simp`. -/
def ofCarrierReflectedAvoidance
    (a : OrbitBaseSelectionCarrierReflectedAvoidance h w.toCarrierWitness) :
    OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w where
  k := a.k
  reflected_base_not_mem_orbitFamilyUnion := by
    intro r
    simpa using a.reflected_base_not_mem_carrier r

@[simp] theorem ofCarrierReflectedAvoidance_k
    (a : OrbitBaseSelectionCarrierReflectedAvoidance h w.toCarrierWitness) :
    (ofCarrierReflectedAvoidance (w := w) a).k = a.k := by
  rfl

/-- The compact avoidance criterion over the input induced by the canonical
carrier gives canonical reflected avoidance. -/
def ofAvoidanceComplementResidual38Witness
    (a : AdjacentMovedReflectionAvoidanceComplementResidual38Witness
      h w.toCarrierWitness.toInput) :
    OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w where
  k := a.k
  reflected_base_not_mem_orbitFamilyUnion := by
    intro r
    simpa using a.reflection_not_mem_orbitFamilyUnion r

@[simp] theorem ofAvoidanceComplementResidual38Witness_k
    (a : AdjacentMovedReflectionAvoidanceComplementResidual38Witness
      h w.toCarrierWitness.toInput) :
    (ofAvoidanceComplementResidual38Witness (w := w) a).k = a.k := by
  rfl

/-- The split avoidance criterion over the input induced by the canonical
carrier gives canonical reflected avoidance. -/
def ofAvoidanceSplit38Witness
    (a : AdjacentMovedReflectionAvoidanceSplit38Witness
      h w.toCarrierWitness.toInput) :
    OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w where
  k := a.k
  reflected_base_not_mem_orbitFamilyUnion := by
    intro r
    simpa using a.reflection_not_mem_orbitFamilyUnion r

@[simp] theorem ofAvoidanceSplit38Witness_k
    (a : AdjacentMovedReflectionAvoidanceSplit38Witness
      h w.toCarrierWitness.toInput) :
    (ofAvoidanceSplit38Witness (w := w) a).k = a.k := by
  rfl

/-- A semantic split-avoidance witness for the carrier induced by a canonical
carrier witness gives canonical reflected avoidance. -/
noncomputable def ofSemanticAvoidance
    (a : AdjacentMovedReflectionAvoidanceSemanticWitness h
      (OrbitBaseSelectionCarrierSemanticWitness.ofCarrierWitness
        w.toCarrierWitness)) :
    OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w where
  k := a.toSplitAvoidance.k
  reflected_base_not_mem_orbitFamilyUnion := by
    intro r
    simpa [OrbitBaseSelectionCarrierSemanticWitness.ofCarrierWitness,
      OrbitBaseSelectionCarrierSemanticWitness.toInput,
      OrbitBaseSelectionCarrierSemanticWitness.toCarrierWitness,
      AdjacentMovedReflectionAvoidanceSemanticWitness.toSplitAvoidance] using
      a.toSplitAvoidance.reflection_not_mem_orbitFamilyUnion r

@[simp] theorem ofSemanticAvoidance_k
    (a : AdjacentMovedReflectionAvoidanceSemanticWitness h
      (OrbitBaseSelectionCarrierSemanticWitness.ofCarrierWitness
        w.toCarrierWitness)) :
    (ofSemanticAvoidance (w := w) a).k = a.toSplitAvoidance.k := by
  rfl

end OrbitBaseSelectionCanonicalCarrierReflectedAvoidance

namespace OrbitBaseSelectionCarrierReflectedAvoidance

variable {h : D19ActsOnMoore57 V Γ}

/-- Method-form wrapper for recovering canonical reflected avoidance from
carrier-form reflected avoidance on the induced carrier. -/
def toCanonicalCarrierReflectedAvoidance
    {w : OrbitBaseSelectionCanonicalCarrierWitness h}
    (a : OrbitBaseSelectionCarrierReflectedAvoidance h w.toCarrierWitness) :
    OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w :=
  OrbitBaseSelectionCanonicalCarrierReflectedAvoidance.ofCarrierReflectedAvoidance a

end OrbitBaseSelectionCarrierReflectedAvoidance

namespace AdjacentMovedReflectionAvoidanceComplementResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}

/-- Method-form wrapper for recovering canonical reflected avoidance from a
compact avoidance criterion over the induced input. -/
def toCanonicalCarrierReflectedAvoidance
    {w : OrbitBaseSelectionCanonicalCarrierWitness h}
    (a : AdjacentMovedReflectionAvoidanceComplementResidual38Witness
      h w.toCarrierWitness.toInput) :
    OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w :=
  OrbitBaseSelectionCanonicalCarrierReflectedAvoidance.ofAvoidanceComplementResidual38Witness a

end AdjacentMovedReflectionAvoidanceComplementResidual38Witness

namespace AdjacentMovedReflectionAvoidanceSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}

/-- Method-form wrapper for recovering canonical reflected avoidance from a
split avoidance criterion over the induced input. -/
def toCanonicalCarrierReflectedAvoidance
    {w : OrbitBaseSelectionCanonicalCarrierWitness h}
    (a : AdjacentMovedReflectionAvoidanceSplit38Witness
      h w.toCarrierWitness.toInput) :
    OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w :=
  OrbitBaseSelectionCanonicalCarrierReflectedAvoidance.ofAvoidanceSplit38Witness a

end AdjacentMovedReflectionAvoidanceSplit38Witness

namespace AdjacentMovedReflectionAvoidanceSemanticWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Method-form wrapper for recovering canonical reflected avoidance from a
semantic avoidance witness over the induced carrier. -/
noncomputable def toCanonicalCarrierReflectedAvoidance
    {w : OrbitBaseSelectionCanonicalCarrierWitness h}
    (a : AdjacentMovedReflectionAvoidanceSemanticWitness h
      (OrbitBaseSelectionCarrierSemanticWitness.ofCarrierWitness
        w.toCarrierWitness)) :
    OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w :=
  OrbitBaseSelectionCanonicalCarrierReflectedAvoidance.ofSemanticAvoidance a

end AdjacentMovedReflectionAvoidanceSemanticWitness

end Moore57
