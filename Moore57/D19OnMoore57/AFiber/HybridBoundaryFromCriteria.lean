import Moore57.D19OnMoore57.Final.TraceRotationOneHybridBoundary
import Moore57.D19OnMoore57.AFiber.CardinalityBoundary

/-!
# Hybrid A-fiber boundary constructors from canonical criteria

This file connects the canonical A-fiber criterion to the current hybrid final
boundary.  The canonical equality supplies the two required inclusions, and the
existing zero-contribution theorem for the canonical fixed residual side turns
the split residual contribution equation into the direct A-fiber filtered
cardinality statement `38`.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- The canonical moving/A-fiber equality gives the forward inclusion required
by the hybrid boundary. -/
theorem moving_subset_aFiber
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    rotationOneMovingResidualPart h input w.k ⊆
      w.coords.fiberUnion w.indices := by
  intro y hy
  simpa [w.moving_eq_aFiber] using hy

/-- The canonical moving/A-fiber equality gives the reverse inclusion required
by the hybrid boundary. -/
theorem aFiber_subset_moving
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    w.coords.fiberUnion w.indices ⊆
      rotationOneMovingResidualPart h input w.k := by
  intro y hy
  simpa [w.moving_eq_aFiber] using hy

/-- Convert the equality-form canonical criterion to the inclusion-form
canonical criterion. -/
noncomputable def toInclusionCriteria38Witness
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness h input
    where
  k := w.k
  reflection_not_mem_orbitFamilyUnion :=
    w.reflection_not_mem_orbitFamilyUnion
  coords := w.coords
  indices := w.indices
  moving_subset_aFiber := w.moving_subset_aFiber
  aFiber_subset_moving := w.aFiber_subset_moving
  residual_contribution := w.residual_contribution

/-- The canonical criterion implies the direct selected-A-fiber filtered
cardinality statement `38`, because the fixed residual side contributes zero. -/
theorem aFiber_card_eq_thirtyEight
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input)
    (d : ZMod 19) (hd : d ≠ 0) :
    fixedAFiberAFiberCard h (w.coords.fiberUnion w.indices) d = 38 := by
  have hfixed :
      ((rotationOneFixedResidualPart h input w.k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card = 0 :=
    rotationOneFixedResidualPart_filter_adjacent_rotation_card_eq_zero
      h input w.k d hd
  simpa [fixedAFiberAFiberCard, hfixed] using
    w.residual_contribution d hd

/-- Package the direct A-fiber cardinality statement extracted from the
canonical criterion as the final A-fiber-cardinality boundary record. -/
def toAFiberCardinality38Boundary
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    AFiberCardinality38Boundary h w.coords w.indices where
  card_eq_thirtyEight := w.aFiber_card_eq_thirtyEight

/-- Package the extracted direct cardinality statement as A-fiber-only
contribution data. -/
noncomputable def toAFiberOnlyContribution38Data
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    AFiberOnlyContribution38Data h input w.k
      (w.coords.fiberUnion w.indices) :=
  w.toAFiberCardinality38Boundary.toAFiberOnlyContribution38Data input w.k

end AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

namespace AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Inclusion-form canonical criteria also determine the direct selected
A-fiber cardinality boundary, via their equality-form conversion. -/
def toAFiberCardinality38Boundary
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    AFiberCardinality38Boundary h w.coords w.indices :=
  w.toCanonicalAFiberCriteria38Witness.toAFiberCardinality38Boundary

end AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness

namespace AFiberOnlyContribution38Data

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {indices : Finset (ZMod 19)}

/-- Convert A-fiber-only contribution data on a selected A-fiber union back to
the direct A-fiber-cardinality boundary package. -/
def toAFiberCardinality38Boundary
    (data : AFiberOnlyContribution38Data h input k
      (coords.fiberUnion indices)) :
    AFiberCardinality38Boundary h coords indices where
  card_eq_thirtyEight := by
    intro d hd
    rw [fixedAFiberAFiberCard, data.aFiber_contribution d hd]
    exact data.aFiber_eq_thirtyEight d hd

end AFiberOnlyContribution38Data

namespace FixedAFiberContribution38Data

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {indices : Finset (ZMod 19)}

/-- Convert split fixed/A-fiber contribution data on a selected A-fiber union
to the direct A-fiber-cardinality boundary package.  The fixed side is removed
using the existing zero-contribution theorem. -/
def toAFiberCardinality38Boundary
    (data : FixedAFiberContribution38Data h input k
      (coords.fiberUnion indices)) :
    AFiberCardinality38Boundary h coords indices where
  card_eq_thirtyEight := by
    intro d hd
    have hfixed :
        data.fixedContribution d = 0 := by
      calc
        data.fixedContribution d =
            ((rotationOneFixedResidualPart h input k).filter fun y =>
              Γ.Adj y (h.rotation d y)).card := by
              exact (data.fixed_contribution d hd).symm
        _ = 0 :=
            rotationOneFixedResidualPart_filter_adjacent_rotation_card_eq_zero
              h input k d hd
    have haFiber :
        fixedAFiberAFiberCard h (coords.fiberUnion indices) d =
          data.aFiberContribution d := by
      simpa [fixedAFiberAFiberCard] using data.aFiber_contribution d hd
    rw [haFiber]
    simpa [hfixed] using data.contribution_sum d hd

end FixedAFiberContribution38Data

namespace D19FinalTraceRotationOneHybridBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Build the current hybrid final boundary from the existing canonical
A-fiber criterion over the canonical carrier-produced input. -/
noncomputable def of_canonicalAFiberCriteria
    (traceCore : TraceCharacterCoreData Γ h.rotation h.a1)
    (rotationOneFixedCount_le_nineteen :
      fixedVertexCount (h.rotation 1) ≤ 19)
    (orbitBase : OrbitBaseSelectionCanonicalCarrierWitness h)
    (adjacentMoved :
      AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
        h orbitBase.toCarrierWitness.toInput) :
    D19FinalTraceRotationOneHybridBoundaryInputs h where
  traceCore := traceCore
  rotationOneFixedCount_le_nineteen :=
    rotationOneFixedCount_le_nineteen
  orbitBase := orbitBase
  reflectedAvoidance :=
    { k := adjacentMoved.k
      reflected_base_not_mem_orbitFamilyUnion := by
        intro r
        simpa using adjacentMoved.reflection_not_mem_orbitFamilyUnion r }
  coords := adjacentMoved.coords
  indices := adjacentMoved.indices
  moving_subset_aFiber := adjacentMoved.moving_subset_aFiber
  aFiber_subset_moving := adjacentMoved.aFiber_subset_moving
  aFiber_card_eq_thirtyEight :=
    adjacentMoved.aFiber_card_eq_thirtyEight

/-- Build the current hybrid final boundary from the inclusion-form canonical
A-fiber criterion over the canonical carrier-produced input. -/
noncomputable def of_canonicalAFiberInclusionCriteria
    (traceCore : TraceCharacterCoreData Γ h.rotation h.a1)
    (rotationOneFixedCount_le_nineteen :
      fixedVertexCount (h.rotation 1) ≤ 19)
    (orbitBase : OrbitBaseSelectionCanonicalCarrierWitness h)
    (adjacentMoved :
      AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness.{u, uP}
        h orbitBase.toCarrierWitness.toInput) :
    D19FinalTraceRotationOneHybridBoundaryInputs h :=
  of_canonicalAFiberCriteria traceCore rotationOneFixedCount_le_nineteen
    orbitBase adjacentMoved.toCanonicalAFiberCriteria38Witness

end D19FinalTraceRotationOneHybridBoundaryInputs

end Moore57
