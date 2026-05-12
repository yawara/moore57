import Moore57.D19OnMoore57.Final.TraceRotationOne
import Moore57.D19OnMoore57.Trace.CoreCharacterBoundary

/-!
# Final D19 inputs with final-boundary trace-core data

This file adds a thin final boundary that keeps the A-fiber-cardinality carrier
shape, but replaces the trace-core record by the final-boundary package where
`rotation_a1` is supplied by the `D19ActsOnMoore57` witness.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A-fiber-cardinality carrier final inputs whose trace core is stated as the
final-boundary package: multiplicity data plus the nontrivial rotation
character identity, with `rotation_a1` supplied by `h`. -/
structure D19FinalTraceCoreRotationOneCanonicalAFiberCardCarrierInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Final-boundary trace core for the representation-character side. -/
  traceCore : D19ActsOnMoore57.TraceCoreCharacterBoundary h
  /-- The fixed-count bound only for rotation by `1`. -/
  rotationOneFixedCount_le_nineteen :
    fixedVertexCount (h.rotation 1) ≤ 19
  /-- Bounded carrier witness for the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionCarrierWitness h
  /-- Reflected-base avoidance stated directly against the carrier. -/
  reflectedAvoidance :
    OrbitBaseSelectionCarrierReflectedAvoidance h orbitBase
  /-- A coordinate system for the A-side fibers. -/
  coords : AFiberCoordinates.{u, uP} Γ
  /-- The A-side fiber indices used in the moving residual. -/
  indices : Finset (ZMod 19)
  /-- The moving residual complement is exactly the selected A-fiber union. -/
  moving_eq_aFiber :
    rotationOneMovingResidualPart h orbitBase.toInput
        reflectedAvoidance.k =
      coords.fiberUnion indices
  /-- The concrete A-fiber-side filtered cardinality is `38` for every nonzero
  rotation step. -/
  aFiber_card_eq_thirtyEight :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      fixedAFiberAFiberCard h (coords.fiberUnion indices) d = 38

namespace D19FinalTraceCoreRotationOneCanonicalAFiberCardCarrierInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the final-boundary trace-core presentation to the existing
A-fiber-cardinality carrier boundary. -/
noncomputable def
    toD19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs
    (data :
      D19FinalTraceCoreRotationOneCanonicalAFiberCardCarrierInputs h) :
    D19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs h
    where
  traceCore := data.traceCore.toTraceCharacterCoreData
  rotationOneFixedCount_le_nineteen :=
    data.rotationOneFixedCount_le_nineteen
  orbitBase := data.orbitBase
  reflectedAvoidance := data.reflectedAvoidance
  coords := data.coords
  indices := data.indices
  moving_eq_aFiber := data.moving_eq_aFiber
  aFiber_card_eq_thirtyEight := data.aFiber_card_eq_thirtyEight

/-- Forget the final-boundary trace-core carrier presentation down to the final
input record. -/
noncomputable def toD19FinalInputs
    (data :
      D19FinalTraceCoreRotationOneCanonicalAFiberCardCarrierInputs h) :
    D19FinalInputs h :=
  data.toD19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs
    |>.toD19FinalInputs

/-- The final-boundary trace-core A-fiber-cardinality carrier inputs cannot
exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
      (D19FinalTraceCoreRotationOneCanonicalAFiberCardCarrierInputs h) := by
  rintro ⟨data⟩
  exact
    D19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs.not_nonempty
      h
      ⟨data.toD19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs⟩

end D19FinalTraceCoreRotationOneCanonicalAFiberCardCarrierInputs

end Moore57
