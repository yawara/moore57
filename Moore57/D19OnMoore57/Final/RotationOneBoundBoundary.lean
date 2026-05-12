import Moore57.D19OnMoore57.Final.TraceRotationOne
import Moore57.D19OnMoore57.Rotation.OneFixedBoundBoundary

/-!
# Final D19 inputs with packaged rotation-one fixed bound

This file adds a thin variant of the A-fiber cardinality carrier boundary that
keeps the final rotation-one fixed-count assumption in the dedicated boundary
record.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A-fiber cardinality carrier final inputs whose rotation-one fixed-count
bound is supplied through the final-boundary wrapper record. -/
structure D19FinalRotationOneBoundCanonicalAFiberCardCarrierInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Split trace/multiplicity data for the representation-character side. -/
  traceCore : TraceCharacterCoreData Γ h.rotation h.a1
  /-- Packaged final-boundary fixed-count assumption for rotation by `1`. -/
  fixedBound : D19ActsOnMoore57.RotationOneFixedBoundBoundaryInput h
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

namespace D19FinalRotationOneBoundCanonicalAFiberCardCarrierInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the packaged rotation-one fixed-bound wrapper to the direct
A-fiber-cardinality carrier final boundary. -/
noncomputable def toD19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs
    (data :
      D19FinalRotationOneBoundCanonicalAFiberCardCarrierInputs h) :
    D19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs h where
  traceCore := data.traceCore
  rotationOneFixedCount_le_nineteen :=
    data.fixedBound.rotationOneFixedCount_le_nineteen
  orbitBase := data.orbitBase
  reflectedAvoidance := data.reflectedAvoidance
  coords := data.coords
  indices := data.indices
  moving_eq_aFiber := data.moving_eq_aFiber
  aFiber_card_eq_thirtyEight := data.aFiber_card_eq_thirtyEight

/-- Forget the packaged fixed-bound presentation down to the final input
record. -/
noncomputable def toD19FinalInputs
    (data :
      D19FinalRotationOneBoundCanonicalAFiberCardCarrierInputs h) :
    D19FinalInputs h :=
  data.toD19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs
    |>.toD19FinalInputs

/-- The packaged fixed-bound A-fiber-cardinality carrier final inputs cannot
exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
      (D19FinalRotationOneBoundCanonicalAFiberCardCarrierInputs h) := by
  rintro ⟨data⟩
  exact
    D19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs.not_nonempty
      h
      ⟨data.toD19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs⟩

end D19FinalRotationOneBoundCanonicalAFiberCardCarrierInputs

end Moore57
