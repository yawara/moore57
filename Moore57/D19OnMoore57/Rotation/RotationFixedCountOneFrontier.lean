import Moore57.D19OnMoore57.LinearCharacter.D19LinearCharacterMinus8Connectors
import Moore57.D19OnMoore57.Rotation.RotationFixedUpperBoundFromData
import Moore57.D19OnMoore57.Rotation.RotationFixedRegularity
import Moore57.D19OnMoore57.Rotation.RotationOneFixedBoundBoundary

/-!
# Rotation fixed count-one frontier

This file exposes the already-proved exact fixed-count statement in the
`smulEquiv (DihedralGroup.r d)` shape used by the representation-side
connectors.  All constructors here are thin wrappers around existing
rotation fixed-count packages.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- The proved rotation fixed-count theorem in the `smulEquiv` rotation shape. -/
theorem rotationFixedCountOne_smulEquiv
    (h : D19ActsOnMoore57 V Γ) :
    ∀ d : ZMod 19, d ≠ 0 →
      fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1 := by
  intro d hd
  simpa [D19ActsOnMoore57.rotation] using h.rotation_fixed_card_eq_one hd

/-- Split fixed-point data also gives the `smulEquiv` rotation count-one shape. -/
theorem rotationFixedCountOne_smulEquiv_of_rotationFixedData
    (hfixed : RotationFixedData h.rotation) :
    ∀ d : ZMod 19, d ≠ 0 →
      fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1 := by
  intro d hd
  simpa [D19ActsOnMoore57.rotation] using hfixed.rotation_fixed d hd

namespace RotationFixedUpperBoundInput

/-- A coarse upper-bound package already implies exact count `1` for all
nontrivial rotations, exposed in the `smulEquiv` rotation shape. -/
theorem rotationFixedCountOne_smulEquiv
    (input : RotationFixedUpperBoundInput h) :
    ∀ d : ZMod 19, d ≠ 0 →
      fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1 :=
  D19ActsOnMoore57.rotationFixedCountOne_smulEquiv_of_rotationFixedData
    (h := h) input.toRotationFixedData

/-- Rebuild the coarse upper-bound package from split fixed-point data through
the representation-side `of_rotationFixedCountOne` constructor. -/
def ofRotationFixedData_via_rotationFixedCountOne
    (hfixed : RotationFixedData h.rotation) :
    RotationFixedUpperBoundInput h :=
  of_rotationFixedCountOne (h := h)
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv_of_rotationFixedData
      (h := h) hfixed)

/-- The ambient Moore57/D19 action theorem is enough to fill the coarse
upper-bound package via `of_rotationFixedCountOne`. -/
def of_provedRotationFixedCountOne
    (h : D19ActsOnMoore57 V Γ) :
    RotationFixedUpperBoundInput h :=
  of_rotationFixedCountOne (h := h)
    (D19ActsOnMoore57.rotationFixedCountOne_smulEquiv h)

end RotationFixedUpperBoundInput

namespace RotationOneFixedBoundWitness

/-- A rotation-one fixed-bound witness implies exact count `1` for every
nontrivial rotation, in the representation-side rotation shape. -/
theorem rotationFixedCountOne_smulEquiv
    (w : RotationOneFixedBoundWitness h) :
    ∀ d : ZMod 19, d ≠ 0 →
      fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1 :=
  w.toRotationFixedUpperBoundInput.rotationFixedCountOne_smulEquiv

/-- Convert a rotation-one fixed-bound witness through the count-one connector. -/
def toRotationFixedUpperBoundInput_via_rotationFixedCountOne
    (w : RotationOneFixedBoundWitness h) :
    RotationFixedUpperBoundInput h :=
  RotationFixedUpperBoundInput.of_rotationFixedCountOne
    (h := h) w.rotationFixedCountOne_smulEquiv

end RotationOneFixedBoundWitness

namespace RotationOneFixedEnumeration

/-- A finite enumeration of rotation-one fixed vertices implies exact count
`1` for every nontrivial rotation, in the representation-side rotation shape. -/
theorem rotationFixedCountOne_smulEquiv
    (e : RotationOneFixedEnumeration h) :
    ∀ d : ZMod 19, d ≠ 0 →
      fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1 :=
  e.toRotationFixedUpperBoundInput.rotationFixedCountOne_smulEquiv

/-- Convert a rotation-one fixed enumeration through the count-one connector. -/
def toRotationFixedUpperBoundInput_via_rotationFixedCountOne
    (e : RotationOneFixedEnumeration h) :
    RotationFixedUpperBoundInput h :=
  RotationFixedUpperBoundInput.of_rotationFixedCountOne
    (h := h) e.rotationFixedCountOne_smulEquiv

end RotationOneFixedEnumeration

namespace RotationOneFixedBoundBoundaryInput

/-- The boundary wrapper for the rotation-one bound implies exact count `1`
for every nontrivial rotation, in the representation-side rotation shape. -/
theorem rotationFixedCountOne_smulEquiv
    (data : RotationOneFixedBoundBoundaryInput h) :
    ∀ d : ZMod 19, d ≠ 0 →
      fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1 :=
  data.toRotationFixedUpperBoundInput.rotationFixedCountOne_smulEquiv

/-- Convert the boundary wrapper through the count-one connector. -/
def toRotationFixedUpperBoundInput_via_rotationFixedCountOne
    (data : RotationOneFixedBoundBoundaryInput h) :
    RotationFixedUpperBoundInput h :=
  RotationFixedUpperBoundInput.of_rotationFixedCountOne
    (h := h) data.rotationFixedCountOne_smulEquiv

end RotationOneFixedBoundBoundaryInput

end D19ActsOnMoore57

namespace D19FinalCharacterInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Final character inputs carry the exact rotation count-one statement through
their fixed upper-bound field. -/
theorem rotationFixedCountOne_smulEquiv
    (data : D19FinalCharacterInputs h) :
    ∀ d : ZMod 19, d ≠ 0 →
      fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1 :=
  data.fixedUpperBound.rotationFixedCountOne_smulEquiv

end D19FinalCharacterInputs

namespace D19FinalInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Final D19 inputs carry the exact rotation count-one statement through
their character package. -/
theorem rotationFixedCountOne_smulEquiv
    (data : D19FinalInputs h) :
    ∀ d : ZMod 19, d ≠ 0 →
      fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1 :=
  data.character.rotationFixedCountOne_smulEquiv

end D19FinalInputs

namespace TraceCharacterData

variable {h : D19ActsOnMoore57 V Γ}

/-- Bundled trace character data already contains the split rotation fixed
data; expose it in the `smulEquiv` rotation shape. -/
theorem rotationFixedCountOne_smulEquiv
    (data : TraceCharacterData Γ h.rotation h.a1) :
    ∀ d : ZMod 19, d ≠ 0 →
      fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1 :=
  D19ActsOnMoore57.rotationFixedCountOne_smulEquiv_of_rotationFixedData
    (h := h) data.toRotationFixedData

end TraceCharacterData

end Moore57
