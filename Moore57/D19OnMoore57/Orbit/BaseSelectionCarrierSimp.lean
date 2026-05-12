import Moore57.D19OnMoore57.Orbit.BaseSelectionCarrierAvoidance

/-!
# Simp lemmas for carrier-form orbit-base selections

This file adds stable API lemmas around
`OrbitBaseSelectionCarrierWitness.toInput`, so downstream proofs can rewrite
through the carrier witness without depending on the implementation details of
`toWitness` and `toInput`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace OrbitBaseSelectionCarrierWitness

variable {h : D19ActsOnMoore57 V Γ}

@[simp] theorem toWitness_base
    (w : OrbitBaseSelectionCarrierWitness h) :
    w.toWitness.base = w.base := by
  rfl

@[simp] theorem toInput_base
    (w : OrbitBaseSelectionCarrierWitness h) :
    w.toInput.base = w.base := by
  rfl

@[simp] theorem toInput_base_apply
    (w : OrbitBaseSelectionCarrierWitness h) (q : Fin 56) :
    w.toInput.base q = w.base q := by
  rfl

/-- The carrier is the orbit-family union of the input produced from the
carrier witness. -/
theorem carrier_eq_toInput_orbitFamilyUnion
    (w : OrbitBaseSelectionCarrierWitness h) :
    w.carrier = w.toInput.orbitFamilyUnion :=
  w.carrier_eq_input_orbitFamilyUnion

@[simp] theorem toInput_orbitFamilyUnion_eq_carrier
    (w : OrbitBaseSelectionCarrierWitness h) :
    w.toInput.orbitFamilyUnion = w.carrier :=
  w.carrier_eq_toInput_orbitFamilyUnion.symm

@[simp] theorem toInput_reflectionOrbitFamilyUnion_eq_reflectionCarrierUnion
    (w : OrbitBaseSelectionCarrierWitness h) (k : ZMod 19) :
    w.toInput.reflectionOrbitFamilyUnion k = w.reflectionCarrierUnion k :=
  (w.reflectionCarrierUnion_eq_toInput_reflectionOrbitFamilyUnion k).symm

/-- Wrapper for the carrier/input orbit-family membership equivalence, proved
through the new simp API. -/
theorem mem_toInput_orbitFamilyUnion_iff_mem_carrier'
    (w : OrbitBaseSelectionCarrierWitness h) (y : V) :
    y ∈ w.toInput.orbitFamilyUnion ↔ y ∈ w.carrier := by
  simp

/-- Wrapper for reflected-base carrier avoidance, proved through the new simp
API. -/
theorem reflection_not_mem_toInput_orbitFamilyUnion_iff_not_mem_carrier'
    (w : OrbitBaseSelectionCarrierWitness h) (k : ZMod 19) (r : Fin 56) :
    h.smul (DihedralGroup.sr k) (w.base r) ∉ w.toInput.orbitFamilyUnion ↔
      h.smul (DihedralGroup.sr k) (w.base r) ∉ w.carrier := by
  simp

/-- Wrapper for reflected-union membership, proved through the new simp API. -/
theorem mem_toInput_reflectionOrbitFamilyUnion_iff_mem_reflectionCarrierUnion'
    (w : OrbitBaseSelectionCarrierWitness h) (k : ZMod 19) (y : V) :
    y ∈ w.toInput.reflectionOrbitFamilyUnion k ↔
      y ∈ w.reflectionCarrierUnion k := by
  simp

/-- Wrapper for carrier-form residual membership, proved through the new simp
API and the input residual membership theorem. -/
theorem mem_reflectionCopyResidual_toInput_iff_not_carrier_and_not_reflectionCarrier'
    (w : OrbitBaseSelectionCarrierWitness h) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyResidual h w.toInput.base k ↔
      y ∉ w.carrier ∧ y ∉ w.reflectionCarrierUnion k := by
  simpa using
    (w.mem_reflectionCopyResidual_toInput_iff_not_carrier_and_not_reflectionCarrier
      k y)

end OrbitBaseSelectionCarrierWitness

namespace OrbitBaseSelectionCarrierReflectedAvoidance

variable {h : D19ActsOnMoore57 V Γ}
variable {w : OrbitBaseSelectionCarrierWitness h}

/-- Wrapper for the input-form reflected-base avoidance generated from a
carrier-form avoidance witness, with `toInput.base` normalized by simp. -/
theorem reflected_base_not_mem_toInput_orbitFamilyUnion'
    (a : OrbitBaseSelectionCarrierReflectedAvoidance h w) :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr a.k) (w.toInput.base r) ∉
        w.toInput.orbitFamilyUnion := by
  intro r
  simpa using a.reflected_base_not_mem_toInput_orbitFamilyUnion r

end OrbitBaseSelectionCarrierReflectedAvoidance

end Moore57
