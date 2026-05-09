import Moore57.OrbitBaseSelectionCarrierCriteria
import Moore57.AdjacentMovedReflectionResidualOriginalReflected

/-!
# Carrier-form reflected avoidance for selected orbit bases

This file keeps the orbit-base selection witness in carrier form when stating
the reflected-base avoidance and residual-membership conditions.  The lemmas
below translate those carrier-form conditions back to the existing
`OrbitBaseSelectionInput` API.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace OrbitBaseSelectionCarrierWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Membership in the produced input's orbit-family union is the same as
membership in the bounded carrier. -/
theorem mem_toInput_orbitFamilyUnion_iff_mem_carrier
    (w : OrbitBaseSelectionCarrierWitness h) (y : V) :
    y ∈ w.toInput.orbitFamilyUnion ↔ y ∈ w.carrier := by
  rw [← w.carrier_eq_input_orbitFamilyUnion]

/-- Reflected-base avoidance against the produced input's orbit-family union is
the same as reflected-base avoidance against the bounded carrier. -/
theorem reflection_not_mem_toInput_orbitFamilyUnion_iff_not_mem_carrier
    (w : OrbitBaseSelectionCarrierWitness h) (k : ZMod 19) (r : Fin 56) :
    h.smul (DihedralGroup.sr k) (w.base r) ∉ w.toInput.orbitFamilyUnion ↔
      h.smul (DihedralGroup.sr k) (w.base r) ∉ w.carrier := by
  exact not_congr
    (w.mem_toInput_orbitFamilyUnion_iff_mem_carrier
      (h.smul (DihedralGroup.sr k) (w.base r)))

/-- The reflected carrier union generated from a carrier witness. -/
noncomputable def reflectionCarrierUnion
    (w : OrbitBaseSelectionCarrierWitness h) (k : ZMod 19) : Finset V :=
  h.reflectionOrbitFamilyUnion w.base k

/-- Membership in the reflected carrier union. -/
theorem mem_reflectionCarrierUnion_iff
    (w : OrbitBaseSelectionCarrierWitness h) (k : ZMod 19) (y : V) :
    y ∈ w.reflectionCarrierUnion k ↔
      ∃ q : Fin 56, ∃ i : ZMod 19,
        h.rotation i (h.smul (DihedralGroup.sr k) (w.base q)) = y := by
  simpa [reflectionCarrierUnion] using
    h.mem_reflectionOrbitFamilyUnion_iff w.base k y

/-- The reflected carrier union is the reflected orbit-family union attached to
the input produced from the carrier witness. -/
theorem reflectionCarrierUnion_eq_toInput_reflectionOrbitFamilyUnion
    (w : OrbitBaseSelectionCarrierWitness h) (k : ZMod 19) :
    w.reflectionCarrierUnion k = w.toInput.reflectionOrbitFamilyUnion k := by
  ext y
  simp [reflectionCarrierUnion, OrbitBaseSelectionInput.reflectionOrbitFamilyUnion,
    OrbitBaseSelectionCarrierWitness.toInput,
    OrbitBaseSelectionCarrierWitness.toWitness,
    OrbitBaseSelectionWitness.toInput,
    OrbitBaseSelectionWitness.ofOrbitCoordinateInjective]

/-- Membership in the produced input's reflected orbit-family union is the same
as membership in the reflected carrier union. -/
theorem mem_toInput_reflectionOrbitFamilyUnion_iff_mem_reflectionCarrierUnion
    (w : OrbitBaseSelectionCarrierWitness h) (k : ZMod 19) (y : V) :
    y ∈ w.toInput.reflectionOrbitFamilyUnion k ↔
      y ∈ w.reflectionCarrierUnion k := by
  rw [← w.reflectionCarrierUnion_eq_toInput_reflectionOrbitFamilyUnion k]

/-- Carrier-form residual membership for the reflection-copy residual attached
to the input produced from a carrier witness. -/
theorem mem_reflectionCopyResidual_toInput_iff_not_carrier_and_not_reflectionCarrier
    (w : OrbitBaseSelectionCarrierWitness h) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyResidual h w.toInput.base k ↔
      y ∉ w.carrier ∧ y ∉ w.reflectionCarrierUnion k := by
  rw [w.toInput.mem_reflectionCopyResidual_iff_not_orbitFamilyUnion_and_not_reflectionOrbitFamilyUnion]
  rw [w.mem_toInput_orbitFamilyUnion_iff_mem_carrier]
  rw [w.mem_toInput_reflectionOrbitFamilyUnion_iff_mem_reflectionCarrierUnion]

end OrbitBaseSelectionCarrierWitness

/-- Carrier-form reflected-base avoidance for a selected orbit-base carrier
witness. -/
structure OrbitBaseSelectionCarrierReflectedAvoidance
    (h : D19ActsOnMoore57 V Γ) (w : OrbitBaseSelectionCarrierWitness h) where
  k : ZMod 19
  reflected_base_not_mem_carrier :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (w.base r) ∉ w.carrier

namespace OrbitBaseSelectionCarrierReflectedAvoidance

variable {h : D19ActsOnMoore57 V Γ}
variable {w : OrbitBaseSelectionCarrierWitness h}

/-- Carrier-form reflected-base avoidance gives the existing avoidance
condition over the produced `OrbitBaseSelectionInput`. -/
theorem reflected_base_not_mem_toInput_orbitFamilyUnion
    (a : OrbitBaseSelectionCarrierReflectedAvoidance h w) :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr a.k) (w.toInput.base r) ∉
        w.toInput.orbitFamilyUnion := by
  intro r
  simpa [OrbitBaseSelectionCarrierWitness.toInput,
    OrbitBaseSelectionCarrierWitness.toWitness,
    OrbitBaseSelectionWitness.toInput,
    OrbitBaseSelectionWitness.ofOrbitCoordinateInjective] using
    (w.reflection_not_mem_toInput_orbitFamilyUnion_iff_not_mem_carrier
      a.k r).mpr (a.reflected_base_not_mem_carrier r)

end OrbitBaseSelectionCarrierReflectedAvoidance

end Moore57
