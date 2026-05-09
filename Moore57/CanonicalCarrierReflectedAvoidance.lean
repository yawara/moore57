import Moore57.OrbitBaseSelectionCarrierCanonical
import Moore57.OrbitBaseSelectionCarrierAvoidance

/-!
# Canonical carrier reflected avoidance

This file packages reflected-base avoidance for canonical carrier witnesses,
where the carrier is stated directly as `h.orbitFamilyUnion w.base`, and
provides the thin conversion to the carrier-witness API.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Reflected-base avoidance for a canonical carrier witness, stated directly
against the canonical orbit-family union. -/
structure OrbitBaseSelectionCanonicalCarrierReflectedAvoidance
    (h : D19ActsOnMoore57 V Γ)
    (w : OrbitBaseSelectionCanonicalCarrierWitness h) where
  k : ZMod 19
  reflected_base_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (w.base r) ∉ h.orbitFamilyUnion w.base

namespace OrbitBaseSelectionCanonicalCarrierReflectedAvoidance

variable {h : D19ActsOnMoore57 V Γ}
variable {w : OrbitBaseSelectionCanonicalCarrierWitness h}

/-- Canonical reflected avoidance, restated against the carrier produced by
`toCarrierWitness`. -/
theorem reflected_base_not_mem_toCarrierWitness_carrier
    (a : OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w) :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr a.k) (w.toCarrierWitness.base r) ∉
        w.toCarrierWitness.carrier := by
  intro r
  simpa using a.reflected_base_not_mem_orbitFamilyUnion r

/-- Convert canonical reflected avoidance to the carrier-witness API. -/
noncomputable def toCarrierReflectedAvoidance
    (a : OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w) :
    OrbitBaseSelectionCarrierReflectedAvoidance h w.toCarrierWitness where
  k := a.k
  reflected_base_not_mem_carrier :=
    a.reflected_base_not_mem_toCarrierWitness_carrier

@[simp] theorem toCarrierReflectedAvoidance_k
    (a : OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w) :
    a.toCarrierReflectedAvoidance.k = a.k := by
  rfl

@[simp] theorem toCarrierReflectedAvoidance_reflected_base_not_mem_carrier
    (a : OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w)
    (r : Fin 56) :
    h.smul (DihedralGroup.sr a.toCarrierReflectedAvoidance.k)
        (w.toCarrierWitness.base r) ∉
      w.toCarrierWitness.carrier := by
  exact a.toCarrierReflectedAvoidance.reflected_base_not_mem_carrier r

/-- The carrier API conversion produces the same reflected-base avoidance
condition over the input generated from the canonical carrier witness. -/
theorem reflected_base_not_mem_toInput_orbitFamilyUnion
    (a : OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w) :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr a.k) (w.toCarrierWitness.toInput.base r) ∉
        w.toCarrierWitness.toInput.orbitFamilyUnion := by
  intro r
  simpa using
    a.toCarrierReflectedAvoidance
      |>.reflected_base_not_mem_toInput_orbitFamilyUnion r

/-- Canonical reflected-base avoidance is equivalent to carrier-form
avoidance after converting the witness to a carrier witness. -/
theorem reflected_base_not_mem_orbitFamilyUnion_iff_toCarrierWitness_carrier
    (a : OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w)
    (r : Fin 56) :
    h.smul (DihedralGroup.sr a.k) (w.base r) ∉ h.orbitFamilyUnion w.base ↔
      h.smul (DihedralGroup.sr a.k) (w.toCarrierWitness.base r) ∉
        w.toCarrierWitness.carrier := by
  simp

/-- Membership in the converted carrier is membership in the canonical
orbit-family union. -/
@[simp] theorem mem_toCarrierWitness_carrier
    (y : V) :
    y ∈ w.toCarrierWitness.carrier ↔ y ∈ h.orbitFamilyUnion w.base := by
  rfl

/-- Membership in the input produced from the converted carrier witness is
membership in the canonical orbit-family union. -/
@[simp] theorem mem_toCarrierWitness_toInput_orbitFamilyUnion
    (y : V) :
    y ∈ w.toCarrierWitness.toInput.orbitFamilyUnion ↔
      y ∈ h.orbitFamilyUnion w.base := by
  simp

/-- Reflected-base avoidance at the final input boundary, with the input base
and orbit-family union normalized to the canonical witness. -/
theorem reflected_base_not_mem_final_orbitFamilyUnion
    (a : OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h w) :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr a.k) (w.base r) ∉
        w.toCarrierWitness.toInput.orbitFamilyUnion := by
  intro r
  simpa using a.reflected_base_not_mem_toInput_orbitFamilyUnion r

end OrbitBaseSelectionCanonicalCarrierReflectedAvoidance

end Moore57
