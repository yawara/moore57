import Moore57.D19OnMoore57.Orbit.BaseSelectionCanonicalCarrierCardinality

/-!
# Nonempty bridges for canonical carrier witnesses

This file records the `Nonempty`-level equivalences between the canonical
carrier witness and the existing orbit-base criteria.  In particular, an
existence proof may be supplied through `OrbitBaseSelectionInput`, where the
canonical orbit-family cardinality is computed from the existing moved-base and
pairwise-disjoint orbit criteria, rather than as a direct field.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace OrbitBaseSelectionCanonicalCarrierWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert a canonical carrier witness directly to the downstream
base-selection input by reusing the bounded-carrier criterion. -/
noncomputable def toInput
    (w : OrbitBaseSelectionCanonicalCarrierWitness h) :
    OrbitBaseSelectionInput h :=
  w.toCarrierWitness.toInput

@[simp] theorem toInput_base
    (w : OrbitBaseSelectionCanonicalCarrierWitness h) :
    w.toInput.base = w.base := by
  rfl

/-- Any canonical carrier witness gives the downstream orbit-base input. -/
theorem nonempty_toInput :
    Nonempty (OrbitBaseSelectionCanonicalCarrierWitness h) →
      Nonempty (OrbitBaseSelectionInput h) := by
  rintro ⟨w⟩
  exact ⟨w.toInput⟩

/-- Any downstream orbit-base input gives a canonical carrier witness; the
`orbitFamilyUnion_card = 1064` field is computed by the existing input
criterion. -/
theorem nonempty_ofInput :
    Nonempty (OrbitBaseSelectionInput h) →
      Nonempty (OrbitBaseSelectionCanonicalCarrierWitness h) := by
  rintro ⟨input⟩
  exact ⟨OrbitBaseSelectionCanonicalCarrierWitness.ofInput input⟩

/-- Canonical carrier witnesses and downstream orbit-base inputs are
equivalent at the `Nonempty` level. -/
theorem nonempty_iff_input :
    Nonempty (OrbitBaseSelectionCanonicalCarrierWitness h) ↔
      Nonempty (OrbitBaseSelectionInput h) := by
  constructor
  · exact nonempty_toInput
  · exact nonempty_ofInput

/-- Any canonical carrier witness gives the general bounded-carrier witness. -/
theorem nonempty_toCarrierWitness :
    Nonempty (OrbitBaseSelectionCanonicalCarrierWitness h) →
      Nonempty (OrbitBaseSelectionCarrierWitness h) := by
  rintro ⟨w⟩
  exact ⟨w.toCarrierWitness⟩

/-- Any bounded-carrier witness gives a canonical carrier witness. -/
theorem nonempty_ofCarrierWitness :
    Nonempty (OrbitBaseSelectionCarrierWitness h) →
      Nonempty (OrbitBaseSelectionCanonicalCarrierWitness h) := by
  rintro ⟨w⟩
  exact ⟨OrbitBaseSelectionCanonicalCarrierWitness.ofCarrier w⟩

/-- Canonical carrier witnesses and bounded-carrier witnesses are equivalent at
the `Nonempty` level. -/
theorem nonempty_iff_carrierWitness :
    Nonempty (OrbitBaseSelectionCanonicalCarrierWitness h) ↔
      Nonempty (OrbitBaseSelectionCarrierWitness h) := by
  constructor
  · exact nonempty_toCarrierWitness
  · exact nonempty_ofCarrierWitness

end OrbitBaseSelectionCanonicalCarrierWitness

namespace OrbitBaseSelectionInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Symmetric spelling of the canonical-carrier/input `Nonempty` bridge from
the input namespace. -/
theorem nonempty_iff_canonicalCarrierWitness :
    Nonempty (OrbitBaseSelectionInput h) ↔
      Nonempty (OrbitBaseSelectionCanonicalCarrierWitness h) :=
  OrbitBaseSelectionCanonicalCarrierWitness.nonempty_iff_input.symm

end OrbitBaseSelectionInput

namespace OrbitBaseSelectionCarrierWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Symmetric spelling of the canonical-carrier/carrier `Nonempty` bridge from
the carrier namespace. -/
theorem nonempty_iff_canonicalCarrierWitness :
    Nonempty (OrbitBaseSelectionCarrierWitness h) ↔
      Nonempty (OrbitBaseSelectionCanonicalCarrierWitness h) :=
  OrbitBaseSelectionCanonicalCarrierWitness.nonempty_iff_carrierWitness.symm

end OrbitBaseSelectionCarrierWitness

end Moore57
