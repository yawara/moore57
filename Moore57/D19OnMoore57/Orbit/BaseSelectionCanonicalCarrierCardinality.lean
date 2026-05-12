import Moore57.D19OnMoore57.Orbit.BaseSelectionCarrierCanonical
import Moore57.D19OnMoore57.Orbit.BaseSelectionEnumeration
import Moore57.D19OnMoore57.Orbit.BaseSelectionInputBridge

/-!
# Cardinality constructors for canonical carrier witnesses

This file bridges the canonical carrier witness API back to the existing
orbit-base criteria.  The canonical witness only stores the selected bases and
the cardinality of their canonical orbit-family union, so all stronger
orbit-base inputs can produce one without adding new assumptions.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace OrbitBaseSelectionCanonicalCarrierWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- If the selected orbit finsets are pairwise disjoint and each indexed orbit
has size `19`, the canonical orbit-family union has cardinality `1064`. -/
theorem orbitFamilyUnion_card_of_pairwiseDisjoint_card_nineteen
    (base : Fin 56 → V)
    (hdisj : ∀ q r : Fin 56, q ≠ r →
      Disjoint (h.rotationOrbitFinset (base q))
        (h.rotationOrbitFinset (base r)))
    (hcard : ∀ q : Fin 56, (h.rotationOrbitFinset (base q)).card = 19) :
    (h.orbitFamilyUnion base).card = 1064 :=
  h.orbitFamilyUnion_card_eq_1064_of_fin56 base
    (by
      intro q r hqr
      exact hdisj q r hqr)
    hcard

/-- A moved base in each selected orbit, together with pairwise disjointness,
is enough to compute the canonical orbit-family union cardinality. -/
theorem orbitFamilyUnion_card_of_pairwiseDisjoint_base_moved
    (base : Fin 56 → V)
    (base_moved : ∀ q : Fin 56, h.rotation 1 (base q) ≠ base q)
    (hdisj : ∀ q r : Fin 56, q ≠ r →
      Disjoint (h.rotationOrbitFinset (base q))
        (h.rotationOrbitFinset (base r))) :
    (h.orbitFamilyUnion base).card = 1064 :=
  orbitFamilyUnion_card_of_pairwiseDisjoint_card_nineteen
    (h := h) base hdisj
    (by
      intro q
      exact h.rotationOrbitFinset_card_eq_nineteen_of_nonzero_moved'
        (d := 1) (x := base q) (by decide) (base_moved q))

/-- Constructor from the raw downstream orbit-base fields. -/
noncomputable def ofPairwiseDisjointBaseMoved
    (base : Fin 56 → V)
    (base_moved : ∀ q : Fin 56, h.rotation 1 (base q) ≠ base q)
    (hdisj : ∀ q r : Fin 56, q ≠ r →
      Disjoint (h.rotationOrbitFinset (base q))
        (h.rotationOrbitFinset (base r))) :
    OrbitBaseSelectionCanonicalCarrierWitness h where
  base := base
  orbitFamilyUnion_card :=
    orbitFamilyUnion_card_of_pairwiseDisjoint_base_moved
      (h := h) base base_moved hdisj

/-- Constructor from the downstream orbit-base input. -/
noncomputable def ofInput
    (input : OrbitBaseSelectionInput h) :
    OrbitBaseSelectionCanonicalCarrierWitness h :=
  ofPairwiseDisjointBaseMoved
    (h := h) input.base input.base_moved input.pairwise_disjoint

@[simp] theorem ofInput_base
    (input : OrbitBaseSelectionInput h) :
    (ofInput input).base = input.base := by
  rfl

/-- Constructor from a coordinate-injective witness. -/
noncomputable def ofWitness
    (w : OrbitBaseSelectionWitness h) :
    OrbitBaseSelectionCanonicalCarrierWitness h where
  base := w.base
  orbitFamilyUnion_card := w.orbitFamilyUnion_card

@[simp] theorem ofWitness_base
    (w : OrbitBaseSelectionWitness h) :
    (ofWitness w).base = w.base := by
  rfl

/-- Constructor from the raw global orbit-coordinate injectivity criterion. -/
noncomputable def ofOrbitCoordinateInjective
    (base : Fin 56 → V)
    (hinj :
      Function.Injective
        (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (base qi.1))) :
    OrbitBaseSelectionCanonicalCarrierWitness h where
  base := base
  orbitFamilyUnion_card :=
    h.orbitFamilyUnion_card_eq_1064_of_orbitCoordinate_injective base hinj

/-- Constructor from an explicit coordinate enumeration. -/
noncomputable def ofEnumeration
    (w : OrbitBaseSelectionEnumeration h) :
    OrbitBaseSelectionCanonicalCarrierWitness h where
  base := w.base
  orbitFamilyUnion_card := w.orbitFamilyUnion_card

@[simp] theorem ofEnumeration_base
    (w : OrbitBaseSelectionEnumeration h) :
    (ofEnumeration w).base = w.base := by
  rfl

/-- Constructor from an embedding-valued coordinate witness. -/
noncomputable def ofEmbedding
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    OrbitBaseSelectionCanonicalCarrierWitness h where
  base := w.base
  orbitFamilyUnion_card := w.orbitFamilyUnion_card

@[simp] theorem ofEmbedding_base
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    (ofEmbedding w).base = w.base := by
  rfl

/-- Constructor from a coordinate equivalence with a vertex subtype. -/
noncomputable def ofSubtypeEquiv
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    OrbitBaseSelectionCanonicalCarrierWitness h where
  base := w.base
  orbitFamilyUnion_card := w.orbitFamilyUnion_card

@[simp] theorem ofSubtypeEquiv_base
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    (ofSubtypeEquiv w).base = w.base := by
  rfl

/-- Constructor from the bounded-carrier criterion. -/
noncomputable def ofCarrier
    (w : OrbitBaseSelectionCarrierWitness h) :
    OrbitBaseSelectionCanonicalCarrierWitness h where
  base := w.base
  orbitFamilyUnion_card := w.orbitFamilyUnion_card

@[simp] theorem ofCarrier_base
    (w : OrbitBaseSelectionCarrierWitness h) :
    (ofCarrier w).base = w.base := by
  rfl

/-- The canonical carrier produced from a carrier witness has the same carrier
finset as the original bounded carrier witness. -/
theorem ofCarrier_toCarrierWitness_carrier_eq
    (w : OrbitBaseSelectionCarrierWitness h) :
    (ofCarrier w).toCarrierWitness.carrier = w.carrier := by
  exact w.carrier_eq_orbitFamilyUnion.symm

end OrbitBaseSelectionCanonicalCarrierWitness

namespace OrbitBaseSelectionInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Promote a downstream orbit-base input to a canonical carrier witness. -/
noncomputable def toCanonicalCarrierWitness
    (input : OrbitBaseSelectionInput h) :
    OrbitBaseSelectionCanonicalCarrierWitness h :=
  OrbitBaseSelectionCanonicalCarrierWitness.ofInput input

@[simp] theorem toCanonicalCarrierWitness_base
    (input : OrbitBaseSelectionInput h) :
    input.toCanonicalCarrierWitness.base = input.base := by
  rfl

theorem toCanonicalCarrierWitness_orbitFamilyUnion_card
    (input : OrbitBaseSelectionInput h) :
    (h.orbitFamilyUnion input.toCanonicalCarrierWitness.base).card = 1064 :=
  input.toCanonicalCarrierWitness.orbitFamilyUnion_card

end OrbitBaseSelectionInput

namespace OrbitBaseSelectionWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Promote a coordinate-injective witness to a canonical carrier witness. -/
noncomputable def toCanonicalCarrierWitness
    (w : OrbitBaseSelectionWitness h) :
    OrbitBaseSelectionCanonicalCarrierWitness h :=
  OrbitBaseSelectionCanonicalCarrierWitness.ofWitness w

@[simp] theorem toCanonicalCarrierWitness_base
    (w : OrbitBaseSelectionWitness h) :
    w.toCanonicalCarrierWitness.base = w.base := by
  rfl

theorem toCanonicalCarrierWitness_orbitFamilyUnion_card
    (w : OrbitBaseSelectionWitness h) :
    (h.orbitFamilyUnion w.toCanonicalCarrierWitness.base).card = 1064 :=
  w.toCanonicalCarrierWitness.orbitFamilyUnion_card

end OrbitBaseSelectionWitness

namespace OrbitBaseSelectionEnumeration

variable {h : D19ActsOnMoore57 V Γ}

/-- Promote an explicit coordinate enumeration to a canonical carrier witness. -/
noncomputable def toCanonicalCarrierWitness
    (w : OrbitBaseSelectionEnumeration h) :
    OrbitBaseSelectionCanonicalCarrierWitness h :=
  OrbitBaseSelectionCanonicalCarrierWitness.ofEnumeration w

@[simp] theorem toCanonicalCarrierWitness_base
    (w : OrbitBaseSelectionEnumeration h) :
    w.toCanonicalCarrierWitness.base = w.base := by
  rfl

theorem toCanonicalCarrierWitness_orbitFamilyUnion_card
    (w : OrbitBaseSelectionEnumeration h) :
    (h.orbitFamilyUnion w.toCanonicalCarrierWitness.base).card = 1064 :=
  w.toCanonicalCarrierWitness.orbitFamilyUnion_card

end OrbitBaseSelectionEnumeration

namespace OrbitBaseSelectionEmbeddingWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Promote an embedding-valued coordinate witness to a canonical carrier
witness. -/
noncomputable def toCanonicalCarrierWitness
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    OrbitBaseSelectionCanonicalCarrierWitness h :=
  OrbitBaseSelectionCanonicalCarrierWitness.ofEmbedding w

@[simp] theorem toCanonicalCarrierWitness_base
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    w.toCanonicalCarrierWitness.base = w.base := by
  rfl

end OrbitBaseSelectionEmbeddingWitness

namespace OrbitBaseSelectionSubtypeEquivWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Promote a subtype-equivalence coordinate witness to a canonical carrier
witness. -/
noncomputable def toCanonicalCarrierWitness
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    OrbitBaseSelectionCanonicalCarrierWitness h :=
  OrbitBaseSelectionCanonicalCarrierWitness.ofSubtypeEquiv w

@[simp] theorem toCanonicalCarrierWitness_base
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    w.toCanonicalCarrierWitness.base = w.base := by
  rfl

end OrbitBaseSelectionSubtypeEquivWitness

namespace OrbitBaseSelectionCarrierWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Promote a bounded-carrier witness to a canonical carrier witness. -/
noncomputable def toCanonicalCarrierWitness
    (w : OrbitBaseSelectionCarrierWitness h) :
    OrbitBaseSelectionCanonicalCarrierWitness h :=
  OrbitBaseSelectionCanonicalCarrierWitness.ofCarrier w

@[simp] theorem toCanonicalCarrierWitness_base
    (w : OrbitBaseSelectionCarrierWitness h) :
    w.toCanonicalCarrierWitness.base = w.base := by
  rfl

theorem toCanonicalCarrierWitness_toCarrierWitness_carrier_eq
    (w : OrbitBaseSelectionCarrierWitness h) :
    w.toCanonicalCarrierWitness.toCarrierWitness.carrier = w.carrier :=
  OrbitBaseSelectionCanonicalCarrierWitness.ofCarrier_toCarrierWitness_carrier_eq w

end OrbitBaseSelectionCarrierWitness

end Moore57
