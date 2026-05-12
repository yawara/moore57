import Moore57.D19OnMoore57.AdjacentMoved.Reflection
import Moore57.D19OnMoore57.Orbit.BaseSelection

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

/-!
# Canonical carrier witnesses for orbit-base selections

This file packages the special case where the carrier finset is exactly the
canonical orbit-family union `h.orbitFamilyUnion base`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A carrier witness whose carrier is definitionally the canonical
orbit-family union generated by the selected bases. -/
structure OrbitBaseSelectionCanonicalCarrierWitness
    (h : D19ActsOnMoore57 V Γ) where
  /-- One representative for each of the 56 rotation orbits. -/
  base : Fin 56 → V
  /-- The canonical orbit-family union has the expected bounded size. -/
  orbitFamilyUnion_card : (h.orbitFamilyUnion base).card = 1064

namespace OrbitBaseSelectionCanonicalCarrierWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert a canonical carrier witness to the general carrier-witness API. -/
noncomputable def toCarrierWitness
    (w : OrbitBaseSelectionCanonicalCarrierWitness h) :
    OrbitBaseSelectionCarrierWitness h where
  base := w.base
  carrier := h.orbitFamilyUnion w.base
  mem_carrier := h.mem_orbitFamilyUnion w.base
  carrier_card := w.orbitFamilyUnion_card

@[simp] theorem toCarrierWitness_base
    (w : OrbitBaseSelectionCanonicalCarrierWitness h) :
    w.toCarrierWitness.base = w.base := by
  rfl

@[simp] theorem toCarrierWitness_base_apply
    (w : OrbitBaseSelectionCanonicalCarrierWitness h) (q : Fin 56) :
    w.toCarrierWitness.base q = w.base q := by
  rfl

@[simp] theorem toCarrierWitness_carrier
    (w : OrbitBaseSelectionCanonicalCarrierWitness h) :
    w.toCarrierWitness.carrier = h.orbitFamilyUnion w.base := by
  rfl

@[simp] theorem mem_toCarrierWitness_carrier
    (w : OrbitBaseSelectionCanonicalCarrierWitness h) (y : V) :
    y ∈ w.toCarrierWitness.carrier ↔
      ∃ q : Fin 56, ∃ i : ZMod 19, h.rotation i (w.base q) = y := by
  simpa using h.mem_orbitFamilyUnion w.base y

@[simp] theorem toCarrierWitness_orbitFamilyUnion_card
    (w : OrbitBaseSelectionCanonicalCarrierWitness h) :
    (h.orbitFamilyUnion w.toCarrierWitness.base).card = 1064 := by
  simpa using w.orbitFamilyUnion_card

end OrbitBaseSelectionCanonicalCarrierWitness

end Moore57

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

