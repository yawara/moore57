import Moore57.OrbitBaseSelectionInputs
import Moore57.OrbitBaseSelectionCriteria

/-!
# Carrier criteria for selecting the 56 rotation-orbit bases

This file gives a bounded carrier criterion for `OrbitBaseSelectionInput`.
Instead of proving pairwise disjointness of the 56 orbit finsets directly, it is
enough to exhibit a finset carrier of size `1064` whose membership is exactly
membership in the selected rotation-coordinate image.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A bounded carrier witness for the selected rotation orbits.

The essential data are a finset `carrier` of the expected size and a membership
equivalence saying that this carrier is exactly the image of the 56-by-19
rotation-coordinate map.  The cardinality bound then forces the coordinate map
to be injective, hence recovers the downstream pairwise-disjoint orbit input. -/
structure OrbitBaseSelectionCarrierWitness (h : D19ActsOnMoore57 V Γ) where
  /-- One representative for each of the 56 rotation orbits. -/
  base : Fin 56 → V
  /-- The selected carrier as a bounded finset of vertices. -/
  carrier : Finset V
  /-- Carrier membership is exactly being a rotation of one selected base. -/
  mem_carrier :
    ∀ y : V, y ∈ carrier ↔
      ∃ q : Fin 56, ∃ i : ZMod 19, h.rotation i (base q) = y
  /-- The selected carrier has the expected bounded size. -/
  carrier_card : carrier.card = 1064

namespace OrbitBaseSelectionCarrierWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- The coordinate map, viewed as landing in the carrier subtype. -/
noncomputable def coordToCarrier (w : OrbitBaseSelectionCarrierWitness h) :
    Fin 56 × ZMod 19 → { y : V // y ∈ w.carrier } :=
  fun qi =>
    ⟨h.rotation qi.2 (w.base qi.1),
      (w.mem_carrier _).mpr ⟨qi.1, qi.2, rfl⟩⟩

/-- The coordinate-to-carrier map is surjective by the membership equivalence. -/
theorem coordToCarrier_surjective
    (w : OrbitBaseSelectionCarrierWitness h) :
    Function.Surjective w.coordToCarrier := by
  intro y
  rcases (w.mem_carrier y).mp y.property with ⟨q, i, hi⟩
  exact ⟨(q, i), Subtype.ext hi⟩

/-- The coordinate type and carrier subtype have the same cardinality. -/
theorem coordToCarrier_card_eq
    (w : OrbitBaseSelectionCarrierWitness h) :
    Fintype.card (Fin 56 × ZMod 19) =
      Fintype.card { y : V // y ∈ w.carrier } := by
  calc
    Fintype.card (Fin 56 × ZMod 19) = 1064 := by
      simp [Fintype.card_prod, ZMod.card]
    _ = Fintype.card { y : V // y ∈ w.carrier } := by
      simp [w.carrier_card]

/-- The bounded carrier criterion forces injectivity of the concrete
rotation-coordinate map. -/
theorem orbitCoordinate_injective
    (w : OrbitBaseSelectionCarrierWitness h) :
    Function.Injective
      (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (w.base qi.1)) := by
  have hbij :
      Function.Bijective w.coordToCarrier :=
    (Fintype.bijective_iff_surjective_and_card w.coordToCarrier).2
      ⟨w.coordToCarrier_surjective, w.coordToCarrier_card_eq⟩
  intro qi qj heq
  apply hbij.1
  exact Subtype.ext heq

/-- The selected carrier is definitionally the orbit-family union as a finset. -/
theorem carrier_eq_orbitFamilyUnion
    (w : OrbitBaseSelectionCarrierWitness h) :
    w.carrier = h.orbitFamilyUnion w.base := by
  ext y
  rw [w.mem_carrier, h.mem_orbitFamilyUnion]

/-- The selected orbit finsets are pairwise disjoint. -/
theorem pairwise_disjoint
    (w : OrbitBaseSelectionCarrierWitness h) :
    ∀ q r : Fin 56, q ≠ r →
      Disjoint (h.rotationOrbitFinset (w.base q))
        (h.rotationOrbitFinset (w.base r)) :=
  h.pairwise_disjoint_rotationOrbitFinset_of_orbitCoordinate_injective
    w.base w.orbitCoordinate_injective

/-- Convert a carrier witness into the existing coordinate-injective witness. -/
noncomputable def toWitness
    (w : OrbitBaseSelectionCarrierWitness h) :
    OrbitBaseSelectionWitness h :=
  OrbitBaseSelectionWitness.ofOrbitCoordinateInjective
    w.base w.orbitCoordinate_injective

/-- Convert a carrier witness directly into the downstream input. -/
noncomputable def toInput
    (w : OrbitBaseSelectionCarrierWitness h) :
    OrbitBaseSelectionInput h :=
  w.toWitness.toInput

/-- The carrier is the same finset as the orbit union of the produced input. -/
theorem carrier_eq_input_orbitFamilyUnion
    (w : OrbitBaseSelectionCarrierWitness h) :
    w.carrier = w.toInput.orbitFamilyUnion := by
  simpa [toInput, OrbitBaseSelectionInput.orbitFamilyUnion] using
    w.carrier_eq_orbitFamilyUnion

/-- The selected orbit-family union has cardinality `1064`. -/
theorem orbitFamilyUnion_card
    (w : OrbitBaseSelectionCarrierWitness h) :
    (h.orbitFamilyUnion w.base).card = 1064 := by
  rw [← w.carrier_eq_orbitFamilyUnion]
  exact w.carrier_card

end OrbitBaseSelectionCarrierWitness

namespace OrbitBaseSelectionWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Build a base-selection witness from a bounded carrier criterion. -/
noncomputable def ofCarrier
    (w : OrbitBaseSelectionCarrierWitness h) :
    OrbitBaseSelectionWitness h :=
  w.toWitness

end OrbitBaseSelectionWitness

namespace OrbitBaseSelectionInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Direct constructor for `OrbitBaseSelectionInput` from a bounded carrier
criterion. -/
noncomputable def ofCarrier
    (w : OrbitBaseSelectionCarrierWitness h) :
    OrbitBaseSelectionInput h :=
  w.toInput

end OrbitBaseSelectionInput

end Moore57
