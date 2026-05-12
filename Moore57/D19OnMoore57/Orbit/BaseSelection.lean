import Moore57.D19OnMoore57.D19Core.ActionOrbitConcreteData
import Moore57.D19OnMoore57.D19Core.OrbitContributionData
import Moore57.D19OnMoore57.Orbit.FamilyPartition
import Moore57.D19OnMoore57.Rotation.OrbitFinset

/-!
# Base-selection input for the 56 rotation orbits

This file isolates the remaining geometric input that the Section 5/6
contradiction pipeline needs: a choice of 56 moved base vertices whose rotation
orbits are pairwise disjoint.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The geometric base-selection input for the 56 non-fixed rotation orbits. -/
structure OrbitBaseSelectionInput (h : D19ActsOnMoore57 V Γ) where
  /-- One representative for each of the 56 rotation orbits. -/
  base : Fin 56 → V
  /-- Each representative is moved by the first nontrivial rotation. -/
  base_moved : ∀ q, h.rotation 1 (base q) ≠ base q
  /-- The 56 generated rotation orbits are pairwise disjoint. -/
  pairwise_disjoint :
    ∀ q r, q ≠ r →
      Disjoint (h.rotationOrbitFinset (base q)) (h.rotationOrbitFinset (base r))

namespace OrbitBaseSelectionInput

variable {h : D19ActsOnMoore57 V Γ}

/-- The full orbit map generated from the selected base vertex of orbit `q`. -/
noncomputable def W (input : OrbitBaseSelectionInput h) (q : Fin 56) :
    ZMod 19 → V :=
  fun i => h.rotation i (input.base q)

/-- Each selected base vertex generates an injective `19`-cycle. -/
theorem W_injective (input : OrbitBaseSelectionInput h) (q : Fin 56) :
    Function.Injective (input.W q) :=
  h.rotationOrbitW_injective_of_nonzero_moved
    (d := 1) (x := input.base q) (by decide) (input.base_moved q)

/-- Each selected base vertex has a rotation orbit of cardinality `19`. -/
theorem rotationOrbitFinset_card_base
    (input : OrbitBaseSelectionInput h) (q : Fin 56) :
    (h.rotationOrbitFinset (input.base q)).card = 19 :=
  h.rotationOrbitFinset_card_eq_nineteen_of_nonzero_moved'
    (d := 1) (by decide) (input.base_moved q)

/-- The union of the selected 56 rotation orbits. -/
noncomputable def orbitFamilyUnion (input : OrbitBaseSelectionInput h) :
    Finset V :=
  h.orbitFamilyUnion input.base

/-- Membership in the selected-orbit union is exactly being a rotation of one
of the selected base vertices. -/
theorem mem_orbitFamilyUnion (input : OrbitBaseSelectionInput h) (y : V) :
    y ∈ input.orbitFamilyUnion ↔
      ∃ q : Fin 56, ∃ i : ZMod 19, h.rotation i (input.base q) = y := by
  simpa [orbitFamilyUnion] using h.mem_orbitFamilyUnion input.base y

/-- The selected 56 disjoint rotation orbits contain `1064` vertices. -/
theorem orbitFamilyUnion_card (input : OrbitBaseSelectionInput h) :
    input.orbitFamilyUnion.card = 1064 := by
  simpa [orbitFamilyUnion] using
    h.orbitFamilyUnion_card_eq_1064_of_fin56 input.base
      (by
        intro q r hqr
        exact input.pairwise_disjoint q r hqr)
      input.rotationOrbitFinset_card_base

/-- Constructor-field helper for downstream `D19ActionOrbitConcreteData`. -/
noncomputable def baseForActionOrbitConcreteData
    (input : OrbitBaseSelectionInput h) :
    Fin 56 → V :=
  input.base

/-- Constructor-field helper for the moved-base field of
`D19ActionOrbitConcreteData`. -/
theorem baseForActionOrbitConcreteData_moved
    (input : OrbitBaseSelectionInput h) :
    ∀ q : Fin 56,
      h.rotation 1 (input.baseForActionOrbitConcreteData q) ≠
        input.baseForActionOrbitConcreteData q := by
  simpa [baseForActionOrbitConcreteData] using input.base_moved

/-- Constructor-field helper for downstream `D19OrbitContributionData`. -/
noncomputable def baseForOrbitContributionData
    (input : OrbitBaseSelectionInput h) :
    Fin 56 → V :=
  input.base

/-- Constructor-field helper for the moved-base field of
`D19OrbitContributionData`. -/
theorem baseForOrbitContributionData_moved
    (input : OrbitBaseSelectionInput h) :
    ∀ q : Fin 56,
      h.rotation 1 (input.baseForOrbitContributionData q) ≠
        input.baseForOrbitContributionData q := by
  simpa [baseForOrbitContributionData] using input.base_moved

/-- Extract the base-selection input from orbit concrete data once the
remaining pairwise-disjointness proof is supplied. -/
noncomputable def ofActionOrbitConcreteData
    (data : D19ActionOrbitConcreteData h)
    (pairwise_disjoint :
      ∀ q r, q ≠ r →
        Disjoint (h.rotationOrbitFinset (data.base q))
          (h.rotationOrbitFinset (data.base r))) :
    OrbitBaseSelectionInput h where
  base := data.base
  base_moved := data.base_moved
  pairwise_disjoint := pairwise_disjoint

/-- Extract the base-selection input from orbit contribution data once the
remaining pairwise-disjointness proof is supplied. -/
noncomputable def ofOrbitContributionData
    (data : D19OrbitContributionData h)
    (pairwise_disjoint :
      ∀ q r, q ≠ r →
        Disjoint (h.rotationOrbitFinset (data.base q))
          (h.rotationOrbitFinset (data.base r))) :
    OrbitBaseSelectionInput h where
  base := data.base
  base_moved := data.base_moved
  pairwise_disjoint := pairwise_disjoint

end OrbitBaseSelectionInput

end Moore57

/-!
# Criteria for selecting the 56 rotation-orbit bases

This file packages a lower-level criterion for `OrbitBaseSelectionInput`: it is
enough to choose 56 base vertices such that the global orbit-coordinate map
`(q, i) ↦ h.rotation i (base q)` is injective.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- If the global orbit-coordinate map is injective, then every selected base
vertex is moved by the first nontrivial rotation. -/
theorem base_moved_of_orbitCoordinate_injective
    (base : Fin 56 → V)
    (hinj :
      Function.Injective
        (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (base qi.1))) :
    ∀ q : Fin 56, h.rotation 1 (base q) ≠ base q := by
  intro q hfixed
  have hpair :
      ((q, (1 : ZMod 19)) : Fin 56 × ZMod 19) =
        ((q, (0 : ZMod 19)) : Fin 56 × ZMod 19) := by
    apply hinj
    dsimp
    simpa using hfixed
  have h10 : (1 : ZMod 19) = 0 := congrArg Prod.snd hpair
  exact (by decide : (1 : ZMod 19) ≠ 0) h10

/-- Global injectivity of the orbit-coordinate map implies that the selected
rotation-orbit finsets are pairwise disjoint. -/
theorem pairwise_disjoint_rotationOrbitFinset_of_orbitCoordinate_injective
    (base : Fin 56 → V)
    (hinj :
      Function.Injective
        (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (base qi.1))) :
    ∀ q r : Fin 56, q ≠ r →
      Disjoint (h.rotationOrbitFinset (base q)) (h.rotationOrbitFinset (base r)) := by
  intro q r hqr
  rw [Finset.disjoint_left]
  intro y hyq hyr
  rcases (h.mem_rotationOrbitFinset (base q) y).mp hyq with ⟨i, hi⟩
  rcases (h.mem_rotationOrbitFinset (base r) y).mp hyr with ⟨j, hj⟩
  have hpair :
      ((q, i) : Fin 56 × ZMod 19) = ((r, j) : Fin 56 × ZMod 19) := by
    apply hinj
    dsimp
    exact hi.trans hj.symm
  exact hqr (congrArg Prod.fst hpair)

/-- Constructor for `OrbitBaseSelectionInput` from the single global
injectivity criterion on orbit coordinates. -/
noncomputable def toOrbitBaseSelectionInput_of_orbitCoordinate_injective
    (base : Fin 56 → V)
    (hinj :
      Function.Injective
        (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (base qi.1))) :
    OrbitBaseSelectionInput h where
  base := base
  base_moved := h.base_moved_of_orbitCoordinate_injective base hinj
  pairwise_disjoint :=
    h.pairwise_disjoint_rotationOrbitFinset_of_orbitCoordinate_injective base hinj

/-- The union of the 56 selected orbits has cardinality `1064` under the
single global orbit-coordinate injectivity criterion. -/
theorem orbitFamilyUnion_card_eq_1064_of_orbitCoordinate_injective
    (base : Fin 56 → V)
    (hinj :
      Function.Injective
        (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (base qi.1))) :
    (h.orbitFamilyUnion base).card = 1064 := by
  let input := h.toOrbitBaseSelectionInput_of_orbitCoordinate_injective base hinj
  simpa [OrbitBaseSelectionInput.orbitFamilyUnion, input] using
    input.orbitFamilyUnion_card

end D19ActsOnMoore57

/-- Witness form of the base-selection criterion.  The key field is the global
injectivity of `(q, i) ↦ h.rotation i (base q)`, which is stronger than the
pairwise-disjoint orbit-family assumption required downstream. -/
structure OrbitBaseSelectionWitness (h : D19ActsOnMoore57 V Γ) where
  /-- One representative for each of the 56 rotation orbits. -/
  base : Fin 56 → V
  /-- Each representative is moved by the first nontrivial rotation. -/
  base_moved : ∀ q : Fin 56, h.rotation 1 (base q) ≠ base q
  /-- The global orbit-coordinate map is injective. -/
  orbitCoordinate_injective :
    Function.Injective
      (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (base qi.1))

namespace OrbitBaseSelectionWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- The selected orbit finsets from a witness are pairwise disjoint. -/
theorem pairwise_disjoint (w : OrbitBaseSelectionWitness h) :
    ∀ q r : Fin 56, q ≠ r →
      Disjoint (h.rotationOrbitFinset (w.base q)) (h.rotationOrbitFinset (w.base r)) :=
  h.pairwise_disjoint_rotationOrbitFinset_of_orbitCoordinate_injective
    w.base w.orbitCoordinate_injective

/-- Convert a witness into the downstream base-selection input. -/
noncomputable def toInput (w : OrbitBaseSelectionWitness h) :
    OrbitBaseSelectionInput h where
  base := w.base
  base_moved := w.base_moved
  pairwise_disjoint := w.pairwise_disjoint

/-- Constructor for witnesses when `base_moved` is not supplied separately:
global coordinate injectivity already forces it. -/
noncomputable def ofOrbitCoordinateInjective
    (base : Fin 56 → V)
    (hinj :
      Function.Injective
        (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (base qi.1))) :
    OrbitBaseSelectionWitness h where
  base := base
  base_moved := h.base_moved_of_orbitCoordinate_injective base hinj
  orbitCoordinate_injective := hinj

/-- The union of the selected 56 rotation orbits has cardinality `1064`. -/
theorem orbitFamilyUnion_card (w : OrbitBaseSelectionWitness h) :
    (h.orbitFamilyUnion w.base).card = 1064 := by
  simpa [OrbitBaseSelectionInput.orbitFamilyUnion, toInput] using
    w.toInput.orbitFamilyUnion_card

end OrbitBaseSelectionWitness

namespace OrbitBaseSelectionInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Direct constructor for `OrbitBaseSelectionInput` from global
orbit-coordinate injectivity. -/
noncomputable def ofOrbitCoordinateInjective
    (base : Fin 56 → V)
    (hinj :
      Function.Injective
        (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (base qi.1))) :
    OrbitBaseSelectionInput h :=
  h.toOrbitBaseSelectionInput_of_orbitCoordinate_injective base hinj

end OrbitBaseSelectionInput

end Moore57

/-!
# Bridging base-selection inputs back to coordinate witnesses

`OrbitBaseSelectionInput` is the downstream geometric input: it stores
representatives moved by rotation and pairwise disjoint rotation orbits.  This
file proves that those two fields already imply the global orbit-coordinate
injectivity used by `OrbitBaseSelectionWitness`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace OrbitBaseSelectionInput

variable {h : D19ActsOnMoore57 V Γ}

/-- The pairwise-disjoint selected orbits, together with injectivity on each
orbit coming from `base_moved`, imply global coordinate injectivity. -/
theorem orbitCoordinate_injective (input : OrbitBaseSelectionInput h) :
    Function.Injective
      (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (input.base qi.1)) := by
  intro qi rj heq
  rcases qi with ⟨q, i⟩
  rcases rj with ⟨r, j⟩
  have hqr : q = r := by
    by_contra hneq
    have hyq :
        h.rotation i (input.base q) ∈ h.rotationOrbitFinset (input.base q) := by
      exact (h.mem_rotationOrbitFinset (input.base q)
        (h.rotation i (input.base q))).mpr ⟨i, rfl⟩
    have hyr :
        h.rotation i (input.base q) ∈ h.rotationOrbitFinset (input.base r) := by
      exact (h.mem_rotationOrbitFinset (input.base r)
        (h.rotation i (input.base q))).mpr ⟨j, heq.symm⟩
    exact Finset.disjoint_left.mp (input.pairwise_disjoint q r hneq) hyq hyr
  subst r
  have hij : i = j := by
    apply input.W_injective q
    simpa [W] using heq
  subst j
  rfl

/-- Promote the downstream base-selection input to the stronger witness form. -/
noncomputable def toWitness (input : OrbitBaseSelectionInput h) :
    OrbitBaseSelectionWitness h where
  base := input.base
  base_moved := input.base_moved
  orbitCoordinate_injective := input.orbitCoordinate_injective

@[simp] theorem toWitness_base (input : OrbitBaseSelectionInput h) :
    input.toWitness.base = input.base :=
  rfl

@[simp] theorem toWitness_base_moved (input : OrbitBaseSelectionInput h) :
    input.toWitness.base_moved = input.base_moved :=
  rfl

@[simp] theorem toWitness_orbitCoordinate_injective
    (input : OrbitBaseSelectionInput h) :
    input.toWitness.orbitCoordinate_injective = input.orbitCoordinate_injective :=
  rfl

/-- Cardinality connection through the witness interface. -/
theorem orbitFamilyUnion_card_fromWitness (input : OrbitBaseSelectionInput h) :
    (h.orbitFamilyUnion input.toWitness.base).card = 1064 :=
  input.toWitness.orbitFamilyUnion_card

end OrbitBaseSelectionInput

namespace OrbitBaseSelectionWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructor for `OrbitBaseSelectionWitness` from the downstream
`OrbitBaseSelectionInput`. -/
noncomputable def ofInput (input : OrbitBaseSelectionInput h) :
    OrbitBaseSelectionWitness h :=
  input.toWitness

@[simp] theorem ofInput_base (input : OrbitBaseSelectionInput h) :
    (ofInput input).base = input.base :=
  rfl

@[simp] theorem ofInput_orbitCoordinate_injective
    (input : OrbitBaseSelectionInput h) :
    (ofInput input).orbitCoordinate_injective =
      input.orbitCoordinate_injective :=
  rfl

/-- Cardinality connection for witnesses constructed from an input. -/
theorem ofInput_orbitFamilyUnion_card (input : OrbitBaseSelectionInput h) :
    (h.orbitFamilyUnion (ofInput input).base).card = 1064 :=
  (ofInput input).orbitFamilyUnion_card

end OrbitBaseSelectionWitness

end Moore57

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

/-!
# Enumeration criteria for selecting the 56 rotation-orbit bases

This file gives higher-level constructors for `OrbitBaseSelectionWitness`.
Instead of proving injectivity of the concrete orbit-coordinate map directly,
one may provide a separate enumeration, an embedding, or a bijection with a
subtype of vertices, together with the statement that it agrees with the
rotation-coordinate map.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A coordinate enumeration of the selected rotation orbits.

The map `coord` is allowed to be any injective enumeration, as long as it agrees
pointwise with `(q, i) ↦ h.rotation i (base q)`. -/
structure OrbitBaseSelectionEnumeration (h : D19ActsOnMoore57 V Γ) where
  /-- One representative for each of the 56 rotation orbits. -/
  base : Fin 56 → V
  /-- The enumerating map for the `56 * 19` orbit coordinates. -/
  coord : Fin 56 × ZMod 19 → V
  /-- The enumeration agrees with the rotation-coordinate map. -/
  coord_eq_rotation :
    ∀ qi : Fin 56 × ZMod 19, coord qi = h.rotation qi.2 (base qi.1)
  /-- The enumeration has no repeated vertex. -/
  coord_injective : Function.Injective coord

namespace OrbitBaseSelectionEnumeration

variable {h : D19ActsOnMoore57 V Γ}

/-- The coordinate enumeration proves injectivity of the concrete
rotation-coordinate map required by `OrbitBaseSelectionWitness`. -/
theorem orbitCoordinate_injective (w : OrbitBaseSelectionEnumeration h) :
    Function.Injective
      (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (w.base qi.1)) := by
  intro qi qj heq
  apply w.coord_injective
  calc
    w.coord qi = h.rotation qi.2 (w.base qi.1) := w.coord_eq_rotation qi
    _ = h.rotation qj.2 (w.base qj.1) := heq
    _ = w.coord qj := (w.coord_eq_rotation qj).symm

/-- Convert a coordinate enumeration into the existing base-selection witness. -/
noncomputable def toWitness
    (w : OrbitBaseSelectionEnumeration h) :
    OrbitBaseSelectionWitness h :=
  OrbitBaseSelectionWitness.ofOrbitCoordinateInjective
    w.base w.orbitCoordinate_injective

/-- Convert a coordinate enumeration directly into the downstream input. -/
noncomputable def toInput
    (w : OrbitBaseSelectionEnumeration h) :
    OrbitBaseSelectionInput h :=
  w.toWitness.toInput

/-- The selected orbit-family union has cardinality `1064`. -/
theorem orbitFamilyUnion_card (w : OrbitBaseSelectionEnumeration h) :
    (h.orbitFamilyUnion w.base).card = 1064 :=
  w.toWitness.orbitFamilyUnion_card

/-- The downstream input produced from the enumeration has orbit-union
cardinality `1064`. -/
theorem input_orbitFamilyUnion_card (w : OrbitBaseSelectionEnumeration h) :
    w.toInput.orbitFamilyUnion.card = 1064 :=
  w.toInput.orbitFamilyUnion_card

end OrbitBaseSelectionEnumeration

/-- An embedding-valued coordinate witness for the selected rotation orbits. -/
structure OrbitBaseSelectionEmbeddingWitness (h : D19ActsOnMoore57 V Γ) where
  /-- One representative for each of the 56 rotation orbits. -/
  base : Fin 56 → V
  /-- An embedded copy of the orbit-coordinate type inside the vertex type. -/
  embedding : Fin 56 × ZMod 19 ↪ V
  /-- The embedding agrees with the rotation-coordinate map. -/
  embedding_eq_rotation :
    ∀ qi : Fin 56 × ZMod 19, embedding qi = h.rotation qi.2 (base qi.1)

namespace OrbitBaseSelectionEmbeddingWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- An embedding witness is a coordinate enumeration. -/
noncomputable def toEnumeration
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    OrbitBaseSelectionEnumeration h where
  base := w.base
  coord := w.embedding
  coord_eq_rotation := w.embedding_eq_rotation
  coord_injective := w.embedding.injective

/-- Convert an embedding witness into the existing base-selection witness. -/
noncomputable def toWitness
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    OrbitBaseSelectionWitness h :=
  w.toEnumeration.toWitness

/-- Convert an embedding witness directly into the downstream input. -/
noncomputable def toInput
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    OrbitBaseSelectionInput h :=
  w.toWitness.toInput

/-- The selected orbit-family union has cardinality `1064`. -/
theorem orbitFamilyUnion_card (w : OrbitBaseSelectionEmbeddingWitness h) :
    (h.orbitFamilyUnion w.base).card = 1064 :=
  w.toWitness.orbitFamilyUnion_card

end OrbitBaseSelectionEmbeddingWitness

/-- A bijection from orbit coordinates to a vertex subtype witnessing the
selected rotation orbits.

This is useful when the `56 * 19` vertices have first been isolated as a set
and the coordinate construction is naturally an equivalence with that subtype. -/
structure OrbitBaseSelectionSubtypeEquivWitness (h : D19ActsOnMoore57 V Γ) where
  /-- One representative for each of the 56 rotation orbits. -/
  base : Fin 56 → V
  /-- The vertex set covered by the coordinates. -/
  carrier : Set V
  /-- A bijection from orbit coordinates to the carrier subtype. -/
  coordEquiv : Fin 56 × ZMod 19 ≃ carrier
  /-- The bijection agrees with the rotation-coordinate map after coercion to
  vertices. -/
  coord_eq_rotation :
    ∀ qi : Fin 56 × ZMod 19,
      (coordEquiv qi : V) = h.rotation qi.2 (base qi.1)

namespace OrbitBaseSelectionSubtypeEquivWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- A subtype-equivalence witness proves injectivity of the concrete
rotation-coordinate map. -/
theorem orbitCoordinate_injective
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    Function.Injective
      (fun qi : Fin 56 × ZMod 19 => h.rotation qi.2 (w.base qi.1)) := by
  intro qi qj heq
  apply w.coordEquiv.injective
  apply Subtype.ext
  calc
    (w.coordEquiv qi : V) = h.rotation qi.2 (w.base qi.1) :=
      w.coord_eq_rotation qi
    _ = h.rotation qj.2 (w.base qj.1) := heq
    _ = (w.coordEquiv qj : V) := (w.coord_eq_rotation qj).symm

/-- Convert a subtype-equivalence witness into the existing base-selection
witness. -/
noncomputable def toWitness
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    OrbitBaseSelectionWitness h :=
  OrbitBaseSelectionWitness.ofOrbitCoordinateInjective
    w.base w.orbitCoordinate_injective

/-- Convert a subtype-equivalence witness directly into the downstream input. -/
noncomputable def toInput
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    OrbitBaseSelectionInput h :=
  w.toWitness.toInput

/-- The selected orbit-family union has cardinality `1064`. -/
theorem orbitFamilyUnion_card
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    (h.orbitFamilyUnion w.base).card = 1064 :=
  w.toWitness.orbitFamilyUnion_card

end OrbitBaseSelectionSubtypeEquivWitness

namespace OrbitBaseSelectionWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Build a base-selection witness from an injective coordinate enumeration
that agrees with the rotation-coordinate map. -/
noncomputable def ofEnumeration
    (w : OrbitBaseSelectionEnumeration h) :
    OrbitBaseSelectionWitness h :=
  w.toWitness

/-- Build a base-selection witness from an embedding-valued coordinate
enumeration. -/
noncomputable def ofEmbedding
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    OrbitBaseSelectionWitness h :=
  w.toWitness

/-- Build a base-selection witness from a bijection with a vertex subtype. -/
noncomputable def ofSubtypeEquiv
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    OrbitBaseSelectionWitness h :=
  w.toWitness

end OrbitBaseSelectionWitness

namespace OrbitBaseSelectionInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Build the downstream base-selection input from an injective coordinate
enumeration that agrees with the rotation-coordinate map. -/
noncomputable def ofEnumeration
    (w : OrbitBaseSelectionEnumeration h) :
    OrbitBaseSelectionInput h :=
  w.toInput

/-- Build the downstream base-selection input from an embedding-valued
coordinate enumeration. -/
noncomputable def ofEmbedding
    (w : OrbitBaseSelectionEmbeddingWitness h) :
    OrbitBaseSelectionInput h :=
  w.toInput

/-- Build the downstream base-selection input from a bijection with a vertex
subtype. -/
noncomputable def ofSubtypeEquiv
    (w : OrbitBaseSelectionSubtypeEquivWitness h) :
    OrbitBaseSelectionInput h :=
  w.toInput

end OrbitBaseSelectionInput

end Moore57

