import Moore57.D19OnMoore57.Orbit.OrbitBaseSelectionCriteria

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
