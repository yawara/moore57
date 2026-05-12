import Moore57.D19OnMoore57.Orbit.BaseSelectionInputs
import Moore57.D19OnMoore57.Rotation.OrbitFinset

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
