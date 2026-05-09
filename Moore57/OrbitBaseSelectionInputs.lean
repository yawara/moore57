import Moore57.OrbitFamilyPartition
import Moore57.D19ActionOrbitConcreteData
import Moore57.D19OrbitContributionData

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
