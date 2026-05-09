import Moore57.RotationOrbitFinset
import Moore57.FixedVertexOrbitComplement

/-!
# Finite families of rotation orbits

This file packages coarse finset facts for a finite indexed family of
rotation orbits.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The union of a finite indexed family of rotation-orbit finsets. -/
noncomputable def orbitFamilyUnion
    (h : D19ActsOnMoore57 V Γ) {ι : Type*} [Fintype ι] (base : ι → V) :
    Finset V :=
  (Finset.univ : Finset ι).biUnion fun q => h.rotationOrbitFinset (base q)

/-- Membership in an orbit-family union is exactly being a rotation of one of
the chosen base vertices. -/
theorem mem_orbitFamilyUnion
    (h : D19ActsOnMoore57 V Γ) {ι : Type*} [Fintype ι] (base : ι → V) (y : V) :
    y ∈ h.orbitFamilyUnion base ↔
      ∃ q : ι, ∃ i : ZMod 19, h.rotation i (base q) = y := by
  classical
  simp [orbitFamilyUnion, h.mem_rotationOrbitFinset]

/-- Cardinality of an orbit-family union as the sum of cardinalities, assuming
the indexed orbit finsets are pairwise disjoint. -/
theorem orbitFamilyUnion_card_eq_sum_of_pairwiseDisjoint
    (h : D19ActsOnMoore57 V Γ) {ι : Type*} [Fintype ι] (base : ι → V)
    (hdisj : ∀ ⦃q r : ι⦄, q ≠ r →
      Disjoint (h.rotationOrbitFinset (base q)) (h.rotationOrbitFinset (base r))) :
    (h.orbitFamilyUnion base).card =
      ∑ q : ι, (h.rotationOrbitFinset (base q)).card := by
  classical
  simpa [orbitFamilyUnion] using
    (Finset.card_biUnion
      (s := (Finset.univ : Finset ι))
      (t := fun q : ι => h.rotationOrbitFinset (base q))
      (by
        intro q _hq r _hr hqr
        exact hdisj hqr))

/-- A pairwise-disjoint family of size-`19` rotation orbits has cardinality
`19` times the number of indices. -/
theorem orbitFamilyUnion_card_eq_nineteen_mul_card
    (h : D19ActsOnMoore57 V Γ) {ι : Type*} [Fintype ι] (base : ι → V)
    (hdisj : ∀ ⦃q r : ι⦄, q ≠ r →
      Disjoint (h.rotationOrbitFinset (base q)) (h.rotationOrbitFinset (base r)))
    (hcard : ∀ q : ι, (h.rotationOrbitFinset (base q)).card = 19) :
    (h.orbitFamilyUnion base).card = 19 * Fintype.card ι := by
  classical
  rw [h.orbitFamilyUnion_card_eq_sum_of_pairwiseDisjoint base hdisj]
  calc
    (∑ q : ι, (h.rotationOrbitFinset (base q)).card) = ∑ _q : ι, 19 := by
      simp [hcard]
    _ = 19 * Fintype.card ι := by
      rw [show (∑ _q : ι, 19) = (Finset.univ : Finset ι).card * 19 by
        exact Finset.sum_const_nat
          (s := (Finset.univ : Finset ι))
          (m := 19)
          (f := fun _q : ι => 19)
          (by intro _q _hq; rfl)]
      simp [Finset.card_univ, Nat.mul_comm]

/-- The `Fin 56` specialization of
`orbitFamilyUnion_card_eq_nineteen_mul_card`. -/
theorem orbitFamilyUnion_card_eq_1064_of_fin56
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V)
    (hdisj : ∀ ⦃q r : Fin 56⦄, q ≠ r →
      Disjoint (h.rotationOrbitFinset (base q)) (h.rotationOrbitFinset (base r)))
    (hcard : ∀ q : Fin 56, (h.rotationOrbitFinset (base q)).card = 19) :
    (h.orbitFamilyUnion base).card = 1064 := by
  simpa using
    (h.orbitFamilyUnion_card_eq_nineteen_mul_card base hdisj hcard)

/-- If every base vertex is moved by rotation by `1`, each indexed orbit map is
injective and each corresponding orbit finset has cardinality `19`.

The disjointness hypothesis is included for family-level partition uses; the
two conclusions are orbit-local consequences of `base_moved`. -/
theorem orbitFamily_injective_and_card_nineteen_of_pairwiseDisjoint_base_moved
    (h : D19ActsOnMoore57 V Γ) {ι : Type*} [Fintype ι] (base : ι → V)
    (hdisj : ∀ ⦃q r : ι⦄, q ≠ r →
      Disjoint (h.rotationOrbitFinset (base q)) (h.rotationOrbitFinset (base r)))
    (base_moved : ∀ q : ι, h.rotation 1 (base q) ≠ base q) :
    (∀ q : ι, Function.Injective (fun i : ZMod 19 => h.rotation i (base q))) ∧
      ∀ q : ι, (h.rotationOrbitFinset (base q)).card = 19 := by
  have _ := hdisj
  constructor
  · intro q
    exact h.rotationOrbitW_injective_of_nonzero_moved
      (d := 1) (x := base q) (by decide) (base_moved q)
  · intro q
    exact h.rotationOrbitFinset_card_eq_nineteen_of_nonzero_moved'
      (d := 1) (x := base q) (by decide) (base_moved q)

end D19ActsOnMoore57

end Moore57
