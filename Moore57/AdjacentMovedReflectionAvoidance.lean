import Moore57.AdjacentMovedReflectionCrossDisjoint

-- The orbit-family membership proof below elaborates through several nested
-- finset and orbit-membership equivalences.
set_option maxRecDepth 10000

/-!
# Reflection-copy cross disjointness from avoidance

This file reduces the mixed original/reflection orbit disjointness condition to
the smaller condition that no reflected selected base lies in the selected
rotation-orbit union.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- Rotation orbit membership is symmetric: if `y` is a rotation translate of
`x`, then `x` is a rotation translate of `y`. -/
theorem rotationOrbitFinset_mem_symm {x y : V}
    (hy : y ∈ h.rotationOrbitFinset x) :
    x ∈ h.rotationOrbitFinset y := by
  rcases (h.mem_rotationOrbitFinset x y).mp hy with ⟨i, rfl⟩
  exact (h.mem_rotationOrbitFinset (h.rotation i x) x).mpr
    ⟨-i, by
      calc
        h.rotation (-i) (h.rotation i x)
            = (h.rotation (-i) * h.rotation i) x := by
                simp [Equiv.Perm.mul_apply]
        _ = h.rotation ((-i) + i) x := by
                rw [← h.rotation_add]
        _ = x := by
                simp⟩

/-- If no reflected selected base point lies in the selected orbit-family
union, then every selected orbit is disjoint from every reflected selected
orbit. -/
theorem cross_disjoint_of_reflection_not_mem_orbitFamilyUnion
    (input : OrbitBaseSelectionInput h) (k : ZMod 19)
    (havoid : ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion) :
    ∀ q r : Fin 56,
      Disjoint
        (h.rotationOrbitFinset (input.base q))
        (h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) (input.base r))) := by
  classical
  intro q r
  rw [Finset.disjoint_left]
  intro y hyq hyr
  have href_in_orbit_y :
      h.smul (DihedralGroup.sr k) (input.base r) ∈ h.rotationOrbitFinset y :=
    h.rotationOrbitFinset_mem_symm hyr
  rcases (h.mem_rotationOrbitFinset y
      (h.smul (DihedralGroup.sr k) (input.base r))).mp href_in_orbit_y with
    ⟨j, hj⟩
  rcases (h.mem_rotationOrbitFinset (input.base q) y).mp hyq with ⟨i, rfl⟩
  have href_eq :
      h.rotation (j + i) (input.base q) =
        h.smul (DihedralGroup.sr k) (input.base r) := by
    calc
      h.rotation (j + i) (input.base q)
          = (h.rotation j * h.rotation i) (input.base q) := by
              rw [h.rotation_add]
      _ = h.rotation j (h.rotation i (input.base q)) := by
              simp [Equiv.Perm.mul_apply]
      _ = h.smul (DihedralGroup.sr k) (input.base r) := hj
  have hrefUnion :
      h.smul (DihedralGroup.sr k) (input.base r) ∈ input.orbitFamilyUnion := by
    have hrefUnion' :
        h.smul (DihedralGroup.sr k) (input.base r) ∈
          h.orbitFamilyUnion input.base :=
      (h.mem_orbitFamilyUnion input.base
        (h.smul (DihedralGroup.sr k) (input.base r))).mpr
          ⟨q, j + i, href_eq⟩
    simpa [OrbitBaseSelectionInput.orbitFamilyUnion] using hrefUnion'
  exact (havoid r) hrefUnion

/-- Constructor wrapper: the reflected-base avoidance condition gives the
pairwise disjointness of the two reflection-copy orbit families. -/
theorem pairwiseDisjoint_reflectionCopyBase_of_reflection_not_mem_orbitFamilyUnion
    (input : OrbitBaseSelectionInput h) (k : ZMod 19)
    (havoid : ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion) :
    ((Finset.univ : Finset (Fin 2 × Fin 56)) : Set (Fin 2 × Fin 56)).PairwiseDisjoint
      (fun i => h.rotationOrbitFinset (reflectionCopyBase h input.base k i)) :=
  h.pairwiseDisjoint_reflectionCopyBase_of_base_cross input k
    (h.cross_disjoint_of_reflection_not_mem_orbitFamilyUnion input k havoid)

end D19ActsOnMoore57

end Moore57
