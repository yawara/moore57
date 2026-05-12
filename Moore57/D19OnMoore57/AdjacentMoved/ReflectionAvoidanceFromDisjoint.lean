import Moore57.D19OnMoore57.AdjacentMoved.ReflectionAvoidance

set_option maxRecDepth 10000

/-!
# Reflected avoidance from cross-disjoint orbit families

The existing direction proves cross-disjointness from reflected-base avoidance.
This file records the converse packaging direction.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- If every selected orbit is disjoint from every reflected selected orbit,
then no reflected selected base lies in the selected orbit-family union. -/
theorem reflection_not_mem_orbitFamilyUnion_of_cross_disjoint
    (h : D19ActsOnMoore57 V Γ)
    (input : OrbitBaseSelectionInput h) (k : ZMod 19)
    (hcross : ∀ q r : Fin 56,
      Disjoint
        (h.rotationOrbitFinset (input.base q))
        (h.rotationOrbitFinset
          (h.smul (DihedralGroup.sr k) (input.base r)))) :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉
        input.orbitFamilyUnion := by
  intro r href
  rcases (input.mem_orbitFamilyUnion
      (h.smul (DihedralGroup.sr k) (input.base r))).mp href with
    ⟨q, i, hi⟩
  have hinOriginal :
      h.smul (DihedralGroup.sr k) (input.base r) ∈
        h.rotationOrbitFinset (input.base q) :=
    (h.mem_rotationOrbitFinset (input.base q)
      (h.smul (DihedralGroup.sr k) (input.base r))).mpr ⟨i, hi⟩
  have hinReflected :
      h.smul (DihedralGroup.sr k) (input.base r) ∈
        h.rotationOrbitFinset
          (h.smul (DihedralGroup.sr k) (input.base r)) :=
    (h.mem_rotationOrbitFinset
      (h.smul (DihedralGroup.sr k) (input.base r))
      (h.smul (DihedralGroup.sr k) (input.base r))).mpr ⟨0, by simp⟩
  exact Finset.disjoint_left.mp (hcross q r) hinOriginal hinReflected

end D19ActsOnMoore57

end Moore57
