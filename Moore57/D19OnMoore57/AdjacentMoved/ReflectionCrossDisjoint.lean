import Moore57.D19OnMoore57.AdjacentMoved.ReflectionCopyCriteria
import Moore57.D19OnMoore57.Orbit.BaseSelectionInputBridge

/-!
# Reflection-copy pairwise disjointness from base and cross disjointness

This file packages the disjointness bookkeeping for reflection-copy orbit
families.  Base/base disjointness comes from `OrbitBaseSelectionInput`, the
mixed base/reflection cases are supplied as a cross-disjointness hypothesis,
and reflection/reflection disjointness is transported across the reflection.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- A reflection transports disjointness of rotation orbits to disjointness of
the reflected rotation orbits. -/
theorem disjoint_reflection_rotationOrbitFinset_of_disjoint
    (k : ZMod 19) {x y : V}
    (hdisj : Disjoint (h.rotationOrbitFinset x) (h.rotationOrbitFinset y)) :
    Disjoint
      (h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) x))
      (h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) y)) := by
  classical
  rw [← h.reflection_image_rotationOrbitFinset k x,
    ← h.reflection_image_rotationOrbitFinset k y]
  rw [Finset.disjoint_left]
  intro z hzx hzy
  rcases Finset.mem_image.mp hzx with ⟨x', hx', hx'z⟩
  rcases Finset.mem_image.mp hzy with ⟨y', hy', hy'z⟩
  have hxy : x' = y' :=
    (h.smulEquiv (DihedralGroup.sr k)).injective (hx'z.trans hy'z.symm)
  exact Finset.disjoint_left.mp hdisj hx' (hxy ▸ hy')

/-- Reflection-copy orbit families are pairwise disjoint when the selected
base orbits are pairwise disjoint and every original orbit is disjoint from
every reflected orbit. -/
theorem pairwiseDisjoint_reflectionCopyBase_of_base_cross
    (input : OrbitBaseSelectionInput h) (k : ZMod 19)
    (hcross : ∀ q r : Fin 56,
      Disjoint
        (h.rotationOrbitFinset (input.base q))
        (h.rotationOrbitFinset (h.smul (DihedralGroup.sr k) (input.base r)))) :
    ((Finset.univ : Finset (Fin 2 × Fin 56)) : Set (Fin 2 × Fin 56)).PairwiseDisjoint
      (fun i => h.rotationOrbitFinset (reflectionCopyBase h input.base k i)) := by
  classical
  intro i _hi j _hj hij
  rcases i with ⟨side, q⟩
  rcases j with ⟨side', r⟩
  fin_cases side <;> fin_cases side'
  · have hqr : q ≠ r := by
      intro hqr
      exact hij (by simp [hqr])
    simpa [reflectionCopyBase] using input.pairwise_disjoint q r hqr
  · simpa [reflectionCopyBase] using hcross q r
  · simpa [reflectionCopyBase] using (hcross r q).symm
  · have hqr : q ≠ r := by
      intro hqr
      exact hij (by simp [hqr])
    simpa [reflectionCopyBase] using
      h.disjoint_reflection_rotationOrbitFinset_of_disjoint k
        (input.pairwise_disjoint q r hqr)

end D19ActsOnMoore57

end Moore57
