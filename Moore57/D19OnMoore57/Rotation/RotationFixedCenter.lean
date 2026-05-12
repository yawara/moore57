import Moore57.D19OnMoore57.Rotation.RotationFixedCountUnique
import Moore57.D19OnMoore57.Rotation.RotationFixedRegularity
import Moore57.D19OnMoore57.Rotation.RotationFixedSets
import Moore57.D19OnMoore57.Reflection.ReflectionOrbitTools

/-!
# Fixed center for the rotation subgroup

This file names the unique vertex fixed by rotation `1`, using the fixed-count
theorem, and records that the same vertex is fixed by every rotation and by
every reflection.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Rotation by `1` has a unique fixed vertex. -/
theorem existsUnique_rotation_one_fixed
    (h : D19ActsOnMoore57 V Γ) :
    ∃! v : V, h.rotation 1 v = v :=
  h.existsUnique_rotation_one_fixed_of_fixedVertexCount_eq_one
    h.rotation_one_fixedVertexCount_eq_one

/-- The chosen center fixed by rotation `1`. -/
noncomputable def rotationFixedCenter
    (h : D19ActsOnMoore57 V Γ) : V :=
  Classical.choose h.existsUnique_rotation_one_fixed

/-- The chosen center is fixed by rotation `1`. -/
theorem rotationFixedCenter_fixed_rotation_one
    (h : D19ActsOnMoore57 V Γ) :
    h.rotation 1 h.rotationFixedCenter = h.rotationFixedCenter :=
  (Classical.choose_spec h.existsUnique_rotation_one_fixed).1

/-- Any vertex fixed by rotation `1` is the chosen center. -/
theorem eq_rotationFixedCenter_of_rotation_one_fixed
    (h : D19ActsOnMoore57 V Γ) {v : V}
    (hv : h.rotation 1 v = v) :
    v = h.rotationFixedCenter :=
  (Classical.choose_spec h.existsUnique_rotation_one_fixed).2 v hv

/-- The rotation-one fixed set is the singleton consisting of the chosen
center. -/
theorem fixedVertexSet_rotation_one_eq_singleton_rotationFixedCenter
    (h : D19ActsOnMoore57 V Γ) :
    fixedVertexSet (h.rotation 1) = ({h.rotationFixedCenter} : Set V) := by
  ext v
  rw [mem_fixedVertexSet, Set.mem_singleton_iff]
  constructor
  · exact h.eq_rotationFixedCenter_of_rotation_one_fixed
  · intro hv
    rw [hv]
    exact h.rotationFixedCenter_fixed_rotation_one

/-- The chosen center is fixed by every rotation. -/
theorem rotationFixedCenter_fixed_rotation
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) :
    h.rotation d h.rotationFixedCenter = h.rotationFixedCenter := by
  by_cases hd : d = 0
  · subst d
    simp
  · have hone : (1 : ZMod 19) ≠ 0 := by decide
    have hset :
        fixedVertexSet (h.rotation 1) = fixedVertexSet (h.rotation d) :=
      h.fixedVertexSet_rotation_eq_of_nonzero hone hd
    have hc_one : h.rotationFixedCenter ∈ fixedVertexSet (h.rotation 1) := by
      rw [mem_fixedVertexSet]
      exact h.rotationFixedCenter_fixed_rotation_one
    have hc_d : h.rotationFixedCenter ∈ fixedVertexSet (h.rotation d) := by
      simpa [hset] using hc_one
    exact mem_fixedVertexSet.mp hc_d

/-- Every reflection fixes the chosen rotation center. -/
theorem reflection_smul_rotationFixedCenter
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    h.smul (DihedralGroup.sr k) h.rotationFixedCenter = h.rotationFixedCenter := by
  have hneg :
      h.rotation (-1 : ZMod 19) h.rotationFixedCenter =
        h.rotationFixedCenter :=
    h.rotationFixedCenter_fixed_rotation (-1)
  have hfixed :
      h.rotation 1 (h.smul (DihedralGroup.sr k) h.rotationFixedCenter) =
        h.smul (DihedralGroup.sr k) h.rotationFixedCenter := by
    simpa [hneg] using
      h.rotation_neg_reflection_smul k (-1 : ZMod 19) h.rotationFixedCenter
  exact h.eq_rotationFixedCenter_of_rotation_one_fixed hfixed

end D19ActsOnMoore57

end Moore57
