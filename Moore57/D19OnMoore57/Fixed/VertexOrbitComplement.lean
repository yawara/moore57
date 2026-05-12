import Moore57.D19OnMoore57.Rotation.FixedDataBridge
import Moore57.D19OnMoore57.Rotation.OrbitFinset

/-!
# Fixed vertices and moved rotation orbits

This file packages elementary cardinality consequences of `RotationFixedData`
for a nontrivial rotation, together with a convenience wrapper for full
rotation orbits of moved vertices.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Under `RotationFixedData`, the fixed-vertex subtype of any nontrivial
rotation has exactly one element. -/
theorem fixedVertexSet_rotation_one_card_of_RotationFixedData
    (h : D19ActsOnMoore57 V Γ) (hfixed : RotationFixedData h.rotation)
    {d : ZMod 19} (hd : d ≠ 0) :
    Fintype.card (fixedVertexSet (h.rotation d)) = 1 := by
  simpa [fixedVertexCount_eq_card_fixedVertexSet] using
    hfixed.rotation_fixed d hd

/-- Finset version of
`fixedVertexSet_rotation_one_card_of_RotationFixedData`. -/
theorem fixedVertexSet_rotation_toFinset_card_one_of_RotationFixedData
    (h : D19ActsOnMoore57 V Γ) (hfixed : RotationFixedData h.rotation)
    {d : ZMod 19} (hd : d ≠ 0) :
    (fixedVertexSet (h.rotation d)).toFinset.card = 1 := by
  rw [Set.toFinset_card]
  exact h.fixedVertexSet_rotation_one_card_of_RotationFixedData hfixed hd

/-- The fixed and moved vertex finsets partition all vertices. -/
theorem fixedVertexSet_rotation_toFinset_card_add_compl_card
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) :
    (fixedVertexSet (h.rotation d)).toFinset.card +
      (fixedVertexSet (h.rotation d)).toFinsetᶜ.card = Fintype.card V := by
  classical
  rw [Finset.card_compl]
  exact Nat.add_sub_of_le (Finset.card_le_univ _)

/-- The moved-vertex complement of the unique fixed vertex has cardinality
`3249`. -/
theorem fixedVertexSet_rotation_toFinset_compl_card_of_RotationFixedData
    (h : D19ActsOnMoore57 V Γ) (hfixed : RotationFixedData h.rotation)
    {d : ZMod 19} (hd : d ≠ 0) :
    (fixedVertexSet (h.rotation d)).toFinsetᶜ.card = 3249 := by
  classical
  rw [Finset.card_compl]
  rw [h.card_vertices]
  rw [h.fixedVertexSet_rotation_toFinset_card_one_of_RotationFixedData hfixed hd]

/-- If a vertex is not fixed by one nonzero rotation, its rotation orbit has
all nineteen points. -/
theorem rotationOrbitFinset_card_eq_nineteen_of_not_mem_fixedVertexSet
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x : V}
    (hd : d ≠ 0) (hx : x ∉ fixedVertexSet (h.rotation d)) :
    (h.rotationOrbitFinset x).card = 19 := by
  exact h.card_rotationOrbitFinset_eq_nineteen_of_nonzero_moved hd (by
    simpa [fixedVertexSet] using hx)

/-- If one nonzero rotation moves a vertex, its rotation orbit has all
nineteen points. -/
theorem rotationOrbitFinset_card_eq_nineteen_of_nonzero_moved'
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x : V}
    (hd : d ≠ 0) (hmove : h.rotation d x ≠ x) :
    (h.rotationOrbitFinset x).card = 19 :=
  h.card_rotationOrbitFinset_eq_nineteen_of_nonzero_moved hd hmove

end D19ActsOnMoore57

end Moore57
