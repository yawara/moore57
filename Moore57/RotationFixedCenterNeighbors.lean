import Moore57.RotationFixedCenter
import Moore57.RotationOrbitFinset

/-!
# Neighbors of the fixed rotation center

The unique rotation-fixed center is the only vertex fixed by `rotation 1`.
Hence every neighbor of that center is moved by `rotation 1`, so its rotation
orbit has size `19`.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A neighbor of the fixed rotation center is moved by rotation `1`. -/
theorem rotationFixedCenter_neighbor_moved
    (h : D19ActsOnMoore57 V Γ) {v : V}
    (hv : Γ.Adj h.rotationFixedCenter v) :
    h.rotation 1 v ≠ v := by
  intro hfixed
  have hvcenter : v = h.rotationFixedCenter :=
    h.eq_rotationFixedCenter_of_rotation_one_fixed hfixed
  exact (Γ.ne_of_adj hv) hvcenter.symm

/-- A neighbor of the fixed rotation center has a rotation orbit of size `19`.
-/
theorem rotationOrbitFinset_card_neighbor_rotationFixedCenter
    (h : D19ActsOnMoore57 V Γ) {v : V}
    (hv : Γ.Adj h.rotationFixedCenter v) :
    (h.rotationOrbitFinset v).card = 19 :=
  h.rotationOrbitFinset_card_eq_nineteen_of_nonzero_moved'
    (d := 1) (x := v) (by decide)
    (h.rotationFixedCenter_neighbor_moved hv)

/-- The rotation orbit of a neighbor of the fixed center stays in the
neighbor set of the fixed center. -/
theorem rotationOrbitFinset_subset_neighborFinset_rotationFixedCenter
    (h : D19ActsOnMoore57 V Γ) {v : V}
    (hv : Γ.Adj h.rotationFixedCenter v) :
    h.rotationOrbitFinset v ⊆ Γ.neighborFinset h.rotationFixedCenter := by
  intro y hy
  rcases (h.mem_rotationOrbitFinset v y).mp hy with ⟨i, hi⟩
  have hadj :
      Γ.Adj (h.rotation i h.rotationFixedCenter) (h.rotation i v) := by
    simpa [D19ActsOnMoore57.rotation] using
      (h.smul_adj (DihedralGroup.r i) h.rotationFixedCenter v).mp hv
  rw [SimpleGraph.mem_neighborFinset]
  simpa [h.rotationFixedCenter_fixed_rotation i, hi] using hadj

end D19ActsOnMoore57

end Moore57
