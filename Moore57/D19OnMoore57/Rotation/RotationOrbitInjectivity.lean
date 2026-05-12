import Moore57.D19OnMoore57.Rotation.RotationFixedSets
import Moore57.Moore57Graph.Moore57Definition
import Moore57.D19OnMoore57.Action.D19Action

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- If two rotation orbit positions agree, the corresponding difference fixes
the original point. -/
theorem rotation_sub_fixed_of_rotation_eq
    (h : D19ActsOnMoore57 V Γ) {i j : ZMod 19} {x : V}
    (hij : h.rotation i x = h.rotation j x) :
    h.rotation (i - j) x = x := by
  have hfix_at_j : h.rotation (i - j) (h.rotation j x) = h.rotation j x := by
    calc
      h.rotation (i - j) (h.rotation j x)
          = (h.rotation (i - j) * h.rotation j) x := by
              simp [Equiv.Perm.mul_apply]
      _ = h.rotation ((i - j) + j) x := by
              rw [← h.rotation_add]
      _ = h.rotation i x := by
              rw [sub_add_cancel]
      _ = h.rotation j x := hij
  have hcomm_at_x :
      h.rotation j (h.rotation (i - j) x) =
        h.rotation (i - j) (h.rotation j x) := by
    calc
      h.rotation j (h.rotation (i - j) x)
          = (h.rotation j * h.rotation (i - j)) x := by
              simp [Equiv.Perm.mul_apply]
      _ = h.rotation (j + (i - j)) x := by
              rw [← h.rotation_add]
      _ = h.rotation ((i - j) + j) x := by
              rw [add_comm]
      _ = (h.rotation (i - j) * h.rotation j) x := by
              rw [h.rotation_add]
      _ = h.rotation (i - j) (h.rotation j x) := by
              simp [Equiv.Perm.mul_apply]
  exact (h.rotation j).injective (hcomm_at_x.trans hfix_at_j)

/-- An orbit map is injective if no nonzero rotation fixes the point. -/
theorem rotation_orbit_injective_of_no_nonzero_fixed
    (h : D19ActsOnMoore57 V Γ) {x : V}
    (hnot_fixed : ∀ d : ZMod 19, d ≠ 0 → h.rotation d x ≠ x) :
    Function.Injective (fun n : ZMod 19 => h.rotation n x) := by
  intro i j hij
  have hfix : h.rotation (i - j) x = x :=
    h.rotation_sub_fixed_of_rotation_eq hij
  have hdiff_zero : i - j = 0 := by
    by_contra hdiff_ne_zero
    exact hnot_fixed (i - j) hdiff_ne_zero hfix
  exact sub_eq_zero.mp hdiff_zero

/-- In the order-19 rotation subgroup, if one nonzero rotation moves `x`, then
the full rotation orbit map through `x` is injective. -/
theorem rotation_orbit_injective_of_nonzero_moved
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x : V}
    (hd : d ≠ 0) (hmove : h.rotation d x ≠ x) :
    Function.Injective (fun n : ZMod 19 => h.rotation n x) := by
  apply h.rotation_orbit_injective_of_no_nonzero_fixed
  intro e he hfix
  have hx_fixed_e : x ∈ fixedVertexSet (h.rotation e) := by
    simpa [fixedVertexSet] using hfix
  have hfixed_sets :
      fixedVertexSet (h.rotation e) = fixedVertexSet (h.rotation d) :=
    h.fixedVertexSet_rotation_eq_of_nonzero he hd
  have hx_fixed_d : x ∈ fixedVertexSet (h.rotation d) := by
    simpa [hfixed_sets] using hx_fixed_e
  exact hmove (by simpa [fixedVertexSet] using hx_fixed_d)

end D19ActsOnMoore57

end Moore57
