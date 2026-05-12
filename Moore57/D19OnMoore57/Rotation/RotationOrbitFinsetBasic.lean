import Moore57.D19OnMoore57.Rotation.RotationOrbitFinset

/-!
# Basic equalities for rotation-orbit finsets

These small orbit-normalization lemmas are useful when selecting orbit
representatives.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Starting a rotation orbit at a rotated point gives the same orbit finset. -/
theorem rotationOrbitFinset_rotation_eq
    (h : D19ActsOnMoore57 V Γ) (i : ZMod 19) (x : V) :
    h.rotationOrbitFinset (h.rotation i x) = h.rotationOrbitFinset x := by
  ext y
  rw [h.mem_rotationOrbitFinset, h.mem_rotationOrbitFinset]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨j + i, ?_⟩
    simpa [Equiv.Perm.mul_apply] using
      congrArg (fun σ : Equiv.Perm V => σ x) (h.rotation_add j i)
  · rintro ⟨j, rfl⟩
    refine ⟨j - i, ?_⟩
    calc
      h.rotation (j - i) (h.rotation i x)
          = h.rotation ((j - i) + i) x := by
              simpa [Equiv.Perm.mul_apply] using
                congrArg (fun σ : Equiv.Perm V => σ x)
                  (h.rotation_add (j - i) i).symm
      _ = h.rotation j x := by
              rw [sub_add_cancel]

/-- If `y` belongs to the rotation orbit of `x`, then the two orbit finsets are
equal. -/
theorem rotationOrbitFinset_eq_of_mem
    (h : D19ActsOnMoore57 V Γ) {x y : V}
    (hy : y ∈ h.rotationOrbitFinset x) :
    h.rotationOrbitFinset y = h.rotationOrbitFinset x := by
  rcases (h.mem_rotationOrbitFinset x y).mp hy with ⟨i, rfl⟩
  exact h.rotationOrbitFinset_rotation_eq i x

/-- If `y` is not in the rotation orbit of `x`, the two orbit finsets are
disjoint. -/
theorem disjoint_rotationOrbitFinset_of_not_mem
    (h : D19ActsOnMoore57 V Γ) {x y : V}
    (hy : y ∉ h.rotationOrbitFinset x) :
    Disjoint (h.rotationOrbitFinset x) (h.rotationOrbitFinset y) := by
  rw [Finset.disjoint_left]
  intro z hzx hzy
  apply hy
  have hzx_eq : h.rotationOrbitFinset z = h.rotationOrbitFinset x :=
    h.rotationOrbitFinset_eq_of_mem hzx
  have hzy_eq : h.rotationOrbitFinset z = h.rotationOrbitFinset y :=
    h.rotationOrbitFinset_eq_of_mem hzy
  have hyy : y ∈ h.rotationOrbitFinset y :=
    (h.mem_rotationOrbitFinset y y).mpr ⟨0, by simp⟩
  have hyz : y ∈ h.rotationOrbitFinset z := by
    simpa [hzy_eq] using hyy
  simpa [hzx_eq] using hyz

/-- Non-disjoint rotation orbits are equal. -/
theorem rotationOrbitFinset_eq_of_not_disjoint
    (h : D19ActsOnMoore57 V Γ) {x y : V}
    (hxy : ¬ Disjoint (h.rotationOrbitFinset x) (h.rotationOrbitFinset y)) :
    h.rotationOrbitFinset x = h.rotationOrbitFinset y := by
  by_cases hy : y ∈ h.rotationOrbitFinset x
  · exact (h.rotationOrbitFinset_eq_of_mem hy).symm
  · exact False.elim (hxy (h.disjoint_rotationOrbitFinset_of_not_mem hy))

end D19ActsOnMoore57

end Moore57
