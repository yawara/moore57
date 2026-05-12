import Moore57.D19OnMoore57.Rotation.OrbitInjectivity

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The finite set of vertices in the rotation orbit of `x`. -/
noncomputable def rotationOrbitFinset (h : D19ActsOnMoore57 V Γ) (x : V) : Finset V :=
  (Finset.univ : Finset (ZMod 19)).image fun i => h.rotation i x

/-- Membership in the rotation-orbit finset is exactly being a rotation of `x`. -/
theorem mem_rotationOrbitFinset (h : D19ActsOnMoore57 V Γ) (x y : V) :
    y ∈ h.rotationOrbitFinset x ↔ ∃ i : ZMod 19, h.rotation i x = y := by
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨i, _hi, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Convenient name for injectivity of the rotation orbit map when one nonzero
rotation moves `x`. -/
theorem rotationOrbitW_injective_of_nonzero_moved
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x : V}
    (hd : d ≠ 0) (hmove : h.rotation d x ≠ x) :
    Function.Injective (fun i : ZMod 19 => h.rotation i x) :=
  h.rotation_orbit_injective_of_nonzero_moved hd hmove

/-- If some nonzero rotation moves `x`, then the rotation orbit through `x`
has all nineteen vertices. -/
theorem card_rotationOrbitFinset_eq_nineteen_of_nonzero_moved
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x : V}
    (hd : d ≠ 0) (hmove : h.rotation d x ≠ x) :
    (h.rotationOrbitFinset x).card = 19 := by
  rw [rotationOrbitFinset]
  rw [Finset.card_image_of_injective _ (h.rotationOrbitW_injective_of_nonzero_moved hd hmove)]
  simp

end D19ActsOnMoore57

end Moore57
