import Moore57.BranchOrbitBCSelectionCover

/-!
# Adjusting reflected branch representatives inside a rotation orbit

If a reflection sends `b0` somewhere in the rotation orbit of `c0`, then its
reflection parameter can be shifted so that it sends `b0` exactly to `c0`.
This keeps the geometric boundary closer to the natural orbit-level statement.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCFromCenter

variable {h : D19ActsOnMoore57 V Γ}

/-- A reflected image landing in the C-side branch orbit can be reparameterized
to land on the chosen representative `c0` itself. -/
theorem exists_reflection_smul_b0_eq_c0_of_reflection_smul_b0_mem_c0_orbit
    (data : BranchOrbitABCFromCenter h) {k : ZMod 19}
    (hrefOrbit :
      h.smul (DihedralGroup.sr k) data.b0 ∈
        h.rotationOrbitFinset data.c0) :
    ∃ k' : ZMod 19, h.smul (DihedralGroup.sr k') data.b0 = data.c0 := by
  rcases (h.mem_rotationOrbitFinset data.c0
      (h.smul (DihedralGroup.sr k) data.b0)).mp hrefOrbit with
    ⟨i, hi⟩
  refine ⟨k + i, ?_⟩
  have hrot :
      h.rotation (-i) (h.smul (DihedralGroup.sr k) data.b0) = data.c0 := by
    rw [← hi]
    exact h.rotation_neg_apply_rotation i data.c0
  calc
    h.smul (DihedralGroup.sr (k + i)) data.b0
        = h.smul (DihedralGroup.sr k) (h.rotation i data.b0) := by
          change h.smul (DihedralGroup.sr (k + i)) data.b0 =
            h.smul (DihedralGroup.sr k)
              (h.smul (DihedralGroup.r i) data.b0)
          rw [← h.mul_smul, DihedralGroup.sr_mul_r]
    _ = h.rotation (-i) (h.smul (DihedralGroup.sr k) data.b0) := by
          exact (h.rotation_neg_reflection_smul k i data.b0).symm
    _ = data.c0 := hrot

end BranchOrbitABCFromCenter

end

end Moore57
