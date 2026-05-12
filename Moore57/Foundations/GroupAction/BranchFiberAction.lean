import Moore57.Moore57Graph.Moore57Definition
import Moore57.D19OnMoore57.Action.D19Action

namespace Moore57
namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A group element acts injectively, so it preserves and reflects inequality. -/
theorem smul_ne_iff (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    {x y : V} : h.smul g x ≠ h.smul g y ↔ x ≠ y := by
  constructor
  · intro hne hxy
    exact hne (by rw [hxy])
  · intro hne heq
    exact hne ((h.smulEquiv g).injective heq)

/-- If a group element fixes the center `u`, it carries membership in a branch fiber
to membership in the corresponding moved branch fiber. -/
theorem smul_mem_branchFiber_iff
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    {u b x : V} (hu : h.smul g u = u) :
    h.smul g x ∈ branchFiber Γ u (h.smul g b) ↔
      x ∈ branchFiber Γ u b := by
  rw [mem_branchFiber, mem_branchFiber]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · exact (h.smul_ne_iff g).mp (by simpa [hu] using hx.1)
    · exact (h.smul_adj g b x).mpr hx.2
  · intro hx
    refine ⟨?_, ?_⟩
    · simpa [hu] using (h.smul_ne_iff g).mpr hx.1
    · exact (h.smul_adj g b x).mp hx.2

/-- A rotation acts injectively, so it preserves and reflects inequality. -/
theorem rotation_ne_iff (h : D19ActsOnMoore57 V Γ) (d : ZMod 19)
    {x y : V} : h.rotation d x ≠ h.rotation d y ↔ x ≠ y := by
  simp [rotation]

/-- Rotation version of `smul_mem_branchFiber_iff`. -/
theorem rotation_mem_branchFiber_iff
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19)
    {u b x : V} (hu : h.rotation d u = u) :
    h.rotation d x ∈ branchFiber Γ u (h.rotation d b) ↔
      x ∈ branchFiber Γ u b := by
  simpa [rotation] using
    h.smul_mem_branchFiber_iff (DihedralGroup.r d) (u := u) (b := b) (x := x) hu

end D19ActsOnMoore57
end Moore57
