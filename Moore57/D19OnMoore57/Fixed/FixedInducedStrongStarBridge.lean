import Moore57.Foundations.GraphTheory.StrongZeroOne
import Moore57.D19OnMoore57.Reflection.ReflectionInvolutionFixedSetStarFromActionBoundary

/-!
# Fixed induced strong graph to paper fixed star

This file applies the non-regular branch of the strong `(λ, μ) = (0, 1)`
classification to fixed induced graphs.  For a fixed set of size `56`, the
regular branch is already excluded by the strongly-regular parameter equation,
so the fixed induced graph is a star.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- A star center in the fixed induced graph gives the paper-level fixed-star
center in the ambient graph. -/
theorem fixedSetStarWithCenter_of_fixedInduced_isStarWithCenter
    (g : DihedralGroup 19)
    (c : fixedVertexSet (h.smulEquiv g))
    (hstar : IsStarWithCenter (h.fixedInducedGraph g) c) :
    FixedSetStarWithCenter Γ (h.smulEquiv g) (c : V) where
  center_fixed := c.property
  center_adj_fixed := by
    intro v hv hvc
    let x : fixedVertexSet (h.smulEquiv g) := ⟨v, hv⟩
    have hx_ne : x ≠ c := by
      intro hxc
      exact hvc (Subtype.ext_iff.mp hxc)
    have hadj : (h.fixedInducedGraph g).Adj c x :=
      (hstar c x).mpr (Or.inl ⟨rfl, hx_ne⟩)
    simpa [fixedInducedGraph] using hadj
  fixed_noncenter_not_adj := by
    intro v hv hvc w hw hwc hvw
    let x : fixedVertexSet (h.smulEquiv g) := ⟨v, hv⟩
    let y : fixedVertexSet (h.smulEquiv g) := ⟨w, hw⟩
    have hx_ne : x ≠ c := by
      intro hxc
      exact hvc (Subtype.ext_iff.mp hxc)
    have hy_ne : y ≠ c := by
      intro hyc
      exact hwc (Subtype.ext_iff.mp hyc)
    have hxy : (h.fixedInducedGraph g).Adj x y := by
      simpa [fixedInducedGraph] using hvw
    rcases (hstar x y).mp hxy with hcase | hcase
    · exact hx_ne hcase.1
    · exact hy_ne hcase.1

/-- If the fixed set of any group element has size `56`, then the fixed induced
graph is a star in the paper sense. -/
theorem exists_fixedSetStarWithCenter_of_fixedVertexCount_eq_56
    (g : DihedralGroup 19)
    (hfix : fixedVertexCount (h.smulEquiv g) = 56) :
    ∃ c : V, FixedSetStarWithCenter Γ (h.smulEquiv g) c := by
  have hstrong := h.fixedInducedGraph_isStrongZeroOne g
  have hnotRegular :=
    h.fixedInducedGraph_not_regular_of_fixedVertexCount_eq_56 g hfix
  rcases hstrong.exists_isStarWithCenter_of_not_regular hnotRegular with
    ⟨c, hc⟩
  exact
    ⟨(c : V),
      h.fixedSetStarWithCenter_of_fixedInduced_isStarWithCenter g c hc⟩

/-- Main geometry bridge for raw reflections: once the standard involution
fixed count `56` is available, the reflection fixed set is a paper-shaped
`56`-vertex star. -/
theorem involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56
    (k : ZMod 19)
    (hfix : fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  h.involutionFixedSetStar56_of_reflection_fixedVertexCount_and_fixedSetStarWithCenter
    k hfix
    (h.exists_fixedSetStarWithCenter_of_fixedVertexCount_eq_56
      (DihedralGroup.sr k) hfix)

end D19ActsOnMoore57

end

end Moore57
