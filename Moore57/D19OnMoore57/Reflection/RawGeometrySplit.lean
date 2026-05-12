import Moore57.D19OnMoore57.Reflection.RemainingCandidateGeometryBoundary

/-!
# Raw reflection geometry split

This file removes the artificial `non-56` hypothesis from the current
reflection geometry split.  A reflection with fixed count `56` is already a
fixed star, so the rotation-fixed center is a leaf of the fixed induced graph.
The remaining trace-refined candidates are handled by
`reflection_remaining_non56_candidate_geometry`.

Thus every raw reflection either contributes the fixed-center leaf boundary or
falls into the regular-`10` all-center-neighbor-orbits-preserved boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Exact reflection fixed count `56` still puts `rotationFixedCenter` in the
leaf position of the fixed-induced star. -/
theorem reflectionFixedCenterLeafAt_of_fixedVertexCount_eq_56
    (k : ZMod 19)
    (hcount : fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    ReflectionFixedCenterLeafAt h k := by
  have hstrong := h.fixedInducedGraph_isStrongZeroOne (DihedralGroup.sr k)
  have hnotRegular :=
    h.fixedInducedGraph_not_regular_of_fixedVertexCount_eq_56
      (DihedralGroup.sr k) hcount
  rcases hstrong.exists_isStarWithCenter_of_not_regular hnotRegular with
    ⟨c, hstar⟩
  refine ⟨?_⟩
  rw [
    h.fixedInducedGraph_reflection_rotationFixedCenter_degree_eq_one_of_fixedInduced_isStarWithCenter
      k hstar]

/-- Per-reflection raw split after trace integrality: every reflection either
has the local fixed-center leaf geometry or is in the regular-`10`
all-preserved boundary. -/
theorem reflectionFixedCenterLeafAt_or_regularTenAllCenterNeighborOrbitsPreserved
    (k : ZMod 19) :
    ReflectionFixedCenterLeafAt h k ∨
      ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k := by
  rcases h.fixedVertexCount_reflection_trace_refined_raw_candidates k with
      h6 | h10 | h16 | h26 | h36 | h46 | h56
  · exact h.reflection_remaining_non56_candidate_geometry k
      (Or.inl h6)
  · exact h.reflection_remaining_non56_candidate_geometry k
      (Or.inr (Or.inl h10))
  · exact h.reflection_remaining_non56_candidate_geometry k
      (Or.inr (Or.inr (Or.inl h16)))
  · exact h.reflection_remaining_non56_candidate_geometry k
      (Or.inr (Or.inr (Or.inr (Or.inl h26))))
  · exact h.reflection_remaining_non56_candidate_geometry k
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h36)))))
  · exact h.reflection_remaining_non56_candidate_geometry k
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h46)))))
  · exact Or.inl (h.reflectionFixedCenterLeafAt_of_fixedVertexCount_eq_56 k h56)

/-- Global raw split: unless some reflection is in the regular-`10`
all-preserved boundary, all reflections satisfy the fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary_or_exists_regularTenAllCenterNeighborOrbitsPreserved
    (h : D19ActsOnMoore57 V Γ) :
    ReflectionFixedCenterLeafBoundary h ∨
      ∃ k : ZMod 19,
        ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k := by
  classical
  by_cases hregular :
      ∃ k : ZMod 19,
        ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k
  · exact Or.inr hregular
  · refine Or.inl ?_
    exact
      { degree_le_one := by
          intro k
          rcases h.reflectionFixedCenterLeafAt_or_regularTenAllCenterNeighborOrbitsPreserved
              k with hleaf | hregularAt
          · exact hleaf.degree_le_one
          · exact False.elim (hregular ⟨k, hregularAt⟩) }

/-- Contrapositive convenience form of the global split. -/
theorem exists_regularTenAllCenterNeighborOrbitsPreserved_of_not_reflectionFixedCenterLeafBoundary
    (h : D19ActsOnMoore57 V Γ)
    (hnoLeaf : ¬ ReflectionFixedCenterLeafBoundary h) :
    ∃ k : ZMod 19,
      ReflectionRegularTenAllCenterNeighborOrbitsPreserved h k := by
  rcases h.reflectionFixedCenterLeafBoundary_or_exists_regularTenAllCenterNeighborOrbitsPreserved with
    hleaf | hregular
  · exact False.elim (hnoLeaf hleaf)
  · exact hregular

end D19ActsOnMoore57

end

end Moore57
