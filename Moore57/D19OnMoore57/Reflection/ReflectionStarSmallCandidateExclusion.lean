import Moore57.D19OnMoore57.Reflection.ReflectionFixedCountStarCandidates
import Moore57.D19OnMoore57.Reflection.ReflectionFixedCenterDegreeBounds
import Moore57.D19OnMoore57.Reflection.ReflectionFixedStarFromActionBoundary

/-!
# Structural reduction of reflection fixed-star candidates

For a raw reflection whose fixed-induced graph is a star, the arithmetic
candidates are `6, 16, 26, 36, 46, 56`.  This file records the elementary
structural consequence that, for any of these candidates, `rotationFixedCenter`
cannot be the star center.  Therefore it is a leaf of the fixed-induced star,
so its per-reflection fixed-neighbor count is `1`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)
variable (k : ZMod 19)

/-- If a reflection fixed-induced graph is a star and its fixed count is at
least `6`, then `rotationFixedCenter` is not the star center. -/
theorem fixedInducedGraph_reflection_rotationFixedCenter_ne_star_center_of_fixedVertexCount_ge_six
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c)
    (hcount : 6 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k))) :
    reflectionRotationFixedCenterVertex h k ≠ c := by
  intro hcenter
  have hdegree_eq :
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
          (reflectionRotationFixedCenterVertex h k) =
        fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) - 1 := by
    have hcenter_degree :=
      IsStarWithCenter.degree_center_eq_card_sub_one
        (G := h.fixedInducedGraph (DihedralGroup.sr k)) (c := c) hstar
    rw [← hcenter] at hcenter_degree
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using hcenter_degree
  have hdegree_le :
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
          (reflectionRotationFixedCenterVertex h k) ≤ 3 :=
    h.fixedInducedGraph_reflection_rotationFixedCenter_degree_le_three k
  omega

/-- Under the same hypotheses, `rotationFixedCenter` is a leaf of the
fixed-induced star, hence has fixed-induced degree `1`. -/
theorem fixedInducedGraph_reflection_rotationFixedCenter_degree_eq_one_of_fixedVertexCount_ge_six
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c)
    (hcount : 6 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k))) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree
        (reflectionRotationFixedCenterVertex h k) = 1 := by
  exact
    IsStarWithCenter.degree_noncenter_eq_one
      (G := h.fixedInducedGraph (DihedralGroup.sr k)) (c := c) hstar
      (h.fixedInducedGraph_reflection_rotationFixedCenter_ne_star_center_of_fixedVertexCount_ge_six
        k hstar hcount)

/-- Candidate-classifier form of the non-center statement. -/
theorem fixedInducedGraph_reflection_rotationFixedCenter_ne_star_center_of_fixedInduced_isStarWithCenter
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c) :
    reflectionRotationFixedCenterVertex h k ≠ c := by
  have hcandidates :=
    h.fixedVertexCount_reflection_star_candidates_of_fixedInduced_isStarWithCenter
      k hstar
  have hcount : 6 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) := by
    rcases hcandidates with h6 | h16 | h26 | h36 | h46 | h56 <;> omega
  exact
    h.fixedInducedGraph_reflection_rotationFixedCenter_ne_star_center_of_fixedVertexCount_ge_six
      k hstar hcount

/-- Candidate-classifier form of the fixed-induced leaf-degree statement. -/
theorem fixedInducedGraph_reflection_rotationFixedCenter_degree_eq_one_of_fixedInduced_isStarWithCenter
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree
        (reflectionRotationFixedCenterVertex h k) = 1 := by
  exact
    IsStarWithCenter.degree_noncenter_eq_one
      (G := h.fixedInducedGraph (DihedralGroup.sr k)) (c := c) hstar
      (h.fixedInducedGraph_reflection_rotationFixedCenter_ne_star_center_of_fixedInduced_isStarWithCenter
        k hstar)

/-- Degree form converted to the per-reflection fixed-neighbor count at
`rotationFixedCenter`. -/
theorem reflectionFixedNeighborFinset_rotationFixedCenter_card_eq_one_of_fixedInduced_isStarWithCenter_fixedVertexCount_ge_six
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c)
    (hcount : 6 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k))) :
    (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card = 1 := by
  have hdegree :
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
          (reflectionRotationFixedCenterVertex h k) = 1 :=
    h.fixedInducedGraph_reflection_rotationFixedCenter_degree_eq_one_of_fixedVertexCount_ge_six
      k hstar hcount
  have hdegree_card :=
    h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
      (DihedralGroup.sr k) (reflectionRotationFixedCenterVertex h k)
  simpa [reflectionFixedNeighborFinset, reflectionRotationFixedCenterVertex,
    D19ActsOnMoore57.smulEquiv] using hdegree_card.symm.trans hdegree

/-- Inequality form of the fixed-neighbor bridge. -/
theorem reflectionFixedNeighborFinset_rotationFixedCenter_card_le_one_of_fixedInduced_isStarWithCenter_fixedVertexCount_ge_six
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c)
    (hcount : 6 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k))) :
    (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card ≤ 1 := by
  rw [
    h.reflectionFixedNeighborFinset_rotationFixedCenter_card_eq_one_of_fixedInduced_isStarWithCenter_fixedVertexCount_ge_six
      k hstar hcount]

/-- The reflection star-candidate classifier supplies the `≥ 6` hypothesis, so
any raw reflection fixed-induced star already has fixed-center neighbor count
at most `1`. -/
theorem reflectionFixedNeighborFinset_rotationFixedCenter_card_le_one_of_fixedInduced_isStarWithCenter
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c) :
    (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card ≤ 1 := by
  have hcandidates :=
    h.fixedVertexCount_reflection_star_candidates_of_fixedInduced_isStarWithCenter
      k hstar
  have hcount : 6 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) := by
    rcases hcandidates with h6 | h16 | h26 | h36 | h46 | h56 <;> omega
  exact
    h.reflectionFixedNeighborFinset_rotationFixedCenter_card_le_one_of_fixedInduced_isStarWithCenter_fixedVertexCount_ge_six
      k hstar hcount

/-- Equality-strengthened candidate bridge for downstream uses that need the
actual leaf degree/count rather than only the `≤ 1` bound. -/
theorem reflectionFixedNeighborFinset_rotationFixedCenter_card_eq_one_of_fixedInduced_isStarWithCenter
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c) :
    (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card = 1 := by
  have hcandidates :=
    h.fixedVertexCount_reflection_star_candidates_of_fixedInduced_isStarWithCenter
      k hstar
  have hcount : 6 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) := by
    rcases hcandidates with h6 | h16 | h26 | h36 | h46 | h56 <;> omega
  exact
    h.reflectionFixedNeighborFinset_rotationFixedCenter_card_eq_one_of_fixedInduced_isStarWithCenter_fixedVertexCount_ge_six
      k hstar hcount

/-- If every reflection fixed-induced graph is a star, the existing
fixed-center leaf boundary follows automatically. -/
def reflectionFixedCenterLeafBoundary_of_forall_fixedInduced_isStarWithCenter
    (hstar : ∀ k : ZMod 19,
      ∃ c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
        IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c) :
    ReflectionFixedCenterLeafBoundary h where
  degree_le_one := by
    intro k
    change
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
          (reflectionRotationFixedCenterVertex h k) ≤ 1
    rcases hstar k with ⟨c, hc⟩
    rw [
      h.fixedInducedGraph_reflection_rotationFixedCenter_degree_eq_one_of_fixedInduced_isStarWithCenter
        k hc]

end D19ActsOnMoore57

end

end Moore57
