import Moore57.D19OnMoore57.Involution.InvolutionFixedStarPaperBoundary
import Moore57.D19OnMoore57.Reflection.ReflectionFixedStarFromActionBoundary

/-!
# Reflection paper fixed-star boundary

This file converts the paper-shaped fixed-star statement for every reflection
into the induced-degree boundary used by the branch-geometry pipeline.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- In a paper-shaped fixed star, the fixed neighbors of the center are exactly
the fixed vertices other than the center. -/
theorem reflectionFixedNeighborFinset_eq_fixedFinset_erase_of_fixedSetStarWithCenter
    (k : ZMod 19) {c : V}
    (hc : FixedSetStarWithCenter Γ (h.smulEquiv (DihedralGroup.sr k)) c) :
    reflectionFixedNeighborFinset h k c =
      (fixedFinset (h.smulEquiv (DihedralGroup.sr k))).erase c := by
  ext v
  simp [reflectionFixedNeighborFinset, SimpleGraph.mem_neighborFinset,
    mem_fixedFinset]
  constructor
  · rintro ⟨hadj, hfix⟩
    refine ⟨?_, hfix⟩
    intro hvc
    subst hvc
    exact Γ.loopless.irrefl (a := v) hadj
  · rintro ⟨hvc, hfix⟩
    exact ⟨hc.center_adj_fixed v hfix hvc, hfix⟩

variable {h}

/-- The center in a paper-shaped reflection fixed star has induced fixed degree
`55`. -/
theorem fixedInducedGraph_center_degree_eq_55_of_fixedSetStarWithCenter
    (k : ZMod 19) {c : V}
    (hStar : InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)))
    (hc : FixedSetStarWithCenter Γ (h.smulEquiv (DihedralGroup.sr k)) c) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree
        (⟨c, hc.center_fixed⟩ : reflectionFixedVertex h k) = 55 := by
  classical
  have hdegree :=
    h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
      (DihedralGroup.sr k) (⟨c, hc.center_fixed⟩ : reflectionFixedVertex h k)
  have hneighbor_eq :=
    h.reflectionFixedNeighborFinset_eq_fixedFinset_erase_of_fixedSetStarWithCenter
      k hc
  rw [show
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
          (⟨c, hc.center_fixed⟩ : reflectionFixedVertex h k) =
        (reflectionFixedNeighborFinset h k c).card by
        simpa [reflectionFixedNeighborFinset] using hdegree,
    hneighbor_eq]
  rw [Finset.card_erase_of_mem]
  · rw [hStar.fixed_card]
  · simpa [mem_fixedFinset] using hc.center_fixed

/-- Every non-center fixed vertex in a paper-shaped reflection fixed star has
induced fixed degree at most `1`. -/
theorem fixedInducedGraph_noncenter_degree_le_one_of_fixedSetStarWithCenter
    (k : ZMod 19) {c : V}
    (hc : FixedSetStarWithCenter Γ (h.smulEquiv (DihedralGroup.sr k)) c)
    (x : reflectionFixedVertex h k)
    (hx : x ≠ (⟨c, hc.center_fixed⟩ : reflectionFixedVertex h k)) :
    (h.fixedInducedGraph (DihedralGroup.sr k)).degree x ≤ 1 := by
  classical
  have hdegree :=
    h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
      (DihedralGroup.sr k) x
  rw [show
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree x =
        (reflectionFixedNeighborFinset h k (x : V)).card by
        simpa [reflectionFixedNeighborFinset] using hdegree]
  have hx_ne : (x : V) ≠ c := by
    intro hxc
    exact hx (Subtype.ext hxc)
  have hsubset : reflectionFixedNeighborFinset h k (x : V) ⊆ ({c} : Finset V) := by
    intro y hy
    have hy_adj : Γ.Adj (x : V) y := by
      exact (SimpleGraph.mem_neighborFinset (G := Γ)
        (v := (x : V)) (w := y)).1 (Finset.mem_filter.mp hy).1
    have hy_fixed :
        (h.smulEquiv (DihedralGroup.sr k)) y = y :=
      (Finset.mem_filter.mp hy).2
    by_cases hyc : y = c
    · simp [hyc]
    · exact (hc.fixed_noncenter_not_adj (x : V) x.property hx_ne
        y hy_fixed hyc hy_adj).elim
  exact le_trans (Finset.card_le_card hsubset) (by simp)

/-- Paper-shaped fixed-star statements for every reflection, plus the assertion
that the rotation-fixed center is never the paper-star center, yield the
induced fixed-star degree boundary used downstream. -/
def reflectionFixedInducedStarDegrees_of_reflectionFixedSetStar56
    (hStar :
      ∀ k : ZMod 19,
        InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)))
    (hcenter_ne :
      ∀ k : ZMod 19, ∀ c : V,
        FixedSetStarWithCenter Γ (h.smulEquiv (DihedralGroup.sr k)) c →
          c ≠ h.rotationFixedCenter) :
    ReflectionFixedInducedStarDegrees h where
  exists_center_degree := by
    intro k
    rcases (hStar k).exists_center with ⟨c, hc⟩
    refine
      ⟨⟨c, hc.center_fixed⟩,
        h.fixedInducedGraph_center_degree_eq_55_of_fixedSetStarWithCenter
          k (hStar k) hc,
        ?_⟩
    intro x hx
    exact
      h.fixedInducedGraph_noncenter_degree_le_one_of_fixedSetStarWithCenter
        k hc x hx
  rotationFixedCenter_degree_le_one := by
    intro k
    rcases (hStar k).exists_center with ⟨c, hc⟩
    exact
      h.fixedInducedGraph_noncenter_degree_le_one_of_fixedSetStarWithCenter
        k hc (reflectionRotationFixedCenterVertex h k) (by
          intro hcenter
          exact hcenter_ne k c hc (Subtype.ext_iff.mp hcenter).symm)

/-- The same paper-shaped reflection fixed-star data recovers the older
`ReflectionFixedStarBoundary` wrapper. -/
def reflectionFixedStarBoundary_of_reflectionFixedSetStar56
    (hStar :
      ∀ k : ZMod 19,
        InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)))
    (hcenter_ne :
      ∀ k : ZMod 19, ∀ c : V,
        FixedSetStarWithCenter Γ (h.smulEquiv (DihedralGroup.sr k)) c →
          c ≠ h.rotationFixedCenter) :
    ReflectionFixedStarBoundary h :=
  (h.reflectionFixedInducedStarDegrees_of_reflectionFixedSetStar56
    hStar hcenter_ne).toReflectionFixedStarBoundary

end D19ActsOnMoore57

end

end Moore57
