import Moore57.D19OnMoore57.Reflection.FixedSetStarHigmanArithmeticBridge
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Fixed-induced star edge formula

This file isolates the elementary graph-counting step used by the reflection
fixed-star pipeline: a finite star has exactly `n - 1` edges.  It then applies
that count to fixed-induced reflection graphs and supplies a connector to the
existing `D19LinearCharacterInput` arithmetic bridge.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace IsStarWithCenter

variable {G : SimpleGraph V} [DecidableRel G.Adj] {c : V}

theorem neighborFinset_center_eq_univ_erase
    (hstar : IsStarWithCenter G c) :
    G.neighborFinset c = (Finset.univ : Finset V).erase c := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase,
    Finset.mem_univ, and_true]
  constructor
  · intro hcv
    exact fun hvc => by
      rw [hvc] at hcv
      exact G.loopless.irrefl c hcv
  · intro hv
    exact (hstar c v).mpr (Or.inl ⟨rfl, hv⟩)

theorem degree_center_eq_card_sub_one
    (hstar : IsStarWithCenter G c) :
    G.degree c = Fintype.card V - 1 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    hstar.neighborFinset_center_eq_univ_erase]
  rw [Finset.card_erase_of_mem (Finset.mem_univ c)]
  simp

omit [DecidableEq V] in
theorem neighborFinset_noncenter_eq_singleton
    (hstar : IsStarWithCenter G c) {v : V} (hv : v ≠ c) :
    G.neighborFinset v = ({c} : Finset V) := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  constructor
  · intro hvw
    rcases (hstar v w).mp hvw with hcase | hcase
    · exact (hv hcase.1).elim
    · exact hcase.1
  · intro hw
    subst w
    exact (hstar v c).mpr (Or.inr ⟨rfl, hv⟩)

omit [DecidableEq V] in
theorem degree_noncenter_eq_one
    (hstar : IsStarWithCenter G c) {v : V} (hv : v ≠ c) :
    G.degree v = 1 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    hstar.neighborFinset_noncenter_eq_singleton hv]
  simp

/-- A finite star on `n` vertices has exactly `n - 1` edges. -/
theorem card_edgeFinset_eq_card_sub_one
    (hstar : IsStarWithCenter G c) :
    G.edgeFinset.card = Fintype.card V - 1 := by
  classical
  have hcenter_not_mem : c ∉ (Finset.univ : Finset V).erase c := by
    simp
  have hsum_split :
      (∑ v : V, G.degree v) =
        G.degree c +
          Finset.sum ((Finset.univ : Finset V).erase c) (fun v => G.degree v) := by
    calc
      (∑ v : V, G.degree v)
          = Finset.sum (Finset.univ : Finset V) (fun v => G.degree v) := by
              simp
      _ = Finset.sum (insert c ((Finset.univ : Finset V).erase c))
            (fun v => G.degree v) := by
              congr
              ext v
              simp
      _ = G.degree c +
            Finset.sum ((Finset.univ : Finset V).erase c) (fun v => G.degree v) := by
              rw [Finset.sum_insert hcenter_not_mem]
  have hsum_noncenter :
      Finset.sum ((Finset.univ : Finset V).erase c) (fun v => G.degree v) =
        ((Finset.univ : Finset V).erase c).card := by
    calc
      Finset.sum ((Finset.univ : Finset V).erase c) (fun v => G.degree v)
          = Finset.sum ((Finset.univ : Finset V).erase c) (fun _ : V => 1) := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              have hvc : v ≠ c := (Finset.mem_erase.mp hv).1
              rw [hstar.degree_noncenter_eq_one hvc]
      _ = ((Finset.univ : Finset V).erase c).card := by
              simp
  have herase_card :
      ((Finset.univ : Finset V).erase c).card = Fintype.card V - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c)]
    simp
  have hsum_star :
      (∑ v : V, G.degree v) = 2 * (Fintype.card V - 1) := by
    rw [hsum_split, hsum_noncenter, hstar.degree_center_eq_card_sub_one,
      herase_card]
    omega
  have htwice :
      2 * G.edgeFinset.card = 2 * (Fintype.card V - 1) := by
    rw [← G.sum_degrees_eq_twice_card_edges, hsum_star]
  omega

end IsStarWithCenter

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- A paper fixed-star center gives the corresponding fixed-induced star. -/
theorem fixedInducedGraph_isStarWithCenter_of_fixedSetStarWithCenter
    (g : DihedralGroup 19) {c : V}
    (hc : FixedSetStarWithCenter Γ (h.smulEquiv g) c) :
    IsStarWithCenter (h.fixedInducedGraph g)
      (⟨c, hc.center_fixed⟩ : fixedVertexSet (h.smulEquiv g)) := by
  intro x y
  constructor
  · intro hxy
    by_cases hxc : (x : V) = c
    · left
      refine ⟨Subtype.ext hxc, ?_⟩
      intro hyc
      have hy_val : (y : V) = c := Subtype.ext_iff.mp hyc
      have hxy_eq : x = y := Subtype.ext (hxc.trans hy_val.symm)
      rw [hxy_eq] at hxy
      exact (h.fixedInducedGraph g).loopless.irrefl y hxy
    · by_cases hyc : (y : V) = c
      · right
        exact ⟨Subtype.ext hyc, fun hxc' => hxc (Subtype.ext_iff.mp hxc')⟩
      · have hnot :=
          hc.fixed_noncenter_not_adj (x : V) x.property hxc
            (y : V) y.property hyc
        exact False.elim (hnot hxy)
  · rintro (⟨hxc, hy_ne⟩ | ⟨hyc, hx_ne⟩)
    · subst hxc
      have hy_ne_val : (y : V) ≠ c := by
        intro hyc
        exact hy_ne (Subtype.ext hyc)
      simpa [fixedInducedGraph] using
        hc.center_adj_fixed (y : V) y.property hy_ne_val
    · subst hyc
      have hx_ne_val : (x : V) ≠ c := by
        intro hxc
        exact hx_ne (Subtype.ext hxc)
      exact (by
        simpa [fixedInducedGraph] using
          (hc.center_adj_fixed (x : V) x.property hx_ne_val).symm)

/-- Fixed-induced star edge count in the `fixedVertexCount` normalization. -/
theorem fixedInducedGraph_card_edgeFinset_eq_fixedVertexCount_sub_one_of_isStarWithCenter
    (g : DihedralGroup 19)
    {c : fixedVertexSet (h.smulEquiv g)}
    (hstar : IsStarWithCenter (h.fixedInducedGraph g) c) :
    (h.fixedInducedGraph g).edgeFinset.card =
      fixedVertexCount (h.smulEquiv g) - 1 := by
  have hcard :=
    IsStarWithCenter.card_edgeFinset_eq_card_sub_one (G := h.fixedInducedGraph g)
      (c := c) hstar
  simpa [fixedVertexCount_eq_card_fixedVertexSet] using hcard

/-- Paper fixed-star form of the fixed-induced star edge count. -/
theorem fixedInducedGraph_card_edgeFinset_eq_fixedVertexCount_sub_one_of_fixedSetStarWithCenter
    (g : DihedralGroup 19) {c : V}
    (hc : FixedSetStarWithCenter Γ (h.smulEquiv g) c) :
    (h.fixedInducedGraph g).edgeFinset.card =
      fixedVertexCount (h.smulEquiv g) - 1 :=
  h.fixedInducedGraph_card_edgeFinset_eq_fixedVertexCount_sub_one_of_isStarWithCenter
    g (h.fixedInducedGraph_isStarWithCenter_of_fixedSetStarWithCenter g hc)

/-- Reflection-specialized integer form of the star edge count. -/
theorem fixedInducedGraph_reflection_card_edgeFinset_int_eq_fixedVertexCount_sub_one
    (k : ZMod 19) {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c) :
    ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ) =
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 1 := by
  have hnat :=
    h.fixedInducedGraph_card_edgeFinset_eq_fixedVertexCount_sub_one_of_isStarWithCenter
      (DihedralGroup.sr k) hstar
  have hpos :
      0 < fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) := by
    rw [fixedVertexCount_eq_card_fixedVertexSet]
    exact Fintype.card_pos_iff.mpr ⟨c⟩
  calc
    ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ)
        = ((fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) - 1 : ℕ) : ℤ) := by
          exact_mod_cast hnat
    _ = (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 1 := by
          rw [Nat.cast_sub (Nat.succ_le_of_lt hpos)]
          norm_num

/-- Replace a fixed-induced edge-count formula by the star-edge formula expected
by the existing Higman arithmetic bridge. -/
theorem reflection_starEdgeCountFormula_of_fixedInduced_isStarWithCenter
    (k : ZMod 19)
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c)
    (hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ)) :
    (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
      3250 -
        58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
          2 * ((fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) - 1) := by
  rw [hformula]
  rw [h.fixedInducedGraph_reflection_card_edgeFinset_int_eq_fixedVertexCount_sub_one
    k hstar]

namespace D19LinearCharacterInput

/-- Packaged reflection connector using an actual fixed-induced star plus the
raw formula with the fixed-induced edge count. -/
theorem involutionFixedSetStar56_of_fixedInduced_starEdgeCountFormula_bounds
    (hin : D19LinearCharacterInput h) (k : ZMod 19)
    {c : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))}
    (hstar : IsStarWithCenter (h.fixedInducedGraph (DihedralGroup.sr k)) c)
    (hformula :
      (adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) : ℤ) =
        3250 -
          58 * (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) +
            2 * ((h.fixedInducedGraph (DihedralGroup.sr k)).edgeFinset.card : ℤ))
    (hfixed_lower :
      52 ≤ (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ))
    (hfixed_upper :
      (fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) : ℤ) ≤ 56) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  hin.involutionFixedSetStar56_of_starEdgeCountFormula_bounds k
    (h.reflection_starEdgeCountFormula_of_fixedInduced_isStarWithCenter
      k hstar hformula)
    hfixed_lower hfixed_upper

end D19LinearCharacterInput

end D19ActsOnMoore57

end

end Moore57
