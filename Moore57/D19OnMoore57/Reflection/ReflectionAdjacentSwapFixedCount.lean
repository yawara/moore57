import Moore57.D19OnMoore57.Fixed.FixedCommonNeighbors
import Moore57.D19OnMoore57.Reflection.ReflectionTraceCandidateLowerBoundBridge

/-!
# Fixed points from a reflection swapping an edge

Cameron, Chapter 3, Theorem 3.13, Step 2 uses the standard Moore-graph
labelling around an edge: if an involution interchanges adjacent vertices
`a` and `b`, then it fixes one common-neighbor vertex for each point in the
branch `N(a) \ {b}`.  The formal slice below records the injection needed by
our downstream trace-refined candidate list: it gives a lower bound `56`,
therefore in particular the already sufficient lower bound `47`.
-/

namespace Moore57

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

private theorem reflection_smul_reflection_smul_local
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) (x : V) :
    h.smul (DihedralGroup.sr k) (h.smul (DihedralGroup.sr k) x) = x := by
  calc
    h.smul (DihedralGroup.sr k) (h.smul (DihedralGroup.sr k) x)
        = h.smul (DihedralGroup.sr k * DihedralGroup.sr k) x := by
          rw [← h.mul_smul]
    _ = h.smul 1 x := by
          rw [DihedralGroup.sr_mul_self]
    _ = x := h.one_smul x

private theorem reflection_smul_mem_swapped_branch
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {a b u : V}
    (_hab : Γ.Adj a b)
    (ha : h.smul (DihedralGroup.sr k) a = b)
    (hb : h.smul (DihedralGroup.sr k) b = a)
    (hu : u ∈ branchFiber Γ b a) :
    h.smul (DihedralGroup.sr k) u ∈ branchFiber Γ a b := by
  rw [mem_branchFiber]
  have huAdj : Γ.Adj a u := (mem_branchFiber.mp hu).2
  refine ⟨?_, ?_⟩
  · intro hgu_eq_a
    have hgu_eq_gb : h.smul (DihedralGroup.sr k) u =
        h.smul (DihedralGroup.sr k) b := by
      rw [hb]
      exact hgu_eq_a
    exact (mem_branchFiber.mp hu).1
      ((h.smulEquiv (DihedralGroup.sr k)).injective hgu_eq_gb)
  · have hAdj := (h.smul_adj (DihedralGroup.sr k) a u).mp huAdj
    simpa [ha] using hAdj

private theorem not_adj_reflection_smul_of_mem_swapped_branch
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {a b u : V}
    (hab : Γ.Adj a b)
    (ha : h.smul (DihedralGroup.sr k) a = b)
    (hb : h.smul (DihedralGroup.sr k) b = a)
    (hu : u ∈ branchFiber Γ b a) :
    ¬ Γ.Adj u (h.smul (DihedralGroup.sr k) u) := by
  intro hu_gu
  have huAdj : Γ.Adj a u := (mem_branchFiber.mp hu).2
  have hguBranch :
      h.smul (DihedralGroup.sr k) u ∈ branchFiber Γ a b :=
    h.reflection_smul_mem_swapped_branch hab ha hb hu
  have hguAdj : Γ.Adj b (h.smul (DihedralGroup.sr k) u) :=
    (mem_branchFiber.mp hguBranch).2
  have hb_ne_a : b ≠ a := hab.symm.ne
  have hb_ne_u : b ≠ u := (mem_branchFiber.mp hu).1.symm
  have hb_ne_gu : b ≠ h.smul (DihedralGroup.sr k) u := by
    exact (mem_branchFiber.mp hguBranch).2.ne
  have ha_ne_u : a ≠ u := huAdj.ne
  have ha_ne_gu : a ≠ h.smul (DihedralGroup.sr k) u :=
    (mem_branchFiber.mp hguBranch).1.symm
  have hu_ne_gu : u ≠ h.smul (DihedralGroup.sr k) u := hu_gu.ne
  exact h.isMoore.no_four_cycle
    (x0 := b) (x1 := a) (x2 := u) (x3 := h.smul (DihedralGroup.sr k) u)
    hb_ne_a hb_ne_u hb_ne_gu ha_ne_u ha_ne_gu hu_ne_gu
    hab.symm huAdj hu_gu hguAdj.symm

private theorem reflection_smul_ne_self_of_mem_swapped_branch
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {a b u : V}
    (hab : Γ.Adj a b)
    (ha : h.smul (DihedralGroup.sr k) a = b)
    (_hb : h.smul (DihedralGroup.sr k) b = a)
    (hu : u ∈ branchFiber Γ b a) :
    u ≠ h.smul (DihedralGroup.sr k) u := by
  intro hu_fixed
  have huAdj : Γ.Adj a u := (mem_branchFiber.mp hu).2
  have hbu : Γ.Adj b u := by
    have hAdj := (h.smul_adj (DihedralGroup.sr k) a u).mp huAdj
    simpa [ha, hu_fixed.symm] using hAdj
  exact h.isMoore.no_triangle hab hbu huAdj.symm

private theorem not_adj_a_reflection_smul_of_mem_swapped_branch
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {a b u : V}
    (hab : Γ.Adj a b)
    (ha : h.smul (DihedralGroup.sr k) a = b)
    (hb : h.smul (DihedralGroup.sr k) b = a)
    (hu : u ∈ branchFiber Γ b a) :
    ¬ Γ.Adj a (h.smul (DihedralGroup.sr k) u) := by
  intro ha_gu
  have hguBranch :
      h.smul (DihedralGroup.sr k) u ∈ branchFiber Γ a b :=
    h.reflection_smul_mem_swapped_branch hab ha hb hu
  have hguAdj : Γ.Adj b (h.smul (DihedralGroup.sr k) u) :=
    (mem_branchFiber.mp hguBranch).2
  exact h.isMoore.no_triangle hab hguAdj ha_gu.symm

private theorem exists_reflection_fixed_commonNeighbor_of_mem_swapped_branch
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {a b u : V}
    (hab : Γ.Adj a b)
    (ha : h.smul (DihedralGroup.sr k) a = b)
    (hb : h.smul (DihedralGroup.sr k) b = a)
    (hu : u ∈ branchFiber Γ b a) :
    ∃ z : V,
      h.smul (DihedralGroup.sr k) z = z ∧
        Γ.Adj u z ∧ Γ.Adj (h.smul (DihedralGroup.sr k) u) z := by
  exact h.exists_fixed_commonNeighbor_of_swap_not_adj (DihedralGroup.sr k)
    (x := u) (y := h.smul (DihedralGroup.sr k) u)
    rfl
    (h.reflection_smul_reflection_smul_local k u)
    (h.reflection_smul_ne_self_of_mem_swapped_branch hab ha hb hu)
    (h.not_adj_reflection_smul_of_mem_swapped_branch hab ha hb hu)

private theorem eq_of_same_reflection_fixed_commonNeighbor_of_mem_swapped_branch
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {a b u v z : V}
    (hab : Γ.Adj a b)
    (ha : h.smul (DihedralGroup.sr k) a = b)
    (hb : h.smul (DihedralGroup.sr k) b = a)
    (hu : u ∈ branchFiber Γ b a)
    (hv : v ∈ branchFiber Γ b a)
    (hzu : Γ.Adj u z ∧ Γ.Adj (h.smul (DihedralGroup.sr k) u) z)
    (hzv : Γ.Adj v z ∧ Γ.Adj (h.smul (DihedralGroup.sr k) v) z) :
    u = v := by
  by_contra hne
  have huAdj : Γ.Adj a u := (mem_branchFiber.mp hu).2
  have hvAdj : Γ.Adj a v := (mem_branchFiber.mp hv).2
  have hz_ne_a : z ≠ a := by
    intro hza
    have ha_gu : Γ.Adj a (h.smul (DihedralGroup.sr k) u) := by
      simpa [hza] using hzu.2.symm
    exact h.not_adj_a_reflection_smul_of_mem_swapped_branch hab ha hb hu ha_gu
  exact h.isMoore.no_four_cycle
    (x0 := u) (x1 := z) (x2 := v) (x3 := a)
    hzu.1.ne hne (huAdj.ne).symm (hzv.1.ne).symm hz_ne_a (hvAdj.ne).symm
    hzu.1 hzv.1.symm hvAdj.symm huAdj

private noncomputable def fixedPointFromSwappedBranch
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {a b : V}
    (hab : Γ.Adj a b)
    (ha : h.smul (DihedralGroup.sr k) a = b)
    (hb : h.smul (DihedralGroup.sr k) b = a)
    (u : {x // x ∈ branchFiber Γ b a}) :
    fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)) :=
  let hz :=
    h.exists_reflection_fixed_commonNeighbor_of_mem_swapped_branch
      hab ha hb u.property
  ⟨Classical.choose hz, by
    change h.smul (DihedralGroup.sr k) (Classical.choose hz) =
      Classical.choose hz
    exact (Classical.choose_spec hz).1⟩

private theorem fixedPointFromSwappedBranch_injective
    (h : D19ActsOnMoore57 V Γ) {k : ZMod 19} {a b : V}
    (hab : Γ.Adj a b)
    (ha : h.smul (DihedralGroup.sr k) a = b)
    (hb : h.smul (DihedralGroup.sr k) b = a) :
    Function.Injective
      (h.fixedPointFromSwappedBranch (k := k) hab ha hb) := by
  intro u v huv
  have hspecu :=
    Classical.choose_spec
      (h.exists_reflection_fixed_commonNeighbor_of_mem_swapped_branch
        (k := k) hab ha hb u.property)
  have hspecv :=
    Classical.choose_spec
      (h.exists_reflection_fixed_commonNeighbor_of_mem_swapped_branch
        (k := k) hab ha hb v.property)
  have hz_eq :
      Classical.choose
          (h.exists_reflection_fixed_commonNeighbor_of_mem_swapped_branch
            (k := k) hab ha hb u.property) =
        Classical.choose
          (h.exists_reflection_fixed_commonNeighbor_of_mem_swapped_branch
            (k := k) hab ha hb v.property) :=
    congrArg Subtype.val huv
  apply Subtype.ext
  exact h.eq_of_same_reflection_fixed_commonNeighbor_of_mem_swapped_branch
    (k := k) hab ha hb u.property v.property hspecu.2
    (by simpa [hz_eq] using hspecv.2)

/-- If a reflection interchanges the adjacent vertices `a` and `b`, then it has
at least the `56` fixed points supplied by the branch `N(a) \ {b}`. -/
theorem fixedVertexCount_reflection_ge_fiftySix_of_adjacent_swap
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) {a b : V}
    (hab : Γ.Adj a b)
    (ha : h.smul (DihedralGroup.sr k) a = b)
    (hb : h.smul (DihedralGroup.sr k) b = a) :
    56 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) := by
  classical
  have hcard :
      Fintype.card {x // x ∈ branchFiber Γ b a} = 56 := by
    rw [Fintype.card_coe]
    exact h.isMoore.branchFiber_card hab.symm
  have hle :
      Fintype.card {x // x ∈ branchFiber Γ b a} ≤
        Fintype.card (fixedVertexSet (h.smulEquiv (DihedralGroup.sr k))) :=
    Fintype.card_le_of_injective
      (h.fixedPointFromSwappedBranch (k := k) hab ha hb)
      (h.fixedPointFromSwappedBranch_injective (k := k) hab ha hb)
  rw [hcard] at hle
  rwa [fixedVertexCount_eq_card_fixedVertexSet]

/-- The trace-refined candidate list upgrades the adjacent-swap lower bound to
the exact Cameron/Higman fixed-point count `56`. -/
theorem fixedVertexCount_reflection_eq_56_of_adjacent_swap
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) {a b : V}
    (hab : Γ.Adj a b)
    (ha : h.smul (DihedralGroup.sr k) a = b)
    (hb : h.smul (DihedralGroup.sr k) b = a) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
  h.fixedVertexCount_reflection_eq_56_of_ge_fortySeven k
    (by
      have h56 :=
        h.fixedVertexCount_reflection_ge_fiftySix_of_adjacent_swap k hab ha hb
      omega)

/-- Positive adjacent-moved count for a reflection is exactly the existence of
an adjacent edge interchanged by that reflection, in the direction needed by
the adjacent-swap fixed-count theorem. -/
theorem exists_adjacent_swap_of_reflection_adjacentMovedCount_pos
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19)
    (hpos : 0 < adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k))) :
    ∃ a b : V,
      Γ.Adj a b ∧
        h.smul (DihedralGroup.sr k) a = b ∧
        h.smul (DihedralGroup.sr k) b = a := by
  classical
  rw [adjacentMovedCount] at hpos
  rcases Finset.card_pos.mp hpos with ⟨a, ha⟩
  rw [Finset.mem_filter] at ha
  refine ⟨a, h.smul (DihedralGroup.sr k) a, ha.2, rfl, ?_⟩
  exact h.reflection_smul_reflection_smul_local k a

/-- If a reflection has any adjacent-moved vertex, then the adjacent-swap branch
gives at least `56` fixed points. -/
theorem fixedVertexCount_reflection_ge_fiftySix_of_adjacentMovedCount_pos
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19)
    (hpos : 0 < adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k))) :
    56 ≤ fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) := by
  rcases h.exists_adjacent_swap_of_reflection_adjacentMovedCount_pos k hpos with
    ⟨a, b, hab, ha, hb⟩
  exact h.fixedVertexCount_reflection_ge_fiftySix_of_adjacent_swap k hab ha hb

/-- The trace-refined candidate list upgrades positive adjacent-moved count to
the exact Cameron/Higman reflection fixed-point count. -/
theorem fixedVertexCount_reflection_eq_56_of_adjacentMovedCount_pos
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19)
    (hpos : 0 < adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k))) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
  h.fixedVertexCount_reflection_eq_56_of_ge_fortySeven k
    (by
      have h56 :=
        h.fixedVertexCount_reflection_ge_fiftySix_of_adjacentMovedCount_pos
          k hpos
      omega)

end D19ActsOnMoore57

end

end Moore57
