import Moore57.D19OnMoore57.Fixed.FixedNeighborCounts
import Moore57.D19OnMoore57.Fixed.FixedCommonNeighbors

namespace Moore57

theorem exists_other_fixed_of_fixedVertexCount_ne_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {σ : Equiv.Perm V} {v : V}
    (hv : σ v = v) (hcount : fixedVertexCount σ ≠ 1) :
    ∃ w, w ≠ v ∧ σ w = w := by
  classical
  let S := fixedVertexSet σ
  have hcard_ne : Fintype.card S ≠ 1 := by
    intro hcard
    apply hcount
    simpa [S, fixedVertexCount_eq_card_fixedVertexSet] using hcard
  have hpos : 0 < Fintype.card S := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨v, hv⟩⟩
  have hone : 1 < Fintype.card S := by omega
  rcases Fintype.one_lt_card_iff.mp hone with ⟨x, y, hxy⟩
  by_cases hxv : (x : V) = v
  · refine ⟨y, ?_, y.property⟩
    intro hyv
    exact hxy (Subtype.ext (hxv.trans hyv.symm))
  · exact ⟨x, hxv, x.property⟩

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

theorem exists_mem_fixedNeighborFinset_of_exists_other_fixed
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {v : V}
    (hv : h.rotation d v = v)
    (hother : ∃ w, w ≠ v ∧ h.rotation d w = w) :
    ∃ z, z ∈ h.fixedNeighborFinset d v := by
  classical
  rcases hother with ⟨w, hw_ne_v, hw⟩
  by_cases hvw_adj : Γ.Adj v w
  · exact ⟨w, by simp [mem_fixedNeighborFinset, hvw_adj, hw]⟩
  · have hv_ne_w : v ≠ w := fun hvw => hw_ne_v hvw.symm
    have hv_smul : h.smul (DihedralGroup.r d) v = v := by
      simpa [rotation] using hv
    have hw_smul : h.smul (DihedralGroup.r d) w = w := by
      simpa [rotation] using hw
    rcases h.exists_fixed_commonNeighbor_of_not_adj
        (DihedralGroup.r d) hv_smul hw_smul hv_ne_w hvw_adj with
      ⟨z, hz_fixed, hz_adj_v, _hz_adj_w⟩
    have hz_rotation : h.rotation d z = z := by
      simpa [rotation] using hz_fixed
    exact ⟨z, by simp [mem_fixedNeighborFinset, hz_adj_v, hz_rotation]⟩

theorem card_fixedNeighborFinset_pos_of_exists_other_fixed
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {v : V}
    (hv : h.rotation d v = v)
    (hother : ∃ w, w ≠ v ∧ h.rotation d w = w) :
    0 < (h.fixedNeighborFinset d v).card := by
  rcases h.exists_mem_fixedNeighborFinset_of_exists_other_fixed d hv hother with ⟨z, hz⟩
  exact Finset.card_pos.mpr ⟨z, hz⟩

theorem card_fixedNeighborFinset_ge_nineteen_of_exists_other_fixed
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {v : V}
    (hv : h.rotation d v = v)
    (hother : ∃ w, w ≠ v ∧ h.rotation d w = w) :
    19 ≤ (h.fixedNeighborFinset d v).card := by
  have hpos := h.card_fixedNeighborFinset_pos_of_exists_other_fixed d hv hother
  have hmod := h.card_fixedNeighborFinset_rotation_modEq_zero_of_moore d hv
  exact Nat.le_of_dvd hpos (Nat.modEq_zero_iff_dvd.mp hmod)

theorem card_fixedNeighborFinset_ge_nineteen_of_fixedVertexCount_ne_one
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {v : V}
    (hv : h.rotation d v = v)
    (hcount : fixedVertexCount (h.rotation d) ≠ 1) :
    19 ≤ (h.fixedNeighborFinset d v).card := by
  rcases exists_other_fixed_of_fixedVertexCount_ne_one hv hcount with ⟨w, hw_ne_v, hw⟩
  exact h.card_fixedNeighborFinset_ge_nineteen_of_exists_other_fixed d hv
    ⟨w, hw_ne_v, hw⟩

theorem fixedVertexCount_rotation_ge_fixedNeighborFinset_card_add_one
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {v : V}
    (hv : h.rotation d v = v) :
    (h.fixedNeighborFinset d v).card + 1 ≤ fixedVertexCount (h.rotation d) := by
  classical
  let S := fixedVertexSet (h.rotation d)
  let N := h.fixedNeighborFinset d v
  have hv_not_mem : v ∉ N := by
    intro hv_mem
    have hvv : Γ.Adj v v := (mem_fixedNeighborFinset h d v v).mp hv_mem |>.1
    exact SimpleGraph.irrefl Γ hvv
  have hsubset : insert v N ⊆ S.toFinset := by
    intro x hx
    rw [Set.mem_toFinset]
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hxN
    · exact hv
    · exact (mem_fixedNeighborFinset h d v x).mp hxN |>.2
  have hle : (insert v N).card ≤ S.toFinset.card :=
    Finset.card_le_card hsubset
  have hcard_insert : (insert v N).card = N.card + 1 := by
    simp [hv_not_mem]
  rw [hcard_insert] at hle
  rw [fixedVertexCount_eq_card_fixedVertexSet, ← Set.toFinset_card]
  exact hle

theorem fixedVertexCount_rotation_ge_twenty_of_one_lt
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19)
    (hcount : 1 < fixedVertexCount (h.rotation d)) :
    20 ≤ fixedVertexCount (h.rotation d) := by
  classical
  have hcard : 1 < Fintype.card (fixedVertexSet (h.rotation d)) := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using hcount
  rcases Fintype.one_lt_card_iff.mp hcard with ⟨v, _w, _hvw⟩
  have hcount_ne : fixedVertexCount (h.rotation d) ≠ 1 := by omega
  have hneighbor :
      19 ≤ (h.fixedNeighborFinset d (v : V)).card :=
    h.card_fixedNeighborFinset_ge_nineteen_of_fixedVertexCount_ne_one d v.property hcount_ne
  have hcount_lower :
      (h.fixedNeighborFinset d (v : V)).card + 1 ≤ fixedVertexCount (h.rotation d) :=
    h.fixedVertexCount_rotation_ge_fixedNeighborFinset_card_add_one d v.property
  omega

end D19ActsOnMoore57

end Moore57
