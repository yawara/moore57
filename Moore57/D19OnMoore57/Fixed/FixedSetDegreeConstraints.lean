import Moore57.D19OnMoore57.Fixed.FixedNeighborCounts
import Moore57.D19OnMoore57.Fixed.FixedCommonNeighbors

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- If a rotation fixes `v` and at least one other vertex, then `v` has a fixed
neighbor for that rotation. -/
theorem fixedNeighborFinset_card_pos_of_exists_other_fixed
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {v : V}
    (hv : h.rotation d v = v)
    (hother : ∃ w, h.rotation d w = w ∧ w ≠ v) :
    (h.fixedNeighborFinset d v).card > 0 := by
  classical
  rcases hother with ⟨w, hwfix, hwne⟩
  by_cases hvw_adj : Γ.Adj v w
  · exact Finset.card_pos.mpr
      ⟨w, (mem_fixedNeighborFinset h d v w).2 ⟨hvw_adj, hwfix⟩⟩
  · have hv_smul : h.smul (DihedralGroup.r d) v = v := by
      simpa [rotation] using hv
    have hw_smul : h.smul (DihedralGroup.r d) w = w := by
      simpa [rotation] using hwfix
    have hvw_ne : v ≠ w := fun hvw => hwne hvw.symm
    rcases h.exists_fixed_commonNeighbor_of_not_adj (DihedralGroup.r d)
        hv_smul hw_smul hvw_ne hvw_adj with
      ⟨z, hzfix, hzadj_v, _hzadj_w⟩
    exact Finset.card_pos.mpr
      ⟨z, (mem_fixedNeighborFinset h d v z).2
        ⟨hzadj_v, by simpa [rotation] using hzfix⟩⟩

/-- A nonempty fixed-neighbor set for a rotation on a Moore graph has at least
`19` vertices, because its cardinality is divisible by `19`. -/
theorem fixedNeighborFinset_card_ge_nineteen_of_exists_other_fixed
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {v : V}
    (hv : h.rotation d v = v)
    (hother : ∃ w, h.rotation d w = w ∧ w ≠ v) :
    (h.fixedNeighborFinset d v).card ≥ 19 := by
  classical
  let n := (h.fixedNeighborFinset d v).card
  have hpos : 0 < n := by
    simpa [n] using h.fixedNeighborFinset_card_pos_of_exists_other_fixed d hv hother
  have hmod : n ≡ 0 [MOD 19] := by
    simpa [n] using h.card_fixedNeighborFinset_rotation_modEq_zero_of_moore d hv
  by_cases hge : 19 ≤ n
  · simpa [n] using hge
  · have hlt : n < 19 := Nat.lt_of_not_ge hge
    have hzero : n = 0 := by
      have hmod_zero : n % 19 = 0 := by
        simpa [Nat.ModEq] using hmod
      simpa [Nat.mod_eq_of_lt hlt] using hmod_zero
    omega

end D19ActsOnMoore57

end Moore57
