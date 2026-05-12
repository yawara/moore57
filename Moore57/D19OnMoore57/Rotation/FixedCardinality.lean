import Mathlib.Algebra.Field.ZMod
import Moore57.D19OnMoore57.Action.D19Action
import Moore57.D19OnMoore57.Fixed.CommonNeighbors
import Moore57.D19OnMoore57.Fixed.InducedDegree
import Moore57.D19OnMoore57.Fixed.NeighborCounts
import Moore57.Foundations.GroupAction.FixedPointBasics
import Moore57.Moore57Graph.Aut.FixedCount
import Moore57.Moore57Graph.Moore57Definition

namespace Moore57

theorem fixedVertexSet_pow_of_mem {V : Type*} {σ : Equiv.Perm V} {v : V}
    (hv : v ∈ fixedVertexSet σ) (n : ℕ) :
    v ∈ fixedVertexSet (σ ^ n) := by
  induction n with
  | zero =>
      simp [fixedVertexSet]
  | succ n ih =>
      rw [mem_fixedVertexSet] at hv ih ⊢
      rw [pow_succ]
      simp [Equiv.Perm.mul_apply, hv, ih]

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Natural scalar multiplication in the additive rotation parameter corresponds
to taking powers of the induced permutation. -/
theorem rotation_nsmul (h : D19ActsOnMoore57 V Γ) (n : ℕ) (d : ZMod 19) :
    h.rotation (n • d) = h.rotation d ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [succ_nsmul, h.rotation_add, ih, pow_succ]

/-- In `ZMod 19`, every element is a natural multiple of any nonzero element. -/
theorem exists_nsmul_eq_of_ne_zero {d e : ZMod 19} (hd : d ≠ 0) :
    ∃ n : ℕ, n • d = e := by
  letI : Fact (Nat.Prime 19) := ⟨by decide⟩
  refine ⟨(e * d⁻¹).val, ?_⟩
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  calc
    (e * d⁻¹) * d = e * (d⁻¹ * d) := by rw [mul_assoc]
    _ = e * 1 := by rw [inv_mul_cancel₀ hd]
    _ = e := by rw [mul_one]

/-- If two rotation parameters are natural multiples of each other, their fixed
vertex sets coincide. -/
theorem fixedVertexSet_rotation_eq_of_mutual_nsmul
    (h : D19ActsOnMoore57 V Γ) {d e : ZMod 19}
    (hde : ∃ n : ℕ, n • d = e) (hed : ∃ m : ℕ, m • e = d) :
    fixedVertexSet (h.rotation d) = fixedVertexSet (h.rotation e) := by
  rcases hde with ⟨n, hn⟩
  rcases hed with ⟨m, hm⟩
  ext v
  constructor
  · intro hv
    have hpow : v ∈ fixedVertexSet (h.rotation d ^ n) :=
      fixedVertexSet_pow_of_mem hv n
    have hrot : h.rotation e = h.rotation d ^ n := by
      rw [← hn, h.rotation_nsmul]
    simpa [hrot] using hpow
  · intro hv
    have hpow : v ∈ fixedVertexSet (h.rotation e ^ m) :=
      fixedVertexSet_pow_of_mem hv m
    have hrot : h.rotation d = h.rotation e ^ m := by
      rw [← hm, h.rotation_nsmul]
    simpa [hrot] using hpow

/-- All nontrivial rotations of the order-19 rotation subgroup have the same
fixed vertex set. -/
theorem fixedVertexSet_rotation_eq_of_nonzero
    (h : D19ActsOnMoore57 V Γ) {d e : ZMod 19} (hd : d ≠ 0) (he : e ≠ 0) :
    fixedVertexSet (h.rotation d) = fixedVertexSet (h.rotation e) :=
  h.fixedVertexSet_rotation_eq_of_mutual_nsmul
    (exists_nsmul_eq_of_ne_zero hd)
    (exists_nsmul_eq_of_ne_zero he)

end D19ActsOnMoore57

end Moore57

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- If two rotation orbit positions agree, the corresponding difference fixes
the original point. -/
theorem rotation_sub_fixed_of_rotation_eq
    (h : D19ActsOnMoore57 V Γ) {i j : ZMod 19} {x : V}
    (hij : h.rotation i x = h.rotation j x) :
    h.rotation (i - j) x = x := by
  have hfix_at_j : h.rotation (i - j) (h.rotation j x) = h.rotation j x := by
    calc
      h.rotation (i - j) (h.rotation j x)
          = (h.rotation (i - j) * h.rotation j) x := by
              simp [Equiv.Perm.mul_apply]
      _ = h.rotation ((i - j) + j) x := by
              rw [← h.rotation_add]
      _ = h.rotation i x := by
              rw [sub_add_cancel]
      _ = h.rotation j x := hij
  have hcomm_at_x :
      h.rotation j (h.rotation (i - j) x) =
        h.rotation (i - j) (h.rotation j x) := by
    calc
      h.rotation j (h.rotation (i - j) x)
          = (h.rotation j * h.rotation (i - j)) x := by
              simp [Equiv.Perm.mul_apply]
      _ = h.rotation (j + (i - j)) x := by
              rw [← h.rotation_add]
      _ = h.rotation ((i - j) + j) x := by
              rw [add_comm]
      _ = (h.rotation (i - j) * h.rotation j) x := by
              rw [h.rotation_add]
      _ = h.rotation (i - j) (h.rotation j x) := by
              simp [Equiv.Perm.mul_apply]
  exact (h.rotation j).injective (hcomm_at_x.trans hfix_at_j)

/-- An orbit map is injective if no nonzero rotation fixes the point. -/
theorem rotation_orbit_injective_of_no_nonzero_fixed
    (h : D19ActsOnMoore57 V Γ) {x : V}
    (hnot_fixed : ∀ d : ZMod 19, d ≠ 0 → h.rotation d x ≠ x) :
    Function.Injective (fun n : ZMod 19 => h.rotation n x) := by
  intro i j hij
  have hfix : h.rotation (i - j) x = x :=
    h.rotation_sub_fixed_of_rotation_eq hij
  have hdiff_zero : i - j = 0 := by
    by_contra hdiff_ne_zero
    exact hnot_fixed (i - j) hdiff_ne_zero hfix
  exact sub_eq_zero.mp hdiff_zero

/-- In the order-19 rotation subgroup, if one nonzero rotation moves `x`, then
the full rotation orbit map through `x` is injective. -/
theorem rotation_orbit_injective_of_nonzero_moved
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} {x : V}
    (hd : d ≠ 0) (hmove : h.rotation d x ≠ x) :
    Function.Injective (fun n : ZMod 19 => h.rotation n x) := by
  apply h.rotation_orbit_injective_of_no_nonzero_fixed
  intro e he hfix
  have hx_fixed_e : x ∈ fixedVertexSet (h.rotation e) := by
    simpa [fixedVertexSet] using hfix
  have hfixed_sets :
      fixedVertexSet (h.rotation e) = fixedVertexSet (h.rotation d) :=
    h.fixedVertexSet_rotation_eq_of_nonzero he hd
  have hx_fixed_d : x ∈ fixedVertexSet (h.rotation d) := by
    simpa [hfixed_sets] using hx_fixed_e
  exact hmove (by simpa [fixedVertexSet] using hx_fixed_d)

end D19ActsOnMoore57

end Moore57

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- All nontrivial rotations have the same number of fixed vertices. -/
theorem fixedVertexCount_rotation_eq_of_nonzero
    (h : D19ActsOnMoore57 V Γ) {d e : ZMod 19} (hd : d ≠ 0) (he : e ≠ 0) :
    fixedVertexCount (h.rotation d) = fixedVertexCount (h.rotation e) := by
  calc
    fixedVertexCount (h.rotation d)
        = Fintype.card (fixedVertexSet (h.rotation d)) := by
          rw [fixedVertexCount_eq_card_fixedVertexSet]
    _ = Fintype.card (fixedVertexSet (h.rotation e)) := by
          exact Fintype.card_congr
            (Equiv.setCongr (h.fixedVertexSet_rotation_eq_of_nonzero hd he))
    _ = fixedVertexCount (h.rotation e) := by
          rw [fixedVertexCount_eq_card_fixedVertexSet]

/-- Every nontrivial rotation has the same fixed-vertex count as rotation by `1`. -/
theorem fixedVertexCount_rotation_eq_one
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} (hd : d ≠ 0) :
    fixedVertexCount (h.rotation d) = fixedVertexCount (h.rotation 1) := by
  exact h.fixedVertexCount_rotation_eq_of_nonzero hd (by decide)

end D19ActsOnMoore57

end Moore57

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

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The fixed neighbors of a vertex are, in particular, ordinary neighbors. -/
theorem fixedNeighborFinset_subset_neighborFinset
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) (v : V) :
    h.fixedNeighborFinset d v ⊆ Γ.neighborFinset v := by
  intro w hw
  exact (Finset.mem_filter.mp hw).1

/-- In a Moore57 graph, a fixed-neighbor finset has cardinality at most `57`. -/
theorem fixedNeighborFinset_card_le_fiftySeven
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) (v : V) :
    (h.fixedNeighborFinset d v).card ≤ 57 := by
  have hle :
      (h.fixedNeighborFinset d v).card ≤ (Γ.neighborFinset v).card :=
    Finset.card_le_card (h.fixedNeighborFinset_subset_neighborFinset d v)
  have hdeg : (Γ.neighborFinset v).card = 57 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, h.isMoore.regular.degree_eq v]
  exact hle.trans_eq hdeg

/-- If a rotation has more than one fixed vertex, every fixed vertex has
`19`, `38`, or `57` fixed neighbors. -/
theorem fixedNeighborFinset_card_eq_19_or_38_or_57
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19)
    (hcount : fixedVertexCount (h.rotation d) ≠ 1)
    {v : V} (hv : h.rotation d v = v) :
    (h.fixedNeighborFinset d v).card = 19 ∨
      (h.fixedNeighborFinset d v).card = 38 ∨
        (h.fixedNeighborFinset d v).card = 57 := by
  let n := (h.fixedNeighborFinset d v).card
  have hge : 19 ≤ n := by
    simpa [n] using
      h.card_fixedNeighborFinset_ge_nineteen_of_fixedVertexCount_ne_one
        d hv hcount
  have hle : n ≤ 57 := by
    simpa [n] using h.fixedNeighborFinset_card_le_fiftySeven d v
  have hmod : n ≡ 0 [MOD 19] := by
    simpa [n] using h.card_fixedNeighborFinset_rotation_modEq_zero_of_moore d hv
  change n = 19 ∨ n = 38 ∨ n = 57
  have hdvd : 19 ∣ n := Nat.modEq_zero_iff_dvd.mp hmod
  rcases hdvd with ⟨m, hm⟩
  have hm_pos : 1 ≤ m := by omega
  have hm_le : m ≤ 3 := by omega
  rw [hm]
  interval_cases m <;> omega

/-- A vertex moved by rotation `1` is adjacent to at most one vertex fixed by
rotation `1`.

If it had two distinct fixed neighbors, either those fixed neighbors are
adjacent, giving a triangle, or they are non-adjacent.  In the non-adjacent
case the moved vertex and its rotation give a forbidden `4`-cycle. -/
theorem moved_vertex_fixedNeighbor_card_le_one
    (h : D19ActsOnMoore57 V Γ) {y : V}
    (hy : y ∉ fixedVertexSet (h.rotation 1)) :
    ((Γ.neighborFinset y).filter fun x => h.rotation 1 x = x).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro x z hx hz
  by_contra hxz
  have hyx : Γ.Adj y x := by
    exact (SimpleGraph.mem_neighborFinset (G := Γ) (v := y) (w := x)).1
      (Finset.mem_filter.mp hx).1
  have hyz : Γ.Adj y z := by
    exact (SimpleGraph.mem_neighborFinset (G := Γ) (v := y) (w := z)).1
      (Finset.mem_filter.mp hz).1
  have hxfix : h.rotation 1 x = x := (Finset.mem_filter.mp hx).2
  have hzfix : h.rotation 1 z = z := (Finset.mem_filter.mp hz).2
  by_cases hxz_adj : Γ.Adj x z
  · exact False.elim (h.isMoore.no_triangle hyx hxz_adj hyz.symm)
  · have hry_ne_y : h.rotation 1 y ≠ y := by
      intro hry
      exact hy hry
    have hy_ne_x : y ≠ x := Γ.ne_of_adj hyx
    have hy_ne_z : y ≠ z := Γ.ne_of_adj hyz
    have hx_ne_ry : x ≠ h.rotation 1 y := by
      intro hxry
      have hrot_eq : h.rotation 1 x = h.rotation 1 y := by
        exact hxfix.trans hxry
      exact hy_ne_x ((h.rotation 1).injective hrot_eq).symm
    have hz_ne_ry : z ≠ h.rotation 1 y := by
      intro hzry
      have hrot_eq : h.rotation 1 z = h.rotation 1 y := by
        exact hzfix.trans hzry
      exact hy_ne_z ((h.rotation 1).injective hrot_eq).symm
    have h_x_ry : Γ.Adj x (h.rotation 1 y) := by
      have hrotAdj :
          Γ.Adj (h.rotation 1 x) (h.rotation 1 y) := by
        simpa [D19ActsOnMoore57.rotation] using
          (h.smul_adj (DihedralGroup.r (1 : ZMod 19)) x y).mp hyx.symm
      simpa [hxfix] using hrotAdj
    have h_ry_z : Γ.Adj (h.rotation 1 y) z := by
      have hrotAdj :
          Γ.Adj (h.rotation 1 y) (h.rotation 1 z) := by
        simpa [D19ActsOnMoore57.rotation] using
          (h.smul_adj (DihedralGroup.r (1 : ZMod 19)) y z).mp hyz
      simpa [hzfix] using hrotAdj
    exact h.isMoore.no_four_cycle
      (x0 := y) (x1 := x) (x2 := h.rotation 1 y) (x3 := z)
      hy_ne_x (fun hEq => hry_ne_y hEq.symm) hy_ne_z hx_ne_ry hxz
      (fun hEq => hz_ne_ry hEq.symm)
      hyx h_x_ry h_ry_z hyz.symm

/-- Double-count edges from the fixed set of rotation `1` to its complement.

If every fixed vertex has exactly `k` fixed neighbors, then each fixed vertex
has `57 - k` neighbors outside the fixed set, while every outside vertex has
at most one fixed neighbor. -/
theorem fixed_moved_cross_edge_bound
    (h : D19ActsOnMoore57 V Γ) (k : ℕ)
    (hreg : ∀ x : V, h.rotation 1 x = x →
      (h.fixedNeighborFinset 1 x).card = k) :
    fixedVertexCount (h.rotation 1) * (57 - k) ≤
      Fintype.card V - fixedVertexCount (h.rotation 1) := by
  classical
  let S : Finset V := (fixedVertexSet (h.rotation 1)).toFinset
  let T : Finset V := Sᶜ
  have hS_mem (x : V) : x ∈ S ↔ h.rotation 1 x = x := by
    simp [S, fixedVertexSet]
  have hT_mem (x : V) : x ∈ T ↔ h.rotation 1 x ≠ x := by
    simp [T, S, fixedVertexSet]
  have h_above :
      ∀ x ∈ S, 57 - k ≤ (T.bipartiteAbove Γ.Adj x).card := by
    intro x hxS
    have hxfix : h.rotation 1 x = x := (hS_mem x).mp hxS
    have hfilter :
        T.bipartiteAbove Γ.Adj x =
          (Γ.neighborFinset x).filter fun y => h.rotation 1 y ≠ y := by
      ext y
      simp [Finset.mem_bipartiteAbove, hT_mem,
        SimpleGraph.mem_neighborFinset, and_comm]
    have hfixed :
        ((Γ.neighborFinset x).filter fun y => h.rotation 1 y = y).card = k := by
      simpa [fixedNeighborFinset] using hreg x hxfix
    have hsum :
        ((Γ.neighborFinset x).filter fun y => h.rotation 1 y = y).card +
          ((Γ.neighborFinset x).filter fun y => h.rotation 1 y ≠ y).card =
            (Γ.neighborFinset x).card := by
      simpa using
        (Finset.card_filter_add_card_filter_not
          (s := Γ.neighborFinset x) (p := fun y => h.rotation 1 y = y))
    have hdeg : (Γ.neighborFinset x).card = 57 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, h.isMoore.regular.degree_eq x]
    have hmoved :
        ((Γ.neighborFinset x).filter fun y => h.rotation 1 y ≠ y).card = 57 - k := by
      omega
    rw [hfilter, hmoved]
  have h_below :
      ∀ y ∈ T, (S.bipartiteBelow Γ.Adj y).card ≤ 1 := by
    intro y hyT
    have hymove : y ∉ fixedVertexSet (h.rotation 1) := by
      simpa [fixedVertexSet] using (hT_mem y).mp hyT
    have hfilter :
        S.bipartiteBelow Γ.Adj y =
          (Γ.neighborFinset y).filter fun x => h.rotation 1 x = x := by
      ext x
      simp [Finset.mem_bipartiteBelow, hS_mem,
        SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm, and_comm]
    rw [hfilter]
    exact h.moved_vertex_fixedNeighbor_card_le_one hymove
  have hdouble :
      S.card * (57 - k) ≤ T.card * 1 :=
    Finset.card_mul_le_card_mul Γ.Adj (s := S) (t := T)
      (m := 57 - k) (n := 1) h_above h_below
  have hScard : S.card = fixedVertexCount (h.rotation 1) := by
    simp [S, fixedVertexCount, fixedVertexSet_toFinset_eq_filter]
  have hTcard : T.card = Fintype.card V - fixedVertexCount (h.rotation 1) := by
    change Sᶜ.card = Fintype.card V - fixedVertexCount (h.rotation 1)
    rw [Finset.card_compl, hScard]
  simpa [hScard, hTcard] using hdouble

/-- The subgraph induced on vertices fixed by rotation `1` is strongly regular
with parameters `(fixedVertexCount, k, 0, 1)` whenever its fixed-neighbor
degree is constantly `k`. -/
theorem fixedInducedGraph_rotation_one_isSRGWith_of_regular
    (h : D19ActsOnMoore57 V Γ) (k : ℕ)
    (hreg : ∀ x : fixedVertexSet (h.rotation 1),
      (h.fixedNeighborFinset 1 (x : V)).card = k) :
    (Γ.induce (fixedVertexSet (h.rotation 1))).IsSRGWith
      (fixedVertexCount (h.rotation 1)) k 0 1 where
  card := by
    rw [fixedVertexCount_eq_card_fixedVertexSet]
  regular := by
    intro x
    rw [h.fixedInducedGraph_rotation_degree_eq_fixedNeighborFinset_card 1 x]
    exact hreg x
  of_adj := by
    intro x y hxy
    simpa [fixedInducedGraph, D19ActsOnMoore57.rotation] using
      h.fixedInducedGraph_commonNeighbors_card_of_adj
        (DihedralGroup.r (1 : ZMod 19))
        (x := x) (y := y)
        (by simpa [fixedInducedGraph, D19ActsOnMoore57.rotation] using hxy)
  of_not_adj := by
    intro x y hxy_ne hxy_not
    simpa [fixedInducedGraph, D19ActsOnMoore57.rotation] using
      h.fixedInducedGraph_commonNeighbors_card_of_not_adj
        (DihedralGroup.r (1 : ZMod 19))
        (x := x) (y := y)
        hxy_ne
        (by simpa [fixedInducedGraph, D19ActsOnMoore57.rotation] using hxy_not)

/-- If the fixed induced graph for rotation `1` is regular of one of the
possible nonzero degrees, its number of vertices is `k^2 + 1`. -/
theorem fixedVertexCount_rotation_one_eq_degree_sq_add_one_of_regular_candidate
    (h : D19ActsOnMoore57 V Γ) (k : ℕ)
    (hreg : ∀ x : fixedVertexSet (h.rotation 1),
      (h.fixedNeighborFinset 1 (x : V)).card = k)
    (hk : k = 19 ∨ k = 38 ∨ k = 57) :
    fixedVertexCount (h.rotation 1) = k * k + 1 := by
  let Gfix := Γ.induce (fixedVertexSet (h.rotation 1))
  have hsrg :
      Gfix.IsSRGWith (fixedVertexCount (h.rotation 1)) k 0 1 :=
    h.fixedInducedGraph_rotation_one_isSRGWith_of_regular k hreg
  have hpos : 0 < fixedVertexCount (h.rotation 1) :=
    h.fixedVertexCount_rotation_pos 1
  have hparam := SimpleGraph.IsSRGWith.param_eq Gfix hsrg hpos
  rcases hk with rfl | rfl | rfl <;> norm_num at hparam ⊢ <;> omega

/-- If, whenever rotation `1` has more than one fixed point, the induced fixed
graph is regular of one of the three possible fixed-neighbor degrees, then
rotation `1` has exactly one fixed point.

This isolates the remaining regularity task from the arithmetic and
cross-edge contradiction. -/
theorem rotation_one_fixedVertexCount_eq_one_of_regular_if_not_one
    (h : D19ActsOnMoore57 V Γ)
    (hregular :
      fixedVertexCount (h.rotation 1) ≠ 1 →
        ∃ k : ℕ,
          (∀ x : fixedVertexSet (h.rotation 1),
            (h.fixedNeighborFinset 1 (x : V)).card = k) ∧
          (k = 19 ∨ k = 38 ∨ k = 57)) :
    fixedVertexCount (h.rotation 1) = 1 := by
  by_contra hne
  rcases hregular hne with ⟨k, hreg, hk⟩
  have hcount :
      fixedVertexCount (h.rotation 1) = k * k + 1 :=
    h.fixedVertexCount_rotation_one_eq_degree_sq_add_one_of_regular_candidate
      k hreg hk
  have hcross :
      fixedVertexCount (h.rotation 1) * (57 - k) ≤
        Fintype.card V - fixedVertexCount (h.rotation 1) :=
    h.fixed_moved_cross_edge_bound k (by
      intro x hx
      exact hreg ⟨x, hx⟩)
  have hcard : Fintype.card V = 3250 := h.card_vertices
  rcases hk with rfl | rfl | rfl
  · omega
  · omega
  · have hlt :
        fixedVertexCount (h.rotation (1 : ZMod 19)) < Fintype.card V :=
      h.fixedVertexCount_rotation_lt_card (by decide)
    omega

/-- Conditional all-nontrivial-rotation version of
`rotation_one_fixedVertexCount_eq_one_of_regular_if_not_one`. -/
theorem rotation_fixed_card_eq_one_of_regular_if_not_one
    (h : D19ActsOnMoore57 V Γ)
    (hregular :
      fixedVertexCount (h.rotation 1) ≠ 1 →
        ∃ k : ℕ,
          (∀ x : fixedVertexSet (h.rotation 1),
            (h.fixedNeighborFinset 1 (x : V)).card = k) ∧
          (k = 19 ∨ k = 38 ∨ k = 57)) :
    ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1 := by
  intro d hd
  rw [h.fixedVertexCount_rotation_eq_one hd]
  exact h.rotation_one_fixedVertexCount_eq_one_of_regular_if_not_one hregular

end D19ActsOnMoore57

end Moore57

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- For two non-adjacent fixed vertices `p,q`, deleting their common fixed
neighbor `z` gives an injection from the fixed neighbors of `p` to those of
`q`. -/
theorem fixedNeighborFinset_erase_card_le_of_rotation_one_fixed_of_not_adj
    (h : D19ActsOnMoore57 V Γ) {p q z : V}
    (_hp : h.rotation 1 p = p) (hq : h.rotation 1 q = q)
    (hpq : p ≠ q) (hpq_not_adj : ¬ Γ.Adj p q)
    (hpz : Γ.Adj p z) (hqz : Γ.Adj q z)
    (_hz : h.rotation 1 z = z) :
    ((h.fixedNeighborFinset 1 p).erase z).card ≤
      ((h.fixedNeighborFinset 1 q).erase z).card := by
  classical
  let A := ((h.fixedNeighborFinset 1 p).erase z : Set V)
  let B := ((h.fixedNeighborFinset 1 q).erase z : Set V)
  have hExists : ∀ a : A, ∃ b : V,
      b ∈ (h.fixedNeighborFinset 1 q).erase z ∧ Γ.Adj (a : V) b := by
    intro a
    have haErase : (a : V) ∈ (h.fixedNeighborFinset 1 p).erase z := by
      change (a : V) ∈ ((h.fixedNeighborFinset 1 p).erase z : Set V)
      exact a.property
    have ha_ne_z : (a : V) ≠ z := (Finset.mem_erase.mp haErase).1
    have haN : (a : V) ∈ h.fixedNeighborFinset 1 p :=
      (Finset.mem_erase.mp haErase).2
    have hpa : Γ.Adj p (a : V) := (mem_fixedNeighborFinset h 1 p (a : V)).mp haN |>.1
    have haFixed : h.rotation 1 (a : V) = (a : V) :=
      (mem_fixedNeighborFinset h 1 p (a : V)).mp haN |>.2
    have haq : (a : V) ≠ q := by
      intro haq
      exact hpq_not_adj (by simpa [haq] using hpa)
    have haq_not_adj : ¬ Γ.Adj (a : V) q := by
      intro haqAdj
      exact h.isMoore.no_four_cycle
        (x0 := p) (x1 := (a : V)) (x2 := q) (x3 := z)
        (Γ.ne_of_adj hpa) hpq (Γ.ne_of_adj hpz)
        (Γ.ne_of_adj haqAdj) ha_ne_z (Γ.ne_of_adj hqz)
        hpa haqAdj hqz hpz.symm
    have haSmul : h.smul (DihedralGroup.r (1 : ZMod 19)) (a : V) = (a : V) := by
      simpa [rotation] using haFixed
    have hqSmul : h.smul (DihedralGroup.r (1 : ZMod 19)) q = q := by
      simpa [rotation] using hq
    rcases h.exists_fixed_commonNeighbor_of_not_adj
        (DihedralGroup.r (1 : ZMod 19)) haSmul hqSmul haq haq_not_adj with
      ⟨b, hbFixedSmul, hab, hqb⟩
    have hbFixed : h.rotation 1 b = b := by
      simpa [rotation] using hbFixedSmul
    have hb_ne_z : b ≠ z := by
      intro hbz
      have hza : Γ.Adj z (a : V) := by
        simpa [hbz] using hab.symm
      exact h.isMoore.no_triangle hpz hza hpa.symm
    have hbN : b ∈ h.fixedNeighborFinset 1 q :=
      (mem_fixedNeighborFinset h 1 q b).2 ⟨hqb, hbFixed⟩
    exact ⟨b, Finset.mem_erase.mpr ⟨hb_ne_z, hbN⟩, hab⟩
  let f : A → B := fun a =>
    ⟨Classical.choose (hExists a), by
      change Classical.choose (hExists a) ∈
        ((h.fixedNeighborFinset 1 q).erase z : Set V)
      exact (Classical.choose_spec (hExists a)).1⟩
  have hf_inj : Function.Injective f := by
    intro a₁ a₂ hfa
    apply Subtype.ext
    by_contra ha_ne
    have ha₁Erase : (a₁ : V) ∈ (h.fixedNeighborFinset 1 p).erase z := by
      change (a₁ : V) ∈ ((h.fixedNeighborFinset 1 p).erase z : Set V)
      exact a₁.property
    have ha₂Erase : (a₂ : V) ∈ (h.fixedNeighborFinset 1 p).erase z := by
      change (a₂ : V) ∈ ((h.fixedNeighborFinset 1 p).erase z : Set V)
      exact a₂.property
    have ha₁N : (a₁ : V) ∈ h.fixedNeighborFinset 1 p :=
      (Finset.mem_erase.mp ha₁Erase).2
    have ha₂N : (a₂ : V) ∈ h.fixedNeighborFinset 1 p :=
      (Finset.mem_erase.mp ha₂Erase).2
    have hpa₁ : Γ.Adj p (a₁ : V) :=
      (mem_fixedNeighborFinset h 1 p (a₁ : V)).mp ha₁N |>.1
    have hpa₂ : Γ.Adj p (a₂ : V) :=
      (mem_fixedNeighborFinset h 1 p (a₂ : V)).mp ha₂N |>.1
    have ha₁b : Γ.Adj (a₁ : V) (f a₁ : V) :=
      (Classical.choose_spec (hExists a₁)).2
    have ha₂b' : Γ.Adj (a₂ : V) (f a₂ : V) :=
      (Classical.choose_spec (hExists a₂)).2
    have hbEq : (f a₁ : V) = (f a₂ : V) := congrArg Subtype.val hfa
    have hba₂ : Γ.Adj (f a₁ : V) (a₂ : V) := by
      have : Γ.Adj (a₂ : V) (f a₁ : V) := by
        simpa [hbEq] using ha₂b'
      exact this.symm
    have hpb : p ≠ (f a₁ : V) := by
      intro hpb
      have hbErase : (f a₁ : V) ∈ (h.fixedNeighborFinset 1 q).erase z := by
        change (f a₁ : V) ∈ ((h.fixedNeighborFinset 1 q).erase z : Set V)
        exact (f a₁).property
      have hbN : (f a₁ : V) ∈ h.fixedNeighborFinset 1 q :=
        (Finset.mem_erase.mp hbErase).2
      have hqb : Γ.Adj q (f a₁ : V) :=
        (mem_fixedNeighborFinset h 1 q (f a₁ : V)).mp hbN |>.1
      exact hpq_not_adj (by simpa [← hpb] using hqb.symm)
    exact h.isMoore.no_four_cycle
      (x0 := p) (x1 := (a₁ : V)) (x2 := (f a₁ : V)) (x3 := (a₂ : V))
      (Γ.ne_of_adj hpa₁) hpb (Γ.ne_of_adj hpa₂)
      (Γ.ne_of_adj ha₁b) ha_ne (Γ.ne_of_adj hba₂)
      hpa₁ ha₁b hba₂ hpa₂.symm
  have hcard : Fintype.card A ≤ Fintype.card B :=
    Fintype.card_le_of_injective f hf_inj
  have hAcard : Fintype.card A = ((h.fixedNeighborFinset 1 p).erase z).card := by
    change Fintype.card {w : V // w ∈
      (((h.fixedNeighborFinset 1 p).erase z : Finset V) : Set V)} =
        ((h.fixedNeighborFinset 1 p).erase z).card
    exact Fintype.card_ofFinset ((h.fixedNeighborFinset 1 p).erase z) (by intro w; rfl)
  have hBcard : Fintype.card B = ((h.fixedNeighborFinset 1 q).erase z).card := by
    change Fintype.card {w : V // w ∈
      (((h.fixedNeighborFinset 1 q).erase z : Finset V) : Set V)} =
        ((h.fixedNeighborFinset 1 q).erase z).card
    exact Fintype.card_ofFinset ((h.fixedNeighborFinset 1 q).erase z) (by intro w; rfl)
  omega

/-- Non-adjacent vertices fixed by rotation `1` have the same degree in the
fixed induced graph. -/
theorem fixedNeighborFinset_card_eq_of_rotation_one_fixed_of_not_adj
    (h : D19ActsOnMoore57 V Γ) {x y : V}
    (hx : h.rotation 1 x = x) (hy : h.rotation 1 y = y)
    (hxy : x ≠ y) (hxy_not_adj : ¬ Γ.Adj x y) :
    (h.fixedNeighborFinset 1 x).card = (h.fixedNeighborFinset 1 y).card := by
  classical
  have hxSmul : h.smul (DihedralGroup.r (1 : ZMod 19)) x = x := by
    simpa [rotation] using hx
  have hySmul : h.smul (DihedralGroup.r (1 : ZMod 19)) y = y := by
    simpa [rotation] using hy
  rcases h.exists_fixed_commonNeighbor_of_not_adj
      (DihedralGroup.r (1 : ZMod 19)) hxSmul hySmul hxy hxy_not_adj with
    ⟨z, hzSmul, hxz, hyz⟩
  have hz : h.rotation 1 z = z := by
    simpa [rotation] using hzSmul
  have hzNx : z ∈ h.fixedNeighborFinset 1 x :=
    (mem_fixedNeighborFinset h 1 x z).2 ⟨hxz, hz⟩
  have hzNy : z ∈ h.fixedNeighborFinset 1 y :=
    (mem_fixedNeighborFinset h 1 y z).2 ⟨hyz, hz⟩
  have hle :
      ((h.fixedNeighborFinset 1 x).erase z).card ≤
        ((h.fixedNeighborFinset 1 y).erase z).card :=
    h.fixedNeighborFinset_erase_card_le_of_rotation_one_fixed_of_not_adj
      hx hy hxy hxy_not_adj hxz hyz hz
  have hge :
      ((h.fixedNeighborFinset 1 y).erase z).card ≤
        ((h.fixedNeighborFinset 1 x).erase z).card :=
    h.fixedNeighborFinset_erase_card_le_of_rotation_one_fixed_of_not_adj
      hy hx hxy.symm (by intro hyx; exact hxy_not_adj hyx.symm) hyz hxz hz
  have hxErase :
      ((h.fixedNeighborFinset 1 x).erase z).card + 1 =
        (h.fixedNeighborFinset 1 x).card :=
    Finset.card_erase_add_one hzNx
  have hyErase :
      ((h.fixedNeighborFinset 1 y).erase z).card + 1 =
        (h.fixedNeighborFinset 1 y).card :=
    Finset.card_erase_add_one hzNy
  omega

/-- Under `fixedVertexCount (rotation 1) ≠ 1`, a fixed vertex has a fixed
neighbor different from any prescribed vertex. -/
theorem exists_fixedNeighbor_ne_of_rotation_one_fixed_of_count_ne_one
    (h : D19ActsOnMoore57 V Γ)
    (hcount : fixedVertexCount (h.rotation 1) ≠ 1)
    {x y : V} (hx : h.rotation 1 x = x) :
    ∃ z, z ∈ h.fixedNeighborFinset 1 x ∧ z ≠ y := by
  classical
  have hge : 19 ≤ (h.fixedNeighborFinset 1 x).card :=
    h.card_fixedNeighborFinset_ge_nineteen_of_fixedVertexCount_ne_one 1 hx hcount
  have hone : 1 < (h.fixedNeighborFinset 1 x).card := by omega
  rcases Finset.one_lt_card_iff.mp hone with ⟨a, b, ha, hb, hab⟩
  by_cases hay : a = y
  · exact ⟨b, hb, by
      intro hby
      exact hab (hay.trans hby.symm)⟩
  · exact ⟨a, ha, hay⟩

/-- Rotation-`1` fixed vertices have constant fixed-neighbor degree whenever the
rotation has fixed count different from `1`. -/
theorem fixedNeighborFinset_card_eq_of_rotation_one_fixed_of_count_ne_one
    (h : D19ActsOnMoore57 V Γ)
    (hcount : fixedVertexCount (h.rotation 1) ≠ 1)
    {x y : V} (hx : h.rotation 1 x = x) (hy : h.rotation 1 y = y) :
    (h.fixedNeighborFinset 1 x).card = (h.fixedNeighborFinset 1 y).card := by
  classical
  by_cases hxy : x = y
  · subst y
    rfl
  by_cases hxyAdj : Γ.Adj x y
  · rcases h.exists_fixedNeighbor_ne_of_rotation_one_fixed_of_count_ne_one
        hcount hx with ⟨a, haN, ha_ne_y⟩
    rcases h.exists_fixedNeighbor_ne_of_rotation_one_fixed_of_count_ne_one
        hcount hy with ⟨b, hbN, hb_ne_x⟩
    have hxa : Γ.Adj x a := (mem_fixedNeighborFinset h 1 x a).mp haN |>.1
    have haFixed : h.rotation 1 a = a := (mem_fixedNeighborFinset h 1 x a).mp haN |>.2
    have hyb : Γ.Adj y b := (mem_fixedNeighborFinset h 1 y b).mp hbN |>.1
    have hbFixed : h.rotation 1 b = b := (mem_fixedNeighborFinset h 1 y b).mp hbN |>.2
    have hay_not_adj : ¬ Γ.Adj a y := by
      intro hay
      exact h.isMoore.no_triangle hxyAdj hay.symm hxa.symm
    have hxb_not_adj : ¬ Γ.Adj x b := by
      intro hxb
      exact h.isMoore.no_triangle hxyAdj hyb hxb.symm
    have hab_not_adj : ¬ Γ.Adj a b := by
      intro hab
      exact h.isMoore.no_four_cycle
        (x0 := x) (x1 := a) (x2 := b) (x3 := y)
        (Γ.ne_of_adj hxa) (by
          intro hxbEq
          exact hb_ne_x hxbEq.symm)
        hxy
        (Γ.ne_of_adj hab) (by
          intro hayEq
          exact ha_ne_y hayEq)
        (Γ.ne_of_adj hyb).symm
        hxa hab hyb.symm hxyAdj.symm
    have hya :
        (h.fixedNeighborFinset 1 y).card = (h.fixedNeighborFinset 1 a).card := by
      exact h.fixedNeighborFinset_card_eq_of_rotation_one_fixed_of_not_adj
        hy haFixed (by intro hyaEq; exact ha_ne_y hyaEq.symm)
        (by intro hyaAdj; exact hay_not_adj hyaAdj.symm)
    have habEq :
        (h.fixedNeighborFinset 1 a).card = (h.fixedNeighborFinset 1 b).card :=
      h.fixedNeighborFinset_card_eq_of_rotation_one_fixed_of_not_adj
        haFixed hbFixed (by
          intro habEq
          exact h.isMoore.no_triangle hxyAdj (by simpa [← habEq] using hyb) hxa.symm)
        hab_not_adj
    have hxb :
        (h.fixedNeighborFinset 1 x).card = (h.fixedNeighborFinset 1 b).card :=
      h.fixedNeighborFinset_card_eq_of_rotation_one_fixed_of_not_adj
        hx hbFixed (by intro hxbEq; exact hb_ne_x hxbEq.symm) hxb_not_adj
    exact hxb.trans (habEq.symm.trans hya.symm)
  · exact h.fixedNeighborFinset_card_eq_of_rotation_one_fixed_of_not_adj
      hx hy hxy hxyAdj

/-- Rotation by `1` has exactly one fixed vertex.

This is the specialisation of the abstract `order19_aut_fixedVertexCount_eq_one`
to the `D₁₉`-action rotation `h.rotation 1`. The same Tier-2 theorem also
covers the cyclic-group case `C₃₈ = ⟨g⟩` via its order-19 element `g^2`. -/
theorem rotation_one_fixedVertexCount_eq_one
    (h : D19ActsOnMoore57 V Γ) :
    fixedVertexCount (h.rotation 1) = 1 :=
  order19_aut_fixedVertexCount_eq_one h.isMoore (h.rotation 1)
    (by
      intro v w
      simpa [D19ActsOnMoore57.rotation] using
        h.smul_adj (DihedralGroup.r (1 : ZMod 19)) v w)
    (h.rotation_pow_nineteen 1)
    (h.rotation_ne_one (by decide))

/-- Every nontrivial rotation has exactly one fixed vertex. -/
theorem rotation_fixed_card_eq_one
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} (hd : d ≠ 0) :
    fixedVertexCount (h.rotation d) = 1 := by
  rw [h.fixedVertexCount_rotation_eq_one hd]
  exact h.rotation_one_fixedVertexCount_eq_one

end D19ActsOnMoore57

end Moore57

