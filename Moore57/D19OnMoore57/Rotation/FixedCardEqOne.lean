import Moore57.D19OnMoore57.Rotation.FixedCardConstraints
import Moore57.D19OnMoore57.Rotation.FixedCardEquality
import Moore57.D19OnMoore57.Rotation.OrbitInjectivity
import Moore57.D19OnMoore57.Fixed.InducedDegree

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
