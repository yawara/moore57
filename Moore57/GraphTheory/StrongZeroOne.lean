import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Tactic

namespace Moore57

noncomputable section

/-- Non-regular strong graph condition with parameters `λ = 0`, `μ = 1`.
This is the exact paper-level condition used before the fixed graph is
classified as either a Moore graph or a star. -/
structure IsStrongZeroOne {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  of_adj : ∀ v w : V, G.Adj v w → Fintype.card (G.commonNeighbors v w) = 0
  of_not_adj :
    ∀ v w : V, v ≠ w → ¬ G.Adj v w →
      Fintype.card (G.commonNeighbors v w) = 1

/-- There is no regular strongly-regular graph with parameters
`(n, k, λ, μ) = (56, k, 0, 1)`.  This is the arithmetic obstruction behind the
paper's fixed-graph classification once the fixed graph is assumed regular
with `56` vertices. -/
theorem not_isSRGWith_56_k_0_1 {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (k : ℕ) :
    ¬ G.IsSRGWith 56 k 0 1 := by
  intro hG
  have hparam := SimpleGraph.IsSRGWith.param_eq G hG (by norm_num)
  have hcard : Fintype.card V = 56 := hG.card
  have hnonempty : Nonempty V := by
    rw [← Fintype.card_pos_iff, hcard]
    norm_num
  rcases hnonempty with ⟨v⟩
  have hk_lt : k < 56 := by
    have hdegree := G.degree_lt_card_verts v
    simpa [hG.regular.degree_eq v, hcard] using hdegree
  have hk_le : k ≤ 55 := by omega
  by_cases hk_zero : k = 0
  · subst k
    norm_num at hparam
  have hk_pos : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk_zero)
  have hk_le56 : k ≤ 56 := by omega
  have hsub_pos : 1 ≤ 56 - k := by omega
  have hparam_int : (k : ℤ) * ((k : ℤ) - 1) = 56 - (k : ℤ) - 1 := by
    have hparam_nat : k * (k - 1) = 56 - k - 1 := by
      simpa using hparam
    have hparam_cast :
        ((k * (k - 1) : ℕ) : ℤ) = ((56 - k - 1 : ℕ) : ℤ) := by
      exact_mod_cast hparam_nat
    rw [Nat.cast_mul, Int.ofNat_sub hk_pos,
      Int.ofNat_sub hsub_pos, Int.ofNat_sub hk_le56] at hparam_cast
    norm_num at hparam_cast ⊢
    exact hparam_cast
  have hsquare : (k : ℤ) * (k : ℤ) = 55 := by
    calc
      (k : ℤ) * (k : ℤ) =
          (k : ℤ) * ((k : ℤ) - 1) + (k : ℤ) := by ring
      _ = 55 := by
        rw [hparam_int]
        ring
  by_cases hk_le7 : k ≤ 7
  · have hk_nonneg_int : 0 ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
    have hk_le7_int : (k : ℤ) ≤ 7 := by exact_mod_cast hk_le7
    nlinarith
  · have hk_ge8 : 8 ≤ k := by omega
    have hk_ge8_int : (8 : ℤ) ≤ k := by exact_mod_cast hk_ge8
    nlinarith

/-- There is no regular strongly-regular graph with parameters
`(n, k, λ, μ) = (n, k, 0, 1)` when `52 ≤ n ≤ 56`.  In this range the parameter
equation would force `k^2 = n - 1`, but no integer square lies between `51`
and `55`. -/
theorem not_isSRGWith_n_k_0_1_of_card_between_52_56
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (n k : ℕ)
    (hn_lower : 52 ≤ n) (hn_upper : n ≤ 56) :
    ¬ G.IsSRGWith n k 0 1 := by
  intro hG
  have hn_pos : 0 < n := by omega
  have hparam := SimpleGraph.IsSRGWith.param_eq G hG hn_pos
  have hcard : Fintype.card V = n := hG.card
  have hnonempty : Nonempty V := by
    rw [← Fintype.card_pos_iff, hcard]
    exact hn_pos
  rcases hnonempty with ⟨v⟩
  have hk_lt : k < n := by
    have hdegree := G.degree_lt_card_verts v
    simpa [hG.regular.degree_eq v, hcard] using hdegree
  have hk_le : k ≤ n := Nat.le_of_lt hk_lt
  have hparam_nat : k * (k - 1) = n - k - 1 := by
    simpa using hparam
  by_cases hk_zero : k = 0
  · subst k
    omega
  · have hk_pos : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk_zero)
    have hsub_pos : 1 ≤ n - k := by omega
    have hparam_int := congrArg (fun m : ℕ => (m : ℤ)) hparam_nat
    change ((k * (k - 1) : ℕ) : ℤ) = ((n - k - 1 : ℕ) : ℤ) at hparam_int
    rw [Nat.cast_mul, Nat.cast_sub hk_pos, Nat.cast_sub hsub_pos,
      Nat.cast_sub hk_le] at hparam_int
    norm_num at hparam_int
    have hsquare : (k : ℤ) * (k : ℤ) = (n : ℤ) - 1 := by
      calc
        (k : ℤ) * (k : ℤ) =
            (k : ℤ) * ((k : ℤ) - 1) + (k : ℤ) := by ring
        _ = (n : ℤ) - 1 := by
          rw [hparam_int]
          ring
    have hn_lower_cast : (52 : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast hn_lower
    have hn_upper_cast : (n : ℤ) ≤ 56 := by
      exact_mod_cast hn_upper
    have hn_lower_int : (51 : ℤ) ≤ (n : ℤ) - 1 := by
      linarith
    have hn_upper_int : (n : ℤ) - 1 ≤ (55 : ℤ) := by
      linarith
    by_cases hk_le7 : k ≤ 7
    · have hk_nonneg_int : 0 ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
      have hk_le7_int : (k : ℤ) ≤ 7 := by exact_mod_cast hk_le7
      nlinarith
    · have hk_ge8 : 8 ≤ k := by omega
      have hk_ge8_int : (8 : ℤ) ≤ k := by exact_mod_cast hk_ge8
      nlinarith

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `G` is a star whose center is `c`: every edge is exactly an edge from
`c` to a different vertex. -/
def IsStarWithCenter (G : SimpleGraph V) (c : V) : Prop :=
  ∀ v w : V, G.Adj v w ↔ (v = c ∧ w ≠ c) ∨ (w = c ∧ v ≠ c)

namespace IsStrongZeroOne

/-- In a strong `(λ, μ) = (0, 1)` graph, distinct non-adjacent vertices have a
unique common neighbor, in ordinary vertex form. -/
theorem existsUnique_commonNeighbor_of_not_adj
    (hG : IsStrongZeroOne G) {v w : V}
    (hne : v ≠ w) (hnadj : ¬ G.Adj v w) :
    ∃! u : V, G.Adj v u ∧ G.Adj w u := by
  have hcard : Fintype.card (G.commonNeighbors v w) = 1 :=
    hG.of_not_adj v w hne hnadj
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨c, hc_unique⟩
  refine ⟨(c : V), ?_, ?_⟩
  · exact c.property
  · intro u hu
    have hu_mem : u ∈ G.commonNeighbors v w := by
      rw [SimpleGraph.mem_commonNeighbors]
      exact hu
    exact congrArg Subtype.val (hc_unique ⟨u, hu_mem⟩)

/-- A chosen common neighbor for distinct non-adjacent vertices. -/
def commonNeighborOfNotAdj
    (hG : IsStrongZeroOne G) {v w : V}
    (hne : v ≠ w) (hnadj : ¬ G.Adj v w) : V :=
  Classical.choose (hG.existsUnique_commonNeighbor_of_not_adj hne hnadj)

theorem commonNeighborOfNotAdj_spec
    (hG : IsStrongZeroOne G) {v w : V}
    (hne : v ≠ w) (hnadj : ¬ G.Adj v w) :
    G.Adj v (hG.commonNeighborOfNotAdj hne hnadj) ∧
      G.Adj w (hG.commonNeighborOfNotAdj hne hnadj) :=
  (Classical.choose_spec (hG.existsUnique_commonNeighbor_of_not_adj hne hnadj)).1

theorem commonNeighborOfNotAdj_eq_of_common
    (hG : IsStrongZeroOne G) {v w u : V}
    (hne : v ≠ w) (hnadj : ¬ G.Adj v w)
    (hu : G.Adj v u ∧ G.Adj w u) :
    hG.commonNeighborOfNotAdj hne hnadj = u := by
  exact
    ((Classical.choose_spec
      (hG.existsUnique_commonNeighbor_of_not_adj hne hnadj)).2 u hu).symm

/-- Adjacent vertices have no common neighbor.  This is the triangle-free
consequence of the `λ = 0` half of `IsStrongZeroOne`. -/
theorem not_commonNeighbor_of_adj
    (hG : IsStrongZeroOne G) {v w u : V}
    (hadj : G.Adj v w) :
    ¬ (G.Adj v u ∧ G.Adj w u) := by
  intro hu
  have hu_mem : u ∈ G.commonNeighbors v w := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact hu
  have hcard : Fintype.card (G.commonNeighbors v w) = 0 :=
    hG.of_adj v w hadj
  have hpos : 0 < Fintype.card (G.commonNeighbors v w) := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨u, hu_mem⟩⟩
  omega

/-- Triangle-free form: if `b` and `c` are both adjacent to `a`, then `b` and
`c` are not adjacent. -/
theorem not_adj_of_adj_of_adj
    (hG : IsStrongZeroOne G) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) :
    ¬ G.Adj b c := by
  intro hbc
  exact hG.not_commonNeighbor_of_adj hbc ⟨hab.symm, hac.symm⟩

omit [DecidableEq V] in
private theorem neighborFinset_subtype_card (v : V) :
    Fintype.card {x : V // x ∈ G.neighborFinset v} = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact Fintype.card_ofFinset (G.neighborFinset v) (by intro x; rfl)

/-- If `v` and `w` are distinct and non-adjacent, then they have the same
degree. -/
theorem degree_eq_of_not_adj
    (hG : IsStrongZeroOne G) {v w : V}
    (hne : v ≠ w) (hnadj : ¬ G.Adj v w) :
    G.degree v = G.degree w := by
  classical
  let c : V := hG.commonNeighborOfNotAdj hne hnadj
  have hc : G.Adj v c ∧ G.Adj w c :=
    hG.commonNeighborOfNotAdj_spec hne hnadj
  let Nv := {x : V // x ∈ G.neighborFinset v}
  let Nw := {x : V // x ∈ G.neighborFinset w}
  have hmap_ne_w :
      ∀ x : Nv, (x : V) ≠ w := by
    intro x hxw
    have hx_adj : G.Adj v (x : V) :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := v) (x : V)).1 x.property
    exact hnadj (by simpa [hxw] using hx_adj)
  have hmap_not_adj_w :
      ∀ x : Nv, (x : V) ≠ c → ¬ G.Adj (x : V) w := by
    intro x hxc hxw
    have hx_adj : G.Adj v (x : V) :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := v) (x : V)).1 x.property
    have hx_common : G.Adj v (x : V) ∧ G.Adj w (x : V) :=
      ⟨hx_adj, hxw.symm⟩
    exact hxc (hG.commonNeighborOfNotAdj_eq_of_common hne hnadj hx_common).symm
  have hmap_ne_v :
      ∀ y : Nw, (y : V) ≠ v := by
    intro y hyv
    have hy_adj : G.Adj w (y : V) :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := w) (y : V)).1 y.property
    exact hnadj (by simpa [hyv] using hy_adj.symm)
  have hmap_not_adj_v :
      ∀ y : Nw, (y : V) ≠ c → ¬ G.Adj (y : V) v := by
    intro y hyc hyv
    have hy_adj : G.Adj w (y : V) :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := w) (y : V)).1 y.property
    have hy_common : G.Adj v (y : V) ∧ G.Adj w (y : V) :=
      ⟨hyv.symm, hy_adj⟩
    exact hyc (hG.commonNeighborOfNotAdj_eq_of_common hne hnadj hy_common).symm
  let f : Nv → Nw := fun x =>
    if hxc : (x : V) = c then
      ⟨c, (SimpleGraph.mem_neighborFinset (G := G) (v := w) c).2 hc.2⟩
    else
      let y : V :=
        hG.commonNeighborOfNotAdj (hmap_ne_w x) (hmap_not_adj_w x hxc)
      ⟨y, by
        have hy :=
          hG.commonNeighborOfNotAdj_spec (hmap_ne_w x) (hmap_not_adj_w x hxc)
        exact (SimpleGraph.mem_neighborFinset (G := G) (v := w) y).2 hy.2⟩
  let g : Nw → Nv := fun y =>
    if hyc : (y : V) = c then
      ⟨c, (SimpleGraph.mem_neighborFinset (G := G) (v := v) c).2 hc.1⟩
    else
      let x : V :=
        hG.commonNeighborOfNotAdj (hmap_ne_v y) (hmap_not_adj_v y hyc)
      ⟨x, by
        have hx :=
          hG.commonNeighborOfNotAdj_spec (hmap_ne_v y) (hmap_not_adj_v y hyc)
        exact (SimpleGraph.mem_neighborFinset (G := G) (v := v) x).2 hx.2⟩
  have hleft : Function.LeftInverse g f := by
    intro x
    apply Subtype.ext
    by_cases hxc : (x : V) = c
    · simp [f, g, hxc]
    · have hx_adj_v : G.Adj v (x : V) :=
        (SimpleGraph.mem_neighborFinset (G := G) (v := v) (x : V)).1 x.property
      let y : V :=
        hG.commonNeighborOfNotAdj (hmap_ne_w x) (hmap_not_adj_w x hxc)
      have hy : G.Adj (x : V) y ∧ G.Adj w y :=
        hG.commonNeighborOfNotAdj_spec (hmap_ne_w x) (hmap_not_adj_w x hxc)
      have hy_ne_c : y ≠ c := by
        intro hyc
        have hxc_adj : G.Adj (x : V) c := by
          simpa [y, hyc] using hy.1
        exact (hG.not_adj_of_adj_of_adj hx_adj_v hc.1) hxc_adj
      have hy_ne_v : y ≠ v := by
        intro hyv
        exact hnadj (by simpa [y, hyv] using hy.2.symm)
      have hy_not_adj_v : ¬ G.Adj y v := by
        intro hyv
        have hy_common : G.Adj v y ∧ G.Adj w y := ⟨hyv.symm, hy.2⟩
        exact hy_ne_c
          (hG.commonNeighborOfNotAdj_eq_of_common hne hnadj hy_common).symm
      have hx_eq :
          hG.commonNeighborOfNotAdj hy_ne_v hy_not_adj_v = (x : V) := by
        exact
          hG.commonNeighborOfNotAdj_eq_of_common
            hy_ne_v hy_not_adj_v ⟨hy.1.symm, hx_adj_v⟩
      simp [f, g, hxc, y, hy_ne_c, hx_eq]
  have hright : Function.RightInverse g f := by
    intro y
    apply Subtype.ext
    by_cases hyc : (y : V) = c
    · simp [f, g, hyc]
    · have hy_adj_w : G.Adj w (y : V) :=
        (SimpleGraph.mem_neighborFinset (G := G) (v := w) (y : V)).1 y.property
      let x : V :=
        hG.commonNeighborOfNotAdj (hmap_ne_v y) (hmap_not_adj_v y hyc)
      have hx : G.Adj (y : V) x ∧ G.Adj v x :=
        hG.commonNeighborOfNotAdj_spec (hmap_ne_v y) (hmap_not_adj_v y hyc)
      have hx_ne_c : x ≠ c := by
        intro hxc
        have hyc_adj : G.Adj (y : V) c := by
          simpa [x, hxc] using hx.1
        exact (hG.not_adj_of_adj_of_adj hy_adj_w hc.2) hyc_adj
      have hx_ne_w : x ≠ w := by
        intro hxw
        exact hnadj (by simpa [x, hxw] using hx.2)
      have hx_not_adj_w : ¬ G.Adj x w := by
        intro hxw_adj
        have hx_common : G.Adj v x ∧ G.Adj w x := ⟨hx.2, hxw_adj.symm⟩
        exact hx_ne_c
          (hG.commonNeighborOfNotAdj_eq_of_common hne hnadj hx_common).symm
      have hy_eq :
          hG.commonNeighborOfNotAdj hx_ne_w hx_not_adj_w = (y : V) := by
        exact
          hG.commonNeighborOfNotAdj_eq_of_common
            hx_ne_w hx_not_adj_w ⟨hx.1.symm, hy_adj_w⟩
      simp [f, g, hyc, x, hx_ne_c, hy_eq]
  have hcard :
      Fintype.card Nv = Fintype.card Nw :=
    Fintype.card_congr
      { toFun := f
        invFun := g
        left_inv := hleft
        right_inv := hright }
  calc
    G.degree v = Fintype.card Nv := by
      exact (neighborFinset_subtype_card (G := G) v).symm
    _ = Fintype.card Nw := hcard
    _ = G.degree w := by
      exact neighborFinset_subtype_card (G := G) w

/-- Vertices of different degrees must be adjacent. -/
theorem adj_of_degree_ne
    (hG : IsStrongZeroOne G) {v w : V}
    (hdeg : G.degree v ≠ G.degree w) :
    G.Adj v w := by
  by_cases hEq : v = w
  · subst w
    exact False.elim (hdeg rfl)
  by_cases hadj : G.Adj v w
  · exact hadj
  · exact False.elim (hdeg (hG.degree_eq_of_not_adj hEq hadj))

omit [DecidableEq V] in
/-- If `v` is adjacent to `w` and has degree different from `1`, then `v` has
some neighbor other than `w`. -/
theorem exists_neighbor_ne_of_adj_degree_ne_one
    {v w : V} (hadj : G.Adj v w) (hdeg : G.degree v ≠ 1) :
    ∃ u : V, G.Adj v u ∧ u ≠ w := by
  by_contra hnone
  have hunique : ∃! u : V, G.Adj v u := by
    refine ⟨w, hadj, ?_⟩
    intro u hu
    by_contra huw
    exact hnone ⟨u, hu, huw⟩
  exact hdeg (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr hunique)

/-- For adjacent vertices of different degrees, at least one endpoint has
degree `1`. -/
theorem degree_eq_one_or_degree_eq_one_of_adj_degree_ne
    (hG : IsStrongZeroOne G) {v w : V}
    (hadj : G.Adj v w) (hdeg : G.degree v ≠ G.degree w) :
    G.degree v = 1 ∨ G.degree w = 1 := by
  by_contra hnone
  have hv_ne_one : G.degree v ≠ 1 := by
    intro hv
    exact hnone (Or.inl hv)
  have hw_ne_one : G.degree w ≠ 1 := by
    intro hw
    exact hnone (Or.inr hw)
  rcases exists_neighbor_ne_of_adj_degree_ne_one (G := G) hadj hv_ne_one with
    ⟨x, hvx, hx_ne_w⟩
  rcases exists_neighbor_ne_of_adj_degree_ne_one (G := G) hadj.symm hw_ne_one with
    ⟨y, hwy, hy_ne_v⟩
  have hnot_wx : ¬ G.Adj w x :=
    hG.not_adj_of_adj_of_adj hadj hvx
  have hnot_xw : ¬ G.Adj x w := by
    intro hxw
    exact hnot_wx hxw.symm
  have hx_deg : G.degree x = G.degree w :=
    hG.degree_eq_of_not_adj hx_ne_w hnot_xw
  have hnot_vy : ¬ G.Adj v y :=
    hG.not_adj_of_adj_of_adj hadj.symm hwy
  have hnot_yv : ¬ G.Adj y v := by
    intro hyv
    exact hnot_vy hyv.symm
  have hy_deg : G.degree y = G.degree v :=
    hG.degree_eq_of_not_adj hy_ne_v hnot_yv
  have hxy_deg : G.degree x ≠ G.degree y := by
    intro hxy
    exact hdeg (hy_deg.symm.trans (hxy.symm.trans hx_deg))
  have hxy : G.Adj x y := hG.adj_of_degree_ne hxy_deg
  have hchosen_v :
      hG.commonNeighborOfNotAdj hx_ne_w hnot_xw = v := by
    exact hG.commonNeighborOfNotAdj_eq_of_common
      hx_ne_w hnot_xw ⟨hvx.symm, hadj.symm⟩
  have hchosen_y :
      hG.commonNeighborOfNotAdj hx_ne_w hnot_xw = y := by
    exact hG.commonNeighborOfNotAdj_eq_of_common
      hx_ne_w hnot_xw ⟨hxy, hwy⟩
  exact hy_ne_v (hchosen_y.symm.trans hchosen_v)

/-- If a degree-one leaf is adjacent to a vertex of different degree, then that
vertex is the center of a star. -/
theorem isStarWithCenter_of_adj_degree_one
    (hG : IsStrongZeroOne G) {leaf center : V}
    (hadj : G.Adj leaf center)
    (hleaf : G.degree leaf = 1)
    (hdeg : G.degree leaf ≠ G.degree center) :
    IsStarWithCenter G center := by
  have hunique : ∃! u : V, G.Adj leaf u :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hleaf
  have hleaf_neighbor_eq : ∀ u : V, G.Adj leaf u → u = center := by
    rcases hunique with ⟨u, hu, huniq⟩
    have hcenter_eq : center = u := huniq center hadj
    intro x hx
    exact (huniq x hx).trans hcenter_eq.symm
  have hcenter_adj : ∀ x : V, x ≠ center → G.Adj center x := by
    intro x hx_center
    by_cases hx_leaf : x = leaf
    · simpa [hx_leaf] using hadj.symm
    · have hleaf_ne_x : leaf ≠ x := by
        intro hlx
        exact hx_leaf hlx.symm
      have hnot_leaf_x : ¬ G.Adj leaf x := by
        intro hlx
        exact hx_center (hleaf_neighbor_eq x hlx)
      by_contra hnot_center_x
      have hleaf_x_deg : G.degree leaf = G.degree x :=
        hG.degree_eq_of_not_adj hleaf_ne_x hnot_leaf_x
      have hcenter_x_deg : G.degree center = G.degree x :=
        hG.degree_eq_of_not_adj hx_center.symm hnot_center_x
      exact hdeg (hleaf_x_deg.trans hcenter_x_deg.symm)
  intro v w
  constructor
  · intro hvw
    by_cases hv_center : v = center
    · left
      exact ⟨hv_center, fun hw_center => by
        subst v
        subst w
        exact (G.loopless.irrefl center hvw).elim⟩
    by_cases hw_center : w = center
    · right
      exact ⟨hw_center, hv_center⟩
    · have hcv : G.Adj center v := hcenter_adj v hv_center
      have hcw : G.Adj center w := hcenter_adj w hw_center
      exact False.elim
        (hG.not_commonNeighbor_of_adj hvw ⟨hcv.symm, hcw.symm⟩)
  · rintro (⟨hv_center, hw_ne_center⟩ | ⟨hw_center, hv_ne_center⟩)
    · subst v
      exact hcenter_adj w hw_ne_center
    · subst w
      exact (hcenter_adj v hv_ne_center).symm

/-- A degree gap in a strong `(0, 1)` graph forces the graph to be a star. -/
theorem exists_isStarWithCenter_of_degree_ne
    (hG : IsStrongZeroOne G) {v w : V}
    (hdeg : G.degree v ≠ G.degree w) :
    ∃ c : V, IsStarWithCenter G c := by
  have hadj : G.Adj v w := hG.adj_of_degree_ne hdeg
  rcases hG.degree_eq_one_or_degree_eq_one_of_adj_degree_ne hadj hdeg with
    hv_one | hw_one
  · exact ⟨w, hG.isStarWithCenter_of_adj_degree_one hadj hv_one hdeg⟩
  · have hdeg' : G.degree w ≠ G.degree v := by
      intro h
      exact hdeg h.symm
    exact ⟨v, hG.isStarWithCenter_of_adj_degree_one hadj.symm hw_one hdeg'⟩

omit [DecidableEq V] in
/-- A non-regular finite graph has two vertices with different degrees. -/
theorem exists_degree_ne_of_not_regular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnot : ¬ ∃ k : ℕ, ∀ v : V, G.degree v = k) :
    ∃ v w : V, G.degree v ≠ G.degree w := by
  classical
  by_contra hnone
  have hall : ∀ v w : V, G.degree v = G.degree w := by
    intro v w
    by_contra hneq
    exact hnone ⟨v, w, hneq⟩
  by_cases hnonempty : Nonempty V
  · rcases hnonempty with ⟨v₀⟩
    exact hnot ⟨G.degree v₀, fun v => hall v v₀⟩
  · exact hnot ⟨0, fun v => False.elim (hnonempty ⟨v⟩)⟩

/-- Main usable form of the Macaj-Siran Lemma 1 non-regular branch: a finite
strong `(λ, μ) = (0, 1)` graph that is not regular is a star. -/
theorem exists_isStarWithCenter_of_not_regular
    (hG : IsStrongZeroOne G)
    (hnot : ¬ ∃ k : ℕ, ∀ v : V, G.degree v = k) :
    ∃ c : V, IsStarWithCenter G c := by
  rcases exists_degree_ne_of_not_regular G hnot with ⟨v, w, hdeg⟩
  exact hG.exists_isStarWithCenter_of_degree_ne hdeg

end IsStrongZeroOne

end

end Moore57
