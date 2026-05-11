import Moore57.InvolutionFixedStarA1

/-!
# Involution edge-count formula

For an involutive automorphism `σ` of a Moore57 graph, counting the edges
between the fixed and moved vertices from both sides gives the geometric
formula for `a₁(σ)`.
-/

namespace Moore57

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The bipartite edge double-count between a finite set and its complement. -/
theorem fixed_moved_bipartite_count_symm
    (Fix : Finset V) :
    (∑ f ∈ Fix, ((Γ.neighborFinset f) \ Fix).card) =
      (∑ x ∈ (Finset.univ \ Fix), ((Γ.neighborFinset x) ∩ Fix).card) := by
  classical
  have hLHS :
      (∑ f ∈ Fix, ((Γ.neighborFinset f) \ Fix).card) =
        ∑ f ∈ Fix, ∑ x ∈ (Finset.univ \ Fix),
          (if Γ.Adj f x then (1 : ℕ) else 0) := by
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [show (Γ.neighborFinset f) \ Fix =
          (Finset.univ \ Fix).filter (Γ.Adj f) from ?_]
    · rw [Finset.card_filter]
    · ext y
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
        SimpleGraph.mem_neighborFinset, true_and]
      tauto
  have hRHS :
      (∑ x ∈ (Finset.univ \ Fix), ((Γ.neighborFinset x) ∩ Fix).card) =
        ∑ x ∈ (Finset.univ \ Fix), ∑ f ∈ Fix,
          (if Γ.Adj f x then (1 : ℕ) else 0) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [show (Γ.neighborFinset x) ∩ Fix =
          Fix.filter (Γ.Adj x) from ?_]
    · rw [Finset.card_filter]
      refine Finset.sum_congr rfl (fun f _ => ?_)
      simp [Γ.adj_comm]
    · ext y
      simp only [Finset.mem_inter, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset]
      tauto
  rw [hLHS, hRHS, Finset.sum_comm]

/-- If `x` is adjacent to its involutive image, then triangle-freeness forbids
fixed neighbors of `x`. -/
theorem no_fixed_neighbor_of_adjacent_image
    (hΓ : IsMoore57 Γ)
    {σ : Equiv.Perm V}
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {x : V} (hAdj : Γ.Adj x (σ x)) :
    (Γ.neighborFinset x ∩ fixedFinset σ) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro y hy
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, mem_fixedFinset] at hy
  obtain ⟨hxy, hyFix⟩ := hy
  have hyσx : Γ.Adj y (σ x) := by
    have h1 : Γ.Adj (σ y) (σ x) := (haut y x).mp hxy.symm
    rw [hyFix] at h1
    exact h1
  exact hΓ.no_triangle hAdj hyσx.symm hxy.symm

/-- If a non-fixed `x` is not adjacent to its involutive image, then its unique
common neighbor with `σ x` is fixed. -/
theorem one_fixed_neighbor_of_nonadjacent_image
    (hΓ : IsMoore57 Γ)
    {σ : Equiv.Perm V}
    (hinv : Function.Involutive σ)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {x : V} (hxNotFix : x ∉ fixedFinset σ)
    (hNotAdj : ¬ Γ.Adj x (σ x)) :
    (Γ.neighborFinset x ∩ fixedFinset σ).card = 1 := by
  classical
  have hxne : x ≠ σ x := by
    rw [mem_fixedFinset] at hxNotFix
    exact fun h => hxNotFix h.symm
  have hcommon : Fintype.card (Γ.commonNeighbors x (σ x)) = 1 :=
    hΓ.of_not_adj hxne hNotAdj
  let CN : Finset V := (Γ.commonNeighbors x (σ x)).toFinset
  have hCN_card : CN.card = 1 := by
    simp [CN, Set.toFinset_card, hcommon]
  have hCN_σ : ∀ y ∈ CN, σ y ∈ CN := by
    intro y hy
    simp only [CN, Set.mem_toFinset, SimpleGraph.mem_commonNeighbors] at hy ⊢
    refine ⟨?_, ?_⟩
    · have h1 : Γ.Adj (σ (σ x)) (σ y) := (haut (σ x) y).mp hy.2
      rw [hinv x] at h1
      exact h1
    · exact (haut x y).mp hy.1
  obtain ⟨y, hCN_y⟩ := Finset.card_eq_one.mp hCN_card
  have hy_in_CN : y ∈ CN := by rw [hCN_y]; exact Finset.mem_singleton_self y
  have hyFix : σ y = y := by
    have hσy_in : σ y ∈ CN := hCN_σ y hy_in_CN
    rw [hCN_y, Finset.mem_singleton] at hσy_in
    exact hσy_in
  have hy_xy : Γ.Adj x y ∧ Γ.Adj (σ x) y := by
    have := hy_in_CN
    simp only [CN, Set.mem_toFinset, SimpleGraph.mem_commonNeighbors] at this
    exact this
  have hsetEq : Γ.neighborFinset x ∩ fixedFinset σ = {y} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, mem_fixedFinset]
      exact ⟨hy_xy.1, hyFix⟩
    · intro z hz
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, mem_fixedFinset] at hz
      obtain ⟨hxz, hzFix⟩ := hz
      have hzσx : Γ.Adj z (σ x) := by
        have h1 : Γ.Adj (σ z) (σ x) := (haut z x).mp hxz.symm
        rw [hzFix] at h1
        exact h1
      have hz_in_CN : z ∈ CN := by
        simp only [CN, Set.mem_toFinset, SimpleGraph.mem_commonNeighbors]
        exact ⟨hxz, hzσx.symm⟩
      rw [hCN_y, Finset.mem_singleton] at hz_in_CN
      exact hz_in_CN
  rw [hsetEq, Finset.card_singleton]

/-- Degree in the fixed induced graph is the number of ambient fixed neighbors. -/
theorem fixed_induced_degree_eq_neighbor_inter_card
    (σ : Equiv.Perm V) (x : fixedVertexSet σ) :
    (Γ.induce (fixedVertexSet σ)).degree x =
      ((Γ.neighborFinset (x : V)) ∩ fixedFinset σ).card := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  have hsubtypeCard :
      Fintype.card ((Γ.induce (fixedVertexSet σ)).neighborSet x) =
        Fintype.card
          {w : V // w ∈ (Γ.neighborFinset (x : V)) ∩ fixedFinset σ} := by
    refine Fintype.card_congr ?neighborEquiv
    exact
      { toFun := fun y =>
          ⟨y.1.1, by
            have hyAdj : Γ.Adj (x : V) y.1.1 := by
              have hyAdjSub : (Γ.induce (fixedVertexSet σ)).Adj x y.1 :=
                (SimpleGraph.mem_neighborSet (G := Γ.induce (fixedVertexSet σ))
                  (v := x) (w := y.1)).1 y.property
              simpa using hyAdjSub
            have hyFixed : σ y.1.1 = y.1.1 := y.1.property
            simp [SimpleGraph.mem_neighborFinset, hyAdj, hyFixed]⟩
        invFun := fun y =>
          ⟨⟨(y : V), by
              exact (mem_fixedFinset σ (y : V)).mp
                (Finset.mem_inter.mp y.property).2⟩, by
            have hyAdj : Γ.Adj (x : V) (y : V) := by
              exact (SimpleGraph.mem_neighborFinset (G := Γ)
                (v := (x : V)) (w := (y : V))).1
                  (Finset.mem_inter.mp y.property).1
            have hyAdjSub :
                (Γ.induce (fixedVertexSet σ)).Adj x
                  ⟨(y : V), (mem_fixedFinset σ (y : V)).mp
                    (Finset.mem_inter.mp y.property).2⟩ := by
              simpa using hyAdj
            exact (SimpleGraph.mem_neighborSet (G := Γ.induce (fixedVertexSet σ))
              (v := x) (w := ⟨(y : V), (mem_fixedFinset σ (y : V)).mp
                (Finset.mem_inter.mp y.property).2⟩)).2
                hyAdjSub⟩
        left_inv := by
          intro y
          ext
          rfl
        right_inv := by
          intro y
          ext
          rfl }
  have hfinsetCard :
      Fintype.card
          {w : V // w ∈ (Γ.neighborFinset (x : V)) ∩ fixedFinset σ} =
        ((Γ.neighborFinset (x : V)) ∩ fixedFinset σ).card := by
    exact Fintype.card_ofFinset
      ((Γ.neighborFinset (x : V)) ∩ fixedFinset σ) (by intro w; rfl)
  exact hsubtypeCard.trans hfinsetCard

/-- The sum of ambient fixed-neighbor counts over fixed vertices is twice the
number of edges in the fixed induced graph. -/
theorem fixed_neighbor_sum_eq_twice_fixed_induced_edges
    (σ : Equiv.Perm V) :
    (∑ f ∈ fixedFinset σ, ((Γ.neighborFinset f) ∩ fixedFinset σ).card) =
      2 * (Γ.induce (fixedVertexSet σ)).edgeFinset.card := by
  classical
  calc
    (∑ f ∈ fixedFinset σ, ((Γ.neighborFinset f) ∩ fixedFinset σ).card)
        = ∑ x : fixedVertexSet σ,
            ((Γ.neighborFinset (x : V)) ∩ fixedFinset σ).card := by
          simpa [fixedVertexSet] using
            (Finset.sum_subtype
              (s := fixedFinset σ)
              (h := by intro x; simp [fixedFinset, fixedVertexSet])
              (f := fun f => ((Γ.neighborFinset f) ∩ fixedFinset σ).card))
    _ = ∑ x : fixedVertexSet σ,
          (Γ.induce (fixedVertexSet σ)).degree x := by
          simp [fixed_induced_degree_eq_neighbor_inter_card]
    _ = 2 * (Γ.induce (fixedVertexSet σ)).edgeFinset.card := by
          exact SimpleGraph.sum_degrees_eq_twice_card_edges
            (Γ.induce (fixedVertexSet σ))

/-- Counting fixed-to-moved edges from the fixed side gives
`57 * #Fix - 2 * #E(Fix)`. -/
theorem fixed_to_moved_edge_count_eq
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) :
    (∑ f ∈ fixedFinset σ, ((Γ.neighborFinset f) \ fixedFinset σ).card) =
      57 * fixedVertexCount σ -
        2 * (Γ.induce (fixedVertexSet σ)).edgeFinset.card := by
  classical
  have hper :
      ∀ f ∈ fixedFinset σ,
        ((Γ.neighborFinset f) \ fixedFinset σ).card +
            ((Γ.neighborFinset f) ∩ fixedFinset σ).card = 57 := by
    intro f _hf
    have hcard := Finset.card_sdiff_add_card_inter
      (Γ.neighborFinset f) (fixedFinset σ)
    rw [SimpleGraph.card_neighborFinset_eq_degree, hΓ.regular.degree_eq f]
      at hcard
    exact hcard
  have hsum_add :
      (∑ f ∈ fixedFinset σ,
          ((Γ.neighborFinset f) \ fixedFinset σ).card) +
        (∑ f ∈ fixedFinset σ,
          ((Γ.neighborFinset f) ∩ fixedFinset σ).card) =
        ∑ f ∈ fixedFinset σ, 57 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hper
  have hfixedNeighbor :
      (∑ f ∈ fixedFinset σ,
          ((Γ.neighborFinset f) ∩ fixedFinset σ).card) =
        2 * (Γ.induce (fixedVertexSet σ)).edgeFinset.card :=
    fixed_neighbor_sum_eq_twice_fixed_induced_edges (Γ := Γ) σ
  have hconst :
      (∑ f ∈ fixedFinset σ, 57) = 57 * fixedVertexCount σ := by
    simp [fixedFinset_card, Nat.mul_comm]
  omega

/-- Counting fixed-to-moved edges from the moved side gives the number of
non-fixed vertices not adjacent to their image. -/
theorem moved_to_fixed_edge_count_eq_nonadjacent
    (hΓ : IsMoore57 Γ)
    {σ : Equiv.Perm V}
    (hinv : Function.Involutive σ)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    (∑ x ∈ (Finset.univ \ fixedFinset σ),
        ((Γ.neighborFinset x) ∩ fixedFinset σ).card) =
      ((Finset.univ \ fixedFinset σ).filter
        fun x => ¬ Γ.Adj x (σ x)).card := by
  classical
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
  by_cases hAdj : Γ.Adj x (σ x)
  · rw [if_neg (not_not_intro hAdj)]
    have hzero : (Γ.neighborFinset x ∩ fixedFinset σ) = ∅ :=
      no_fixed_neighbor_of_adjacent_image hΓ haut hAdj
    simp [hzero]
  · rw [if_pos hAdj]
    exact one_fixed_neighbor_of_nonadjacent_image hΓ hinv haut hx hAdj

/-- Geometric formula for `a₁(σ)` for an involutive automorphism of a Moore57
graph. -/
theorem adjacentMovedCount_eq_involution_fixed_edge_formula
    (hΓ : IsMoore57 Γ)
    {σ : Equiv.Perm V}
    (hinv : Function.Involutive σ)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    (adjacentMovedCount Γ σ : ℤ) =
      3250 - 58 * (fixedVertexCount σ : ℤ) +
        2 * (((Γ.induce (fixedVertexSet σ)).edgeFinset.card : ℤ)) := by
  classical
  let Fix := fixedFinset σ
  let M : Finset V := Finset.univ \ Fix
  let eFix := (Γ.induce (fixedVertexSet σ)).edgeFinset.card
  have hbip :
      (∑ f ∈ Fix, ((Γ.neighborFinset f) \ Fix).card) =
        (∑ x ∈ M, ((Γ.neighborFinset x) ∩ Fix).card) := by
    simpa [Fix, M] using fixed_moved_bipartite_count_symm (Γ := Γ) (fixedFinset σ)
  have hfixedSide :
      (∑ f ∈ Fix, ((Γ.neighborFinset f) \ Fix).card) =
        57 * fixedVertexCount σ - 2 * eFix := by
    simpa [Fix, eFix] using fixed_to_moved_edge_count_eq (Γ := Γ) hΓ σ
  have hmovedSide :
      (∑ x ∈ M, ((Γ.neighborFinset x) ∩ Fix).card) =
        (M.filter fun x => ¬ Γ.Adj x (σ x)).card := by
    simpa [Fix, M] using
      moved_to_fixed_edge_count_eq_nonadjacent (Γ := Γ) hΓ hinv haut
  have hnonadj_eq :
      (M.filter fun x => ¬ Γ.Adj x (σ x)).card =
        57 * fixedVertexCount σ - 2 * eFix := by
    rw [← hmovedSide, ← hbip, hfixedSide]
  have hadj_set :
      (M.filter fun x => Γ.Adj x (σ x)) =
        (Finset.univ : Finset V).filter fun x => Γ.Adj x (σ x) := by
    apply Finset.ext
    intro x
    simp only [M, Fix, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      true_and, mem_fixedFinset]
    refine ⟨fun h => h.2, fun hAdj => ⟨?_, hAdj⟩⟩
    intro hfix
    exact hAdj.ne hfix.symm
  have hadj :
      adjacentMovedCount Γ σ =
        (M.filter fun x => Γ.Adj x (σ x)).card := by
    unfold adjacentMovedCount
    rw [hadj_set]
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := M) (p := fun x => Γ.Adj x (σ x))
  have hFix_le : fixedVertexCount σ ≤ 3250 := by
    have hle : (fixedFinset σ).card ≤ Fintype.card V := Finset.card_le_univ _
    simpa [fixedFinset_card, hΓ.card] using hle
  have hM_card : M.card = 3250 - fixedVertexCount σ := by
    dsimp [M, Fix]
    rw [show (Finset.univ \ fixedFinset σ : Finset V) =
        (fixedFinset σ)ᶜ from
          (Finset.compl_eq_univ_sdiff (fixedFinset σ)).symm,
      Finset.card_compl, hΓ.card, fixedFinset_card]
  have hsum_nat :
      adjacentMovedCount Γ σ + (57 * fixedVertexCount σ - 2 * eFix) =
        3250 - fixedVertexCount σ := by
    rw [← hM_card]
    rw [hadj]
    omega
  have hdegreeSum :
      (∑ f ∈ Fix, ((Γ.neighborFinset f) ∩ Fix).card) = 2 * eFix := by
    simpa [Fix, eFix] using fixed_neighbor_sum_eq_twice_fixed_induced_edges
      (Γ := Γ) σ
  have hfixedNeighbor_le :
      (∑ f ∈ Fix, ((Γ.neighborFinset f) ∩ Fix).card) ≤
        ∑ f ∈ Fix, 57 := by
    refine Finset.sum_le_sum (fun f _hf => ?_)
    have hsub : (Γ.neighborFinset f) ∩ Fix ⊆ Γ.neighborFinset f := by
      intro y hy
      exact (Finset.mem_inter.mp hy).1
    have hcard_le :
        ((Γ.neighborFinset f) ∩ Fix).card ≤ (Γ.neighborFinset f).card :=
      Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree, hΓ.regular.degree_eq f] at hcard_le
    exact hcard_le
  have hedge_le : 2 * eFix ≤ 57 * fixedVertexCount σ := by
    rw [← hdegreeSum]
    have hconst : (∑ f ∈ Fix, 57) = 57 * fixedVertexCount σ := by
      simp [Fix, fixedFinset_card]
      omega
    simpa [hconst] using hfixedNeighbor_le
  have hfixedSide_int :
      ((57 * fixedVertexCount σ - 2 * eFix : ℕ) : ℤ) =
        57 * (fixedVertexCount σ : ℤ) - 2 * (eFix : ℤ) := by
    rw [Int.ofNat_sub hedge_le]
    norm_num
  have hM_int :
      ((3250 - fixedVertexCount σ : ℕ) : ℤ) =
        3250 - (fixedVertexCount σ : ℤ) := by
    rw [Int.ofNat_sub hFix_le]
    norm_num
  have hsum_int :
      (adjacentMovedCount Γ σ : ℤ) +
          (57 * (fixedVertexCount σ : ℤ) - 2 * (eFix : ℤ)) =
        3250 - (fixedVertexCount σ : ℤ) := by
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) hsum_nat
    simpa [Nat.cast_add, hfixedSide_int, hM_int] using hcast
  linarith

omit [DecidableEq V] in
/-- A Moore57 graph has `92625` edges. -/
theorem edgeFinset_card_eq_92625
    (hΓ : IsMoore57 Γ) :
    Γ.edgeFinset.card = 92625 := by
  have hsum : ∑ v : V, Γ.degree v = 2 * Γ.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges Γ
  have hsum57 : ∑ v : V, Γ.degree v = 3250 * 57 := by
    calc
      ∑ v : V, Γ.degree v = ∑ _v : V, 57 := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        exact hΓ.regular.degree_eq v
      _ = 3250 * 57 := by
        simp [hΓ.card]
  omega

end

end Moore57
