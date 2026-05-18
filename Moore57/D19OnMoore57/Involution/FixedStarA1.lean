import Moore57.D19OnMoore57.LinearCharacter.Dimension

/-!
# Involution `a₁` count from a `K_{1,55}` fixed star

Natural-language proof Lemma 9.3 derives `a₁(t) = 112` for any involutive
automorphism `σ` of the (hypothetical) Moore graph of degree `57` whose fixed
set has the shape of a `K_{1,55}` star.

We capture the degree input as a single bipartite-edge count:

  ∑_{f ∈ Fix} |N(f) \ Fix| = 3082

(which equals `2 + 55·56` for the `K_{1,55}` shape).  Combined with
`Moore57` regularity / triangle-freeness / `μ = 1` and the involutive
`σ`-symmetry, this forces `a₁(σ) = 112` as a theorem.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The Finset of fixed vertices of `σ`. -/
def fixedFinset (σ : Equiv.Perm V) : Finset V :=
  (Finset.univ : Finset V).filter fun v => σ v = v

@[simp] theorem mem_fixedFinset (σ : Equiv.Perm V) (v : V) :
    v ∈ fixedFinset σ ↔ σ v = v := by
  simp [fixedFinset]

@[simp] theorem fixedFinset_card (σ : Equiv.Perm V) :
    (fixedFinset σ).card = fixedVertexCount σ :=
  rfl

/-- The bipartite edge double-count: counting `Fix`-to-`Fixᶜ` edges from each
side gives the same total. -/
private theorem bipartite_count_symm
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

/-- A `K_{1,55}` fixed-star structure for an involutive automorphism `σ`. -/
structure InvolutionFixedStar55
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (σ : Equiv.Perm V) : Prop where
  /-- `σ` is an involution. -/
  involutive : Function.Involutive σ
  /-- `σ` is a graph automorphism. -/
  automorphism : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)
  /-- `σ` has exactly `56` fixed vertices. -/
  fixed_card : (fixedFinset σ).card = 56
  /-- The `K_{1,55}` shape: the bipartite edge count from `Fix` is `3082`. -/
  bipartite_edges :
    (∑ f ∈ fixedFinset σ, ((Γ.neighborFinset f) \ fixedFinset σ).card) = 3082

namespace InvolutionFixedStar55

/-- For a non-fixed vertex `x` adjacent to `σ x`, no fixed vertex is adjacent
to `x`: triangle-freeness blocks it. -/
private theorem no_fixed_neighbor_of_adj
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

/-- For a non-fixed `x` not adjacent to `σ x`, exactly one fixed vertex is
adjacent to `x`: the unique common neighbor of `x` and `σ x`. -/
private theorem one_fixed_neighbor_of_not_adj
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
  -- Show `Γ.neighborFinset x ∩ fixedFinset σ = {y}`.
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

/-- Main theorem: an involutive automorphism `σ` of `Moore57` with a `K_{1,55}`
fixed star satisfies `adjacentMovedCount Γ σ = 112`. -/
theorem adjacentMovedCount_eq_112
    (hΓ : IsMoore57 Γ)
    {σ : Equiv.Perm V}
    (hStar : InvolutionFixedStar55 Γ σ) :
    adjacentMovedCount Γ σ = 112 := by
  classical
  have hbip := bipartite_count_symm (Γ := Γ) (fixedFinset σ)
  rw [hStar.bipartite_edges] at hbip
  have hRHS_eq :
      (∑ x ∈ (Finset.univ \ fixedFinset σ),
          ((Γ.neighborFinset x) ∩ fixedFinset σ).card) =
        ((Finset.univ \ fixedFinset σ).filter
            fun x => ¬ Γ.Adj x (σ x)).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
    by_cases hAdj : Γ.Adj x (σ x)
    · rw [if_neg (not_not_intro hAdj)]
      have hzero : (Γ.neighborFinset x ∩ fixedFinset σ) = ∅ :=
        no_fixed_neighbor_of_adj hΓ hStar.automorphism hAdj
      simp [hzero]
    · rw [if_pos hAdj]
      exact one_fixed_neighbor_of_not_adj hΓ hStar.involutive
        hStar.automorphism hx hAdj
  rw [hRHS_eq] at hbip
  -- Split |V \ Fix| = #adj + #non-adj.
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ \ fixedFinset σ : Finset V))
      (p := fun x => Γ.Adj x (σ x))
  -- |V \ Fix| = card V - 56 = 3194.
  have hcompl_card : (Finset.univ \ fixedFinset σ : Finset V).card = 3194 := by
    rw [show (Finset.univ \ fixedFinset σ : Finset V) = (fixedFinset σ)ᶜ from
        (Finset.compl_eq_univ_sdiff (fixedFinset σ)).symm,
      Finset.card_compl, hΓ.card, hStar.fixed_card]
  -- adjacent-moved set: restrict from univ to V \ Fix.
  have hadj_set :
      ((Finset.univ \ fixedFinset σ).filter fun x => Γ.Adj x (σ x)) =
        (Finset.univ : Finset V).filter fun x => Γ.Adj x (σ x) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      mem_fixedFinset]
    refine ⟨fun ⟨_, hAdj⟩ => hAdj, fun hAdj => ⟨?_, hAdj⟩⟩
    intro hfix
    exact hAdj.ne hfix.symm
  have ha1 : adjacentMovedCount Γ σ =
      ((Finset.univ \ fixedFinset σ).filter fun x => Γ.Adj x (σ x)).card := by
    unfold adjacentMovedCount
    rw [hadj_set]
  rw [ha1]
  omega

end InvolutionFixedStar55

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- For any reflection index `d`, an `InvolutionFixedStar55` witness for the
involution `h.smulEquiv (DihedralGroup.sr d)` gives the standard reflection
`a₁` value `112`. -/
theorem adjacentMovedCount_reflection_eq_112
    {d : ZMod 19}
    (hStar : InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr d))) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112 :=
  InvolutionFixedStar55.adjacentMovedCount_eq_112 h.isMoore hStar

/-- The same `InvolutionFixedStar55` witness records the reflection `a₀` value
`56` directly. -/
theorem fixedVertexCount_reflection_eq_56_of_involutionFixedStar55
    {d : ZMod 19}
    (hStar : InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr d))) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56 :=
  hStar.fixed_card

namespace D19LinearCharacterInput

/-- Build `D19LinearCharacterInput` from the linear-character equality, the
`(-8)`-eigenspace bounds, and an `InvolutionFixedStar55` witness for some
reflection: the standard reflection counts `a₀(t) = 56` and `a₁(t) = 112` are
both supplied by the fixed-star data. -/
noncomputable def ofLinearCharacterAndFixedStar55
    (alpha beta gamma : ℕ)
    (hAlpha : alpha ≤ 113)
    (hBeta : beta ≤ 58)
    (hlin : ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ))
    {d : ZMod 19}
    (hStar : InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr d))) :
    D19LinearCharacterInput h :=
  ofLinearCharacterAndCounts (h := h) alpha beta gamma hAlpha hBeta hlin
    (h.fixedVertexCount_reflection_eq_56_of_involutionFixedStar55 hStar)
    (h.adjacentMovedCount_reflection_eq_112 hStar)

end D19LinearCharacterInput

end D19ActsOnMoore57

/-- An explicit `K_{1,55}` star description for the fixed set of an involutive
automorphism `σ`: a center plus 55 leaves with the canonical adjacency
pattern. -/
structure InvolutionK155
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (σ : Equiv.Perm V) where
  involutive : Function.Involutive σ
  automorphism : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)
  center : V
  leaves : Finset V
  center_notMem : center ∉ leaves
  leaves_card : leaves.card = 55
  fixed_iff : ∀ v, σ v = v ↔ v = center ∨ v ∈ leaves
  center_adj_leaves : ∀ l ∈ leaves, Γ.Adj center l
  leaves_pairwise_not_adj :
    ∀ ⦃l₁⦄, l₁ ∈ leaves → ∀ ⦃l₂⦄, l₂ ∈ leaves → ¬ Γ.Adj l₁ l₂

namespace InvolutionK155

variable {σ : Equiv.Perm V}

private theorem fixedFinset_eq (hK : InvolutionK155 Γ σ) :
    fixedFinset σ = insert hK.center hK.leaves := by
  ext v
  simp only [mem_fixedFinset, Finset.mem_insert]
  exact hK.fixed_iff v

private theorem fixedFinset_card_eq_56 (hK : InvolutionK155 Γ σ) :
    (fixedFinset σ).card = 56 := by
  rw [hK.fixedFinset_eq, Finset.card_insert_of_notMem hK.center_notMem,
    hK.leaves_card]

/-- The neighborhood of the center inside the fixed set is exactly the leaves. -/
private theorem center_neighbors_inter_fixed
    (hK : InvolutionK155 Γ σ) :
    (Γ.neighborFinset hK.center) ∩ fixedFinset σ = hK.leaves := by
  ext v
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    hK.fixedFinset_eq, Finset.mem_insert]
  constructor
  · rintro ⟨hAdj, h | h⟩
    · exact (Γ.loopless.irrefl (a := hK.center) (h ▸ hAdj)).elim
    · exact h
  · intro hv
    exact ⟨hK.center_adj_leaves v hv, Or.inr hv⟩

/-- The neighborhood of a leaf inside the fixed set is exactly the center. -/
private theorem leaf_neighbors_inter_fixed
    (hK : InvolutionK155 Γ σ) {l : V} (hl : l ∈ hK.leaves) :
    (Γ.neighborFinset l) ∩ fixedFinset σ = {hK.center} := by
  ext v
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    hK.fixedFinset_eq, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hAdj, hcase | hcase⟩
    · exact hcase
    · exact (hK.leaves_pairwise_not_adj hl hcase hAdj).elim
  · rintro rfl
    exact ⟨(hK.center_adj_leaves l hl).symm, Or.inl rfl⟩

private theorem center_bipartite_edges
    (hΓ : IsMoore57 Γ) (hK : InvolutionK155 Γ σ) :
    ((Γ.neighborFinset hK.center) \ fixedFinset σ).card = 2 := by
  classical
  have hdeg : (Γ.neighborFinset hK.center).card = 57 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hΓ.regular.degree_eq]
  have hinter : ((Γ.neighborFinset hK.center) ∩ fixedFinset σ).card = 55 := by
    rw [hK.center_neighbors_inter_fixed, hK.leaves_card]
  have hsum := Finset.card_sdiff_add_card_inter
    (Γ.neighborFinset hK.center) (fixedFinset σ)
  omega

private theorem leaf_bipartite_edges
    (hΓ : IsMoore57 Γ) (hK : InvolutionK155 Γ σ) {l : V} (hl : l ∈ hK.leaves) :
    ((Γ.neighborFinset l) \ fixedFinset σ).card = 56 := by
  classical
  have hdeg : (Γ.neighborFinset l).card = 57 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hΓ.regular.degree_eq]
  have hinter : ((Γ.neighborFinset l) ∩ fixedFinset σ).card = 1 := by
    rw [hK.leaf_neighbors_inter_fixed hl, Finset.card_singleton]
  have hsum := Finset.card_sdiff_add_card_inter
    (Γ.neighborFinset l) (fixedFinset σ)
  omega

/-- The bipartite edge count from a `K_{1,55}` star is `2 + 55·56 = 3082`. -/
private theorem bipartite_edges_eq_3082
    (hΓ : IsMoore57 Γ) (hK : InvolutionK155 Γ σ) :
    (∑ f ∈ fixedFinset σ, ((Γ.neighborFinset f) \ fixedFinset σ).card) =
      3082 := by
  classical
  -- Per-vertex contributions: 2 at the center, 56 at each leaf.
  have hPerVertex : ∀ f ∈ fixedFinset σ,
      ((Γ.neighborFinset f) \ fixedFinset σ).card =
        (if f = hK.center then 2 else 56) := by
    intro f hf
    rw [mem_fixedFinset] at hf
    rcases (hK.fixed_iff f).mp hf with rfl | hfLeaf
    · simp [hK.center_bipartite_edges hΓ]
    · have hne : f ≠ hK.center := fun heq => hK.center_notMem (heq ▸ hfLeaf)
      simp [hne, hK.leaf_bipartite_edges hΓ hfLeaf]
  rw [Finset.sum_congr rfl hPerVertex]
  -- Σ over (insert center leaves) of (if · = center then 2 else 56) = 2 + 55·56.
  rw [hK.fixedFinset_eq, Finset.sum_insert hK.center_notMem]
  rw [if_pos rfl]
  have hLeavesConst : ∀ l ∈ hK.leaves,
      (if l = hK.center then (2 : ℕ) else 56) = 56 := by
    intro l hl
    have : l ≠ hK.center := fun heq => hK.center_notMem (heq ▸ hl)
    simp [this]
  rw [Finset.sum_congr rfl hLeavesConst, Finset.sum_const, hK.leaves_card]
  ring

/-- An explicit `K_{1,55}` star yields the bipartite-count abstraction
`InvolutionFixedStar55`. -/
theorem toInvolutionFixedStar55
    (hΓ : IsMoore57 Γ) (hK : InvolutionK155 Γ σ) :
    InvolutionFixedStar55 Γ σ where
  involutive := hK.involutive
  automorphism := hK.automorphism
  fixed_card := hK.fixedFinset_card_eq_56
  bipartite_edges := hK.bipartite_edges_eq_3082 hΓ

set_option linter.unusedDecidableInType false in
/-- An explicit `K_{1,55}` star directly gives `a₁(σ) = 112`. -/
theorem adjacentMovedCount_eq_112
    (hΓ : IsMoore57 Γ) (hK : InvolutionK155 Γ σ) :
    adjacentMovedCount Γ σ = 112 :=
  (hK.toInvolutionFixedStar55 hΓ).adjacentMovedCount_eq_112 hΓ

end InvolutionK155

end Moore57
