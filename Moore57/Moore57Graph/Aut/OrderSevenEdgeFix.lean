import Moore57.Moore57Graph.Aut.OrderSevenCandidates
import Moore57.Moore57Graph.Aut.SingletonAndEmptyFixedData

/-!
# Edge-shape fixed subgraph data + Order-7 constructor

Paper reference: Mačaj–Širáň 2010, §6, Lemma 16 case (3).

> Let `X` be a `7`-group of automorphisms of Γ with case (3) shape
> `Fix(X) = K_{1,1} = K_2` (an edge).

This file:

1. Defines `EdgeFixedData Γ σ` — the analog of `SingletonFixedData` and
   `K155FixedData` for an order-7 edge-fix shape: two distinct adjacent
   σ-fixed vertices, spanning all of `Fix(σ)`.

2. Provides constructors:
   * `edgeFixedData_of_fixedVertexCount_eq_two` — generic constructor
     from `|Fix(σ)| = 2` plus mod-7 fix-neighbour constraint
     (yields adjacency of the two fixed vertices).
   * `aut_order_seven_EdgeFixedData_of_small_fix` — order-7 specialisation:
     given `|Fix(σ)| ≤ 8` (and `σ^7 = 1`), the mod-7 congruence forces
     `|Fix(σ)| = 2`, and the constructor applies.

## Status: conditional on small-fix bound

Unlike `aut_order_eleven_C5FixedData` (which is fully unconditional) or
`aut_order_thirteen_EmptyFixedData_unconditional` (also fully unconditional),
the 7-prime case **cannot** be fully discharged from `σ^7 = 1, σ ≠ 1`
alone: the surviving local candidates include both `K_{1, 1+7l}` stars of
various sizes (`l ≥ 0`) and the regular `k=7` case (Hoffman-Singleton, 50
vertices).  The Lemma 16 case 3 pin to `l = 0` (size 2) needs external
input — typically the upstream "|X| ∣ 49 forces Fix-size ≤ 8" argument.

Hence the constructor `aut_order_seven_EdgeFixedData_of_small_fix`
provides the data-packaging step **conditional on** `|Fix(σ)| ≤ 8`.

## Design parallel

| File                              | Output            | Status                        |
|-----------------------------------|-------------------|-------------------------------|
| `OrderElevenIsC5.lean`            | `C5FixedData`     | unconditional                 |
| `OrderThirteenEmptyFix.lean`      | `EmptyFixedData`  | both forms exposed            |
| `OrderNineteenSingletonFix.lean`  | `SingletonFixedData` | unconditional             |
| `OrderSevenEdgeFix.lean` (this)   | `EdgeFixedData`   | small-fix conditional         |

-/

namespace Moore57

variable {V : Type*}

/-! ## Edge fixed subgraph data -/

/-- The σ-fixed subgraph of `Γ` is a single edge `K_2 = K_{1,1}`:
two distinct adjacent σ-fixed vertices, with no other σ-fixed vertices.

Fields:
* `v₀, v₁ : V` — the two endpoints of the edge.
* `v_ne` — the endpoints are distinct.
* `v₀_fixed, v₁_fixed` — σ fixes both endpoints.
* `adj` — the two endpoints are Γ-adjacent (the edge itself).
* `span` — σ has no other fixed points.

This is the §6 Lemma 16 case (3) input: `Fix(σ) = {v₀, v₁}` with
`Γ.Adj v₀ v₁`. -/
structure EdgeFixedData (Γ : SimpleGraph V) (σ : Equiv.Perm V) where
  /-- First endpoint of the edge. -/
  v₀ : V
  /-- Second endpoint of the edge. -/
  v₁ : V
  /-- The two endpoints are distinct. -/
  v_ne : v₀ ≠ v₁
  /-- σ fixes the first endpoint. -/
  v₀_fixed : σ v₀ = v₀
  /-- σ fixes the second endpoint. -/
  v₁_fixed : σ v₁ = v₁
  /-- The two endpoints are Γ-adjacent. -/
  adj : Γ.Adj v₀ v₁
  /-- σ has no fixed points outside `{v₀, v₁}`. -/
  span : ∀ x : V, σ x = x → x = v₀ ∨ x = v₁

namespace EdgeFixedData

variable {Γ : SimpleGraph V} {σ : Equiv.Perm V}

/-- **Edge `fixedVertexCount = 2`.** [done]

The σ-fixed-vertex count equals `2` (the two endpoints). -/
theorem fixedVertexCount_eq_two
    [Fintype V] [DecidableEq V] (h : EdgeFixedData Γ σ) :
    fixedVertexCount σ = 2 := by
  classical
  unfold fixedVertexCount
  have heq :
      ((Finset.univ : Finset V).filter (fun w => σ w = w))
        = {h.v₀, h.v₁} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
               Finset.mem_singleton]
    constructor
    · intro hfix
      exact h.span w hfix
    · rintro (rfl | rfl)
      · exact h.v₀_fixed
      · exact h.v₁_fixed
  rw [heq]
  rw [Finset.card_insert_of_notMem (by simp [h.v_ne]), Finset.card_singleton]

/-- **Edge bridge to `autFixedNeighborFinset` (first endpoint).** [done]

At `v₀`, the σ-fixed neighbour count equals `1` (just `v₁`).  Mirrors
`SingletonFixedData.autFixedNeighborFinset_card_eq_zero` and
`K155FixedData.autFixedNeighborFinset_card_leaf_eq_one`. -/
theorem autFixedNeighborFinset_card_v0_eq_one
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (h : EdgeFixedData Γ σ) :
    (autFixedNeighborFinset Γ σ h.v₀).card = 1 := by
  classical
  have heq :
      autFixedNeighborFinset Γ σ h.v₀ = {h.v₁} := by
    ext w
    simp only [mem_autFixedNeighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hadj, hfix⟩
      rcases h.span w hfix with rfl | rfl
      · exact absurd hadj (SimpleGraph.irrefl Γ)
      · rfl
    · rintro rfl
      exact ⟨h.adj, h.v₁_fixed⟩
  rw [heq, Finset.card_singleton]

/-- **Edge bridge to `autFixedNeighborFinset` (second endpoint).** [done]

At `v₁`, the σ-fixed neighbour count equals `1` (just `v₀`). -/
theorem autFixedNeighborFinset_card_v1_eq_one
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (h : EdgeFixedData Γ σ) :
    (autFixedNeighborFinset Γ σ h.v₁).card = 1 := by
  classical
  have heq :
      autFixedNeighborFinset Γ σ h.v₁ = {h.v₀} := by
    ext w
    simp only [mem_autFixedNeighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hadj, hfix⟩
      rcases h.span w hfix with rfl | rfl
      · rfl
      · exact absurd hadj (SimpleGraph.irrefl Γ)
    · rintro rfl
      exact ⟨h.adj.symm, h.v₀_fixed⟩
  rw [heq, Finset.card_singleton]

/-- **Edge complement neighbour count (`v₀`).** [done]

At the first endpoint, `|N(v₀) \ Fix(σ)| = 56 = 57 − 1`. -/
theorem edgeFixedData_complement_v0_count
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (h : EdgeFixedData Γ σ) :
    ((Γ.neighborFinset h.v₀).filter (fun w => σ w ≠ w)).card = 56 := by
  have h57 : (Γ.neighborFinset h.v₀).card = 57 := by
    have := hΓ.regular.degree_eq h.v₀
    rwa [SimpleGraph.degree] at this
  have h1 : ((Γ.neighborFinset h.v₀).filter (fun w => σ w = w)).card = 1 :=
    h.autFixedNeighborFinset_card_v0_eq_one
  have hsum := Finset.card_filter_add_card_filter_not (s := Γ.neighborFinset h.v₀)
    (p := fun w => σ w = w)
  change ((Γ.neighborFinset h.v₀).filter (fun w => ¬ σ w = w)).card = 56
  omega

/-- **Edge complement neighbour count (`v₁`).** [done]

At the second endpoint, `|N(v₁) \ Fix(σ)| = 56 = 57 − 1`. -/
theorem edgeFixedData_complement_v1_count
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (h : EdgeFixedData Γ σ) :
    ((Γ.neighborFinset h.v₁).filter (fun w => σ w ≠ w)).card = 56 := by
  have h57 : (Γ.neighborFinset h.v₁).card = 57 := by
    have := hΓ.regular.degree_eq h.v₁
    rwa [SimpleGraph.degree] at this
  have h1 : ((Γ.neighborFinset h.v₁).filter (fun w => σ w = w)).card = 1 :=
    h.autFixedNeighborFinset_card_v1_eq_one
  have hsum := Finset.card_filter_add_card_filter_not (s := Γ.neighborFinset h.v₁)
    (p := fun w => σ w = w)
  change ((Γ.neighborFinset h.v₁).filter (fun w => ¬ σ w = w)).card = 56
  omega

end EdgeFixedData

variable [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Constructor from `|Fix(σ)| = 2` (Moore57 generic) -/

/-- **EdgeFixedData from fix-pair count + mod-7 fix-neighbour
constraint.** [done]

Given any permutation `σ : Equiv.Perm V` with `σ ^ 7 = 1` (graph
automorphism) and `fixedVertexCount σ = 2`, construct `EdgeFixedData Γ σ`.

The two fixed vertices necessarily form an edge: the H-degree at each
must be `≡ 1 (mod 7)` (from `aut_card_fixedNeighborFinset_modEq_one_of_pow_seven_pow`)
and `≤ 1` (since there are only 2 fixed vertices, so at most 1 σ-fixed
neighbour); hence H-degree is exactly `1`, i.e. the two fixed vertices
are Γ-adjacent. -/
noncomputable def edgeFixedData_of_fixedVertexCount_eq_two
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_seven : σ ^ 7 = 1)
    (h_count : fixedVertexCount σ = 2) :
    EdgeFixedData Γ σ := by
  classical
  -- Extract the two fixed vertices: |Fix| = 2 gives a 2-element finset.
  have h2 :
      ((Finset.univ : Finset V).filter (fun w => σ w = w)).card = 2 := h_count
  -- Use Finset.card_eq_two to get the pair.
  have hpair :
      ∃ v₀ v₁ : V, v₀ ≠ v₁ ∧
        ((Finset.univ : Finset V).filter (fun w => σ w = w)) = {v₀, v₁} :=
    Finset.card_eq_two.mp h2
  let v₀ : V := hpair.choose
  let v₁ : V := hpair.choose_spec.choose
  have hv_ne : v₀ ≠ v₁ := hpair.choose_spec.choose_spec.1
  have hfilter_eq :
      ((Finset.univ : Finset V).filter (fun w => σ w = w)) = {v₀, v₁} :=
    hpair.choose_spec.choose_spec.2
  -- v₀ fixed: read off membership.
  have hv0_mem : v₀ ∈ ((Finset.univ : Finset V).filter (fun w => σ w = w)) := by
    rw [hfilter_eq]; exact Finset.mem_insert_self _ _
  have hv1_mem : v₁ ∈ ((Finset.univ : Finset V).filter (fun w => σ w = w)) := by
    rw [hfilter_eq]; simp
  have hv0_fixed : σ v₀ = v₀ := (Finset.mem_filter.mp hv0_mem).2
  have hv1_fixed : σ v₁ = v₁ := (Finset.mem_filter.mp hv1_mem).2
  -- span: σ x = x ⟹ x ∈ {v₀, v₁}.
  have hspan : ∀ x : V, σ x = x → x = v₀ ∨ x = v₁ := by
    intro x hx
    have hmem : x ∈ ((Finset.univ : Finset V).filter (fun w => σ w = w)) := by
      simp [hx]
    rw [hfilter_eq] at hmem
    simp at hmem
    exact hmem
  -- Adjacency: H-degree of v₀ in σ-fix induced graph = card of σ-fixed
  -- neighbours of v₀ in Γ.  This is ≤ 1 (singleton {v₁} candidates) and
  -- ≡ 1 (mod 7) from `aut_card_fixedNeighborFinset_modEq_one_of_pow_seven_pow`.
  -- Hence card = 1, so v₁ is a σ-fixed neighbour of v₀, i.e. Γ.Adj v₀ v₁.
  have h_pp : σ ^ (7 : ℕ) ^ 1 = 1 := by simpa using pow_seven
  have h_nbrs_mod :
      (autFixedNeighborFinset Γ σ v₀).card ≡ 1 [MOD 7] :=
    aut_card_fixedNeighborFinset_modEq_one_of_pow_seven_pow
      hΓ σ smul_adj 1 h_pp hv0_fixed
  -- Upper bound: any σ-fixed neighbour of v₀ is in {v₀, v₁}, hence = v₁
  -- (since v₀ ≠ v₀ adj self).  So card ≤ 1.
  have h_nbrs_le_one :
      (autFixedNeighborFinset Γ σ v₀).card ≤ 1 := by
    have hsub :
        autFixedNeighborFinset Γ σ v₀ ⊆ {v₁} := by
      intro w hw
      have hadj : Γ.Adj v₀ w := (mem_autFixedNeighborFinset σ).mp hw |>.1
      have hwfix : σ w = w := (mem_autFixedNeighborFinset σ).mp hw |>.2
      rcases hspan w hwfix with hwv0 | hwv1
      · subst hwv0
        exact absurd hadj (SimpleGraph.irrefl Γ)
      · subst hwv1; simp
    calc (autFixedNeighborFinset Γ σ v₀).card
        ≤ ({v₁} : Finset V).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton v₁
  have h_nbrs_eq_one :
      (autFixedNeighborFinset Γ σ v₀).card = 1 := by
    rw [Nat.ModEq] at h_nbrs_mod
    omega
  -- v₁ is a σ-fixed neighbour of v₀.
  have hv1_in_nbrs : v₁ ∈ autFixedNeighborFinset Γ σ v₀ := by
    -- Since the finset has card 1 and v₁ is the only candidate (any element
    -- must be v₁ by the subset bound above), the finset = {v₁}.
    have hsub :
        autFixedNeighborFinset Γ σ v₀ ⊆ {v₁} := by
      intro w hw
      have hadj : Γ.Adj v₀ w := (mem_autFixedNeighborFinset σ).mp hw |>.1
      have hwfix : σ w = w := (mem_autFixedNeighborFinset σ).mp hw |>.2
      rcases hspan w hwfix with hwv0 | hwv1
      · subst hwv0
        exact absurd hadj (SimpleGraph.irrefl Γ)
      · subst hwv1; simp
    rcases Finset.card_eq_one.mp h_nbrs_eq_one with ⟨u, hu⟩
    have hu_mem_singleton : u ∈ ({v₁} : Finset V) := by
      apply hsub; rw [hu]; exact Finset.mem_singleton_self u
    have : u = v₁ := Finset.mem_singleton.mp hu_mem_singleton
    rw [hu, this]
    exact Finset.mem_singleton_self _
  have hadj : Γ.Adj v₀ v₁ :=
    (mem_autFixedNeighborFinset σ).mp hv1_in_nbrs |>.1
  exact
    { v₀ := v₀
      v₁ := v₁
      v_ne := hv_ne
      v₀_fixed := hv0_fixed
      v₁_fixed := hv1_fixed
      adj := hadj
      span := hspan }

/-! ### Order-7 EdgeFixedData via small fix-count -/

/-- **Lem 16 case 3 `EdgeFixedData` via small fix-count.** [done]

If `|Fix(σ)| ≤ 8`, the mod-7 congruence `|Fix(σ)| ≡ 2 (mod 7)` forces
`|Fix(σ)| = 2`, and `edgeFixedData_of_fixedVertexCount_eq_two` applies.

This mirrors the small-fix narrowing pattern of
`aut_order_thirteen_EmptyFixedData_of_small_fix` and
`aut_order_nineteen_SingletonFixedData_of_small_fix`.  The
small-fix hypothesis (`|Fix| ≤ 8`) is the external pin to `l = 0` in
the `K_{1, 1+7l}` family. -/
noncomputable def aut_order_seven_EdgeFixedData_of_small_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_seven : σ ^ 7 = 1)
    (h_small : fixedVertexCount σ ≤ 8) :
    EdgeFixedData Γ σ :=
  edgeFixedData_of_fixedVertexCount_eq_two hΓ σ smul_adj pow_seven
    (aut_order_seven_fixedVertexCount_eq_two_of_small hΓ σ pow_seven h_small)

end Moore57
