import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Aut.SemiRegularComplement
import Moore57.Moore57Graph.Moore57Definition
import Moore57.Foundations.GroupAction.FixedPoints

/-!
# Singleton + Empty fixed subgraph data (Tier C / §6 Lem 17-19 inputs)

Data structures for the remaining Mačaj–Širáň §6 Lemma 17 / 18 / 19 cases
not covered by `PetersenFixedData`, `HSFixedData`, `C5FixedData`,
`K155FixedData`:

* `SingletonFixedData Γ σ` — `Fix(σ) = {v}` (a single isolated fixed vertex).
  This is the §6 Lem 17 case (2) input.

* `EmptyFixedData V σ` — `Fix(σ) = ∅` (σ has no fixed points).  This is
  the §6 Lem 18 case (3) / Lem 19 case (1)+(3) input.

Both structures are minimal: their main purpose is to make the case
disjunction in Lemma 17 / 18 / 19 explicit.  Bridge lemmas connect them
to the appropriate complement-count facts.
-/

namespace Moore57

variable {V : Type*}

/-! ## Singleton fixed subgraph data -/

/-- The σ-fixed subgraph of Γ is a single isolated vertex.

This is the §6 Lemma 17 case (2) input: `Fix(σ)` consists of exactly one
vertex, with no other σ-fixed vertices in the graph. -/
structure SingletonFixedData (σ : Equiv.Perm V) where
  /-- The unique fixed vertex. -/
  v : V
  /-- σ fixes `v`. -/
  v_fixed : σ v = v
  /-- σ has no other fixed points. -/
  span : ∀ x : V, σ x = x → x = v

namespace SingletonFixedData

variable {Γ : SimpleGraph V} {σ : Equiv.Perm V}

/-- **Singleton bridge to `autFixedNeighborFinset`**: at the unique fixed
vertex, the σ-fixed neighbour count equals `0` (no other fixed vertices
exist, so none can be neighbours). -/
theorem autFixedNeighborFinset_card_eq_zero
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (h : SingletonFixedData σ) :
    (autFixedNeighborFinset Γ σ h.v).card = 0 := by
  rw [Finset.card_eq_zero]
  ext w
  simp only [mem_autFixedNeighborFinset, Finset.notMem_empty, iff_false, not_and]
  intro hadj hfix
  have : w = h.v := h.span w hfix
  rw [this] at hadj
  exact SimpleGraph.irrefl Γ hadj

/-- **Singleton `fixedVertexCount = 1`**: the σ-fixed-vertex count is `1`
(just `v`). -/
theorem fixedVertexCount_eq_one
    [Fintype V] [DecidableEq V] (h : SingletonFixedData σ) :
    fixedVertexCount σ = 1 := by
  unfold fixedVertexCount
  have : (Finset.univ : Finset V).filter (fun w => σ w = w) = {h.v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨h.span w, ?_⟩
    rintro rfl; exact h.v_fixed
  rw [this, Finset.card_singleton]

/-- **Singleton complement neighbour count**: at the unique fixed vertex
on a Moore57 graph, `|N(v) \ Fix(σ)| = 57 = 57 − 0`.

This is the §6 Lem 17 case (2) semi-regular orbit input: σ acts on a
57-element set (the entire neighbourhood) and the orbit-stabilizer
argument gives `orderOf σ ∣ 57`, which combined with σ being a 3-group
gives `orderOf σ ∣ gcd(3^k, 57) = 3` (since 57 = 3·19). -/
theorem singletonFixedData_complement_neighbor_count
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (h : SingletonFixedData σ) :
    ((Γ.neighborFinset h.v).filter (fun w => σ w ≠ w)).card = 57 := by
  have h57 : (Γ.neighborFinset h.v).card = 57 := by
    have := hΓ.regular.degree_eq h.v
    rwa [SimpleGraph.degree] at this
  have h0 : ((Γ.neighborFinset h.v).filter (fun w => σ w = w)).card = 0 :=
    h.autFixedNeighborFinset_card_eq_zero (Γ := Γ)
  have hsum := Finset.card_filter_add_card_filter_not (s := Γ.neighborFinset h.v)
    (p := fun w => σ w = w)
  change ((Γ.neighborFinset h.v).filter (fun w => ¬ σ w = w)).card = 57
  omega

/-- **Singleton semi-regular orbit bridge**: for σ with `SingletonFixedData`
on a Moore57 graph and σ acting semi-regularly on `N(v) \ Fix(σ)`,
`orderOf σ ∣ 57`.  [C3.4] Lem 17 case (2) input. -/
theorem singleton_orderOf_dvd_57_of_semiRegular
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (h : SingletonFixedData σ)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hsemi : ∀ w ∈ autMovedNeighborFinset Γ σ h.v,
             ∀ k : ℕ, (σ^k) w = w → orderOf σ ∣ k) :
    orderOf σ ∣ 57 := by
  have hcard : (autMovedNeighborFinset Γ σ h.v).card = 57 :=
    h.singletonFixedData_complement_neighbor_count (Γ := Γ) hΓ
  exact hcard ▸ orderOf_dvd_card_movedNeighbour_of_semiRegular
    σ smul_adj h.v_fixed hsemi

end SingletonFixedData

/-! ## Empty fixed subgraph data -/

/-- The σ-fixed subgraph of Γ is empty: σ has no fixed points.

This is the §6 Lemma 18 case (3) / Lemma 19 cases (1)+(3) input: σ acts
semi-regularly on the entire vertex set, so `orderOf σ ∣ |V|`. -/
structure EmptyFixedData (σ : Equiv.Perm V) where
  /-- σ has no fixed points. -/
  no_fixed : ∀ x : V, σ x ≠ x

namespace EmptyFixedData

variable {σ : Equiv.Perm V}

/-- **Empty bridge**: globally `|Fix(σ)| = 0`.  The σ-fixed-vertex
finset is empty. -/
theorem fixedVertex_finset_empty
    [Fintype V] [DecidableEq V] (h : EmptyFixedData σ) :
    ((Finset.univ : Finset V).filter (fun w => σ w = w)).card = 0 := by
  rw [Finset.card_eq_zero]
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
             iff_false]
  exact h.no_fixed w

/-- **Empty `fixedVertexCount = 0`**. -/
theorem fixedVertexCount_eq_zero
    [Fintype V] [DecidableEq V] (h : EmptyFixedData σ) :
    fixedVertexCount σ = 0 :=
  h.fixedVertex_finset_empty

/-- **Empty complement = full**: for σ with `EmptyFixedData` on a Moore57
graph, `|V \ Fix(σ)| = |V| = 3250`.

This is the §6 Lem 18 case (3) semi-regular orbit input: σ acts on
the entire 3250-element vertex set without fixed points, and the
orbit-stabilizer argument gives `orderOf σ ∣ 3250`. -/
theorem emptyFixedData_complement_vertex_count
    {Γ : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (h : EmptyFixedData σ) :
    ((Finset.univ : Finset V).filter (fun w => σ w ≠ w)).card = 3250 := by
  have hcard : Fintype.card V = 3250 := hΓ.card
  have h0 : ((Finset.univ : Finset V).filter (fun w => σ w = w)).card = 0 :=
    h.fixedVertex_finset_empty
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
    (p := fun w => σ w = w)
  rw [Finset.card_univ, hcard] at hsum
  change ((Finset.univ : Finset V).filter (fun w => ¬ σ w = w)).card = 3250
  omega

/-- **Empty semi-regular orbit bridge**: for σ with `EmptyFixedData` on a
Moore57 graph and σ acting semi-regularly on `V` (no fixed points),
`orderOf σ ∣ 3250`.  [C3.4] Lem 18 case (3) / Lem 19 input.

Since `Fix(σ) = ∅`, the relevant set is the entire vertex set, and
σ-invariance is automatic. -/
theorem empty_orderOf_dvd_3250_of_semiRegular
    {Γ : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (_h : EmptyFixedData σ)
    (hsemi : ∀ v : V, ∀ k : ℕ, (σ^k) v = v → orderOf σ ∣ k) :
    orderOf σ ∣ 3250 := by
  have hcard : (Finset.univ : Finset V).card = 3250 := by
    rw [Finset.card_univ]; exact hΓ.card
  rw [← hcard]
  apply orderOf_dvd_card_of_semiRegular σ Finset.univ
  · intros; exact Finset.mem_univ _
  · intros v _ k hkv; exact hsemi v k hkv

end EmptyFixedData

end Moore57
