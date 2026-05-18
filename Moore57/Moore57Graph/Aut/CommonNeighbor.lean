import Moore57.Moore57Graph.Moore57Definition

/-!
# Fixed common neighbours under a Moore57 automorphism (Tier 2)

Abstract versions of the rotation/reflection-side common-neighbour lemmas in
`D19OnMoore57/Fixed/CommonNeighbors.lean`. The statements take a bare
`σ : V → V` together with an adjacency-preservation hypothesis, so they apply
to any automorphism of a Moore57 graph regardless of which symmetry group
it comes from.

These are used to build the abstract order-`n` fixed-cardinality theorem
`order19_aut_fixedVertexCount_eq_one`, which is later specialised back to the
`D₁₉` rotation in `D19OnMoore57/Rotation/FixedCardinality.lean`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

omit [DecidableEq V] in
/-- If two non-adjacent vertices are fixed by an automorphism `σ` of a Moore57
graph, then their unique common neighbour is also fixed by `σ`. -/
theorem aut_fixed_commonNeighbor_of_not_adj
    (hΓ : IsMoore57 Γ) (σ : V → V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {x y z : V}
    (hx : σ x = x) (hy : σ y = y)
    (hxy : x ≠ y) (hnadj : ¬ Γ.Adj x y)
    (hz : Γ.Adj x z ∧ Γ.Adj y z) :
    σ z = z := by
  have hz_mem : z ∈ Γ.commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact hz
  have hgz_adj_x : Γ.Adj x (σ z) := by
    have hgz_adj := (smul_adj x z).mp hz.1
    simpa [hx] using hgz_adj
  have hgz_adj_y : Γ.Adj y (σ z) := by
    have hgz_adj := (smul_adj y z).mp hz.2
    simpa [hy] using hgz_adj
  have hgz_mem : σ z ∈ Γ.commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨hgz_adj_x, hgz_adj_y⟩
  have hcard : Fintype.card (Γ.commonNeighbors x y) = 1 :=
    hΓ.of_not_adj hxy hnadj
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨w, hw_unique⟩
  have hw_z : (w : V) = z :=
    (congrArg Subtype.val (hw_unique ⟨z, hz_mem⟩)).symm
  have hw_gz : (w : V) = σ z :=
    (congrArg Subtype.val (hw_unique ⟨σ z, hgz_mem⟩)).symm
  exact hw_gz.symm.trans hw_z

omit [DecidableEq V] in
/-- If an automorphism `σ` of a Moore57 graph swaps two non-adjacent vertices,
then their unique common neighbour is fixed by `σ`. -/
theorem aut_fixed_commonNeighbor_of_swap_not_adj
    (hΓ : IsMoore57 Γ) (σ : V → V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {x y z : V}
    (hgx : σ x = y) (hgy : σ y = x)
    (hxy : x ≠ y) (hnadj : ¬ Γ.Adj x y)
    (hz : Γ.Adj x z ∧ Γ.Adj y z) :
    σ z = z := by
  have hz_mem : z ∈ Γ.commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact hz
  have hgz_adj_x : Γ.Adj x (σ z) := by
    have hgz_adj := (smul_adj y z).mp hz.2
    simpa [hgy] using hgz_adj
  have hgz_adj_y : Γ.Adj y (σ z) := by
    have hgz_adj := (smul_adj x z).mp hz.1
    simpa [hgx] using hgz_adj
  have hgz_mem : σ z ∈ Γ.commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨hgz_adj_x, hgz_adj_y⟩
  have hcard : Fintype.card (Γ.commonNeighbors x y) = 1 :=
    hΓ.of_not_adj hxy hnadj
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨w, hw_unique⟩
  have hw_z : (w : V) = z :=
    (congrArg Subtype.val (hw_unique ⟨z, hz_mem⟩)).symm
  have hw_gz : (w : V) = σ z :=
    (congrArg Subtype.val (hw_unique ⟨σ z, hgz_mem⟩)).symm
  exact hw_gz.symm.trans hw_z

omit [DecidableEq V] in
/-- Existence form: the unique common neighbour of two non-adjacent vertices
fixed by `σ` is itself fixed by `σ`. -/
theorem aut_exists_fixed_commonNeighbor_of_not_adj
    (hΓ : IsMoore57 Γ) (σ : V → V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {x y : V}
    (hx : σ x = x) (hy : σ y = y)
    (hxy : x ≠ y) (hnadj : ¬ Γ.Adj x y) :
    ∃ z, σ z = z ∧ Γ.Adj x z ∧ Γ.Adj y z := by
  have hcard : Fintype.card (Γ.commonNeighbors x y) = 1 :=
    hΓ.of_not_adj hxy hnadj
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨z, _hz_unique⟩
  have hz_mem : (z : V) ∈ Γ.commonNeighbors x y := z.property
  have hz_adj : Γ.Adj x (z : V) ∧ Γ.Adj y (z : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hz_mem
    exact hz_mem
  exact ⟨z, aut_fixed_commonNeighbor_of_not_adj hΓ σ smul_adj hx hy hxy hnadj hz_adj,
    hz_adj⟩

omit [DecidableEq V] in
/-- Existence form: if `σ` swaps two non-adjacent vertices, their unique common
neighbour is fixed by `σ`. -/
theorem aut_exists_fixed_commonNeighbor_of_swap_not_adj
    (hΓ : IsMoore57 Γ) (σ : V → V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {x y : V}
    (hgx : σ x = y) (hgy : σ y = x)
    (hxy : x ≠ y) (hnadj : ¬ Γ.Adj x y) :
    ∃ z, σ z = z ∧ Γ.Adj x z ∧ Γ.Adj y z := by
  have hcard : Fintype.card (Γ.commonNeighbors x y) = 1 :=
    hΓ.of_not_adj hxy hnadj
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨z, _hz_unique⟩
  have hz_mem : (z : V) ∈ Γ.commonNeighbors x y := z.property
  have hz_adj : Γ.Adj x (z : V) ∧ Γ.Adj y (z : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hz_mem
    exact hz_mem
  exact ⟨z,
    aut_fixed_commonNeighbor_of_swap_not_adj hΓ σ smul_adj hgx hgy hxy hnadj hz_adj,
    hz_adj⟩

end Moore57
