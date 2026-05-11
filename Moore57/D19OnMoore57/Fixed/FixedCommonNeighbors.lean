import Moore57.Moore57Graph.Moore57Definition
import Moore57.D19OnMoore57.Action.D19Action

namespace Moore57
namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- If two non-adjacent vertices are fixed by a group element, then their unique
common neighbor is fixed by the same group element. -/
theorem fixed_commonNeighbor_of_not_adj
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    {x y z : V}
    (hx : h.smul g x = x) (hy : h.smul g y = y)
    (hxy : x ≠ y) (hnadj : ¬ Γ.Adj x y)
    (hz : Γ.Adj x z ∧ Γ.Adj y z) :
    h.smul g z = z := by
  have hz_mem : z ∈ Γ.commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact hz
  have hgz_adj_x : Γ.Adj x (h.smul g z) := by
    have hgz_adj := (h.smul_adj g x z).mp hz.1
    simpa [hx] using hgz_adj
  have hgz_adj_y : Γ.Adj y (h.smul g z) := by
    have hgz_adj := (h.smul_adj g y z).mp hz.2
    simpa [hy] using hgz_adj
  have hgz_mem : h.smul g z ∈ Γ.commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨hgz_adj_x, hgz_adj_y⟩
  have hcard : Fintype.card (Γ.commonNeighbors x y) = 1 :=
    h.isMoore.of_not_adj hxy hnadj
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨w, hw_unique⟩
  have hw_z : (w : V) = z :=
    (congrArg Subtype.val (hw_unique ⟨z, hz_mem⟩)).symm
  have hw_gz : (w : V) = h.smul g z :=
    (congrArg Subtype.val (hw_unique ⟨h.smul g z, hgz_mem⟩)).symm
  exact hw_gz.symm.trans hw_z

/-- If a group element swaps two non-adjacent vertices, then their unique
common neighbor is fixed by that group element. -/
theorem fixed_commonNeighbor_of_swap_not_adj
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    {x y z : V}
    (hgx : h.smul g x = y) (hgy : h.smul g y = x)
    (hxy : x ≠ y) (hnadj : ¬ Γ.Adj x y)
    (hz : Γ.Adj x z ∧ Γ.Adj y z) :
    h.smul g z = z := by
  have hz_mem : z ∈ Γ.commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact hz
  have hgz_adj_x : Γ.Adj x (h.smul g z) := by
    have hgz_adj := (h.smul_adj g y z).mp hz.2
    simpa [hgy] using hgz_adj
  have hgz_adj_y : Γ.Adj y (h.smul g z) := by
    have hgz_adj := (h.smul_adj g x z).mp hz.1
    simpa [hgx] using hgz_adj
  have hgz_mem : h.smul g z ∈ Γ.commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨hgz_adj_x, hgz_adj_y⟩
  have hcard : Fintype.card (Γ.commonNeighbors x y) = 1 :=
    h.isMoore.of_not_adj hxy hnadj
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨w, hw_unique⟩
  have hw_z : (w : V) = z :=
    (congrArg Subtype.val (hw_unique ⟨z, hz_mem⟩)).symm
  have hw_gz : (w : V) = h.smul g z :=
    (congrArg Subtype.val (hw_unique ⟨h.smul g z, hgz_mem⟩)).symm
  exact hw_gz.symm.trans hw_z

/-- Existence form: the unique common neighbor of two fixed non-adjacent vertices
is itself fixed. -/
theorem exists_fixed_commonNeighbor_of_not_adj
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    {x y : V}
    (hx : h.smul g x = x) (hy : h.smul g y = y)
    (hxy : x ≠ y) (hnadj : ¬ Γ.Adj x y) :
    ∃ z, h.smul g z = z ∧ Γ.Adj x z ∧ Γ.Adj y z := by
  have hcard : Fintype.card (Γ.commonNeighbors x y) = 1 :=
    h.isMoore.of_not_adj hxy hnadj
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨z, _hz_unique⟩
  have hz_mem : (z : V) ∈ Γ.commonNeighbors x y := z.property
  have hz_adj : Γ.Adj x (z : V) ∧ Γ.Adj y (z : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hz_mem
    exact hz_mem
  exact ⟨z, h.fixed_commonNeighbor_of_not_adj g hx hy hxy hnadj hz_adj, hz_adj⟩

/-- Existence form: if a group element swaps two non-adjacent vertices, their
unique common neighbor is fixed by that group element. -/
theorem exists_fixed_commonNeighbor_of_swap_not_adj
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    {x y : V}
    (hgx : h.smul g x = y) (hgy : h.smul g y = x)
    (hxy : x ≠ y) (hnadj : ¬ Γ.Adj x y) :
    ∃ z, h.smul g z = z ∧ Γ.Adj x z ∧ Γ.Adj y z := by
  have hcard : Fintype.card (Γ.commonNeighbors x y) = 1 :=
    h.isMoore.of_not_adj hxy hnadj
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨z, _hz_unique⟩
  have hz_mem : (z : V) ∈ Γ.commonNeighbors x y := z.property
  have hz_adj : Γ.Adj x (z : V) ∧ Γ.Adj y (z : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hz_mem
    exact hz_mem
  exact ⟨z, h.fixed_commonNeighbor_of_swap_not_adj g hgx hgy hxy hnadj hz_adj,
    hz_adj⟩

end D19ActsOnMoore57
end Moore57
