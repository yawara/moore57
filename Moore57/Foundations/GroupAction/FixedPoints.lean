import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Fixed points of finite permutations

This module is independent of the Moore57 graph.  It records the fixed-point
count and fixed-point set for finite permutations.
-/

namespace Moore57

variable {V : Type*}

/-- Number of fixed points of a permutation. -/
def fixedVertexCount [DecidableEq V] [Fintype V] (σ : Equiv.Perm V) : ℕ :=
  ((Finset.univ : Finset V).filter fun v => σ v = v).card

/-- The set of fixed vertices of a permutation. -/
noncomputable def fixedVertexSet (σ : Equiv.Perm V) : Set V :=
  {v | σ v = v}

instance fixedVertexSet.fintype [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) : Fintype (fixedVertexSet σ) := by
  dsimp [fixedVertexSet]
  infer_instance

@[simp] theorem mem_fixedVertexSet {σ : Equiv.Perm V} {v : V} :
    v ∈ fixedVertexSet σ ↔ σ v = v := by
  rfl

@[simp] theorem fixedVertexSet_one :
    fixedVertexSet (1 : Equiv.Perm V) = Set.univ := by
  ext v
  simp [fixedVertexSet]

theorem fixedVertexSet_toFinset_eq_filter
    [Fintype V] [DecidableEq V] (σ : Equiv.Perm V) :
    (fixedVertexSet σ).toFinset =
      (Finset.univ : Finset V).filter (fun v => σ v = v) := by
  classical
  ext v
  simp [fixedVertexSet]

/-- The fixed-point count is the cardinality of the fixed-point set. -/
theorem fixedVertexCount_eq_card_fixedVertexSet
    [Fintype V] [DecidableEq V] (σ : Equiv.Perm V) :
    fixedVertexCount σ = Fintype.card (fixedVertexSet σ) := by
  classical
  rw [← Set.toFinset_card, fixedVertexSet_toFinset_eq_filter]
  rfl

theorem fixedVertexSet_eq_support_compl
    [Fintype V] [DecidableEq V] (σ : Equiv.Perm V) :
    fixedVertexSet σ = (σ.supportᶜ : Set V) := by
  ext v
  simp [fixedVertexSet, Equiv.Perm.support]

end Moore57
