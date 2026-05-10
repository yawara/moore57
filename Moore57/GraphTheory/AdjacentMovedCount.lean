import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Adjacent-moved vertices

This module records the graph-theoretic count of vertices sent to adjacent
vertices by a permutation.
-/

namespace Moore57

variable {V : Type*} [Fintype V]

/-- The number of vertices sent to adjacent vertices by `σ`.

This is the count denoted `a₁(σ)` in the Moore57 notes. -/
def adjacentMovedCount (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V) : ℕ :=
  ((Finset.univ : Finset V).filter fun v => Γ.Adj v (σ v)).card

end Moore57
