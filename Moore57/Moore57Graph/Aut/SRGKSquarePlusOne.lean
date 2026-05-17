import Moore57.Foundations.GraphTheory.HoffmanSingleton

/-!
# Local Hoffman-Singleton bound: SRG(k² + 1, k, 0, 1) classification

A strongly-regular graph with parameters `(k² + 1, k, 0, 1)` exists only
for `k ∈ {0, 1, 2, 3, 7, 57}`.

This is a "local" form of the classical Hoffman-Singleton theorem on Moore
graphs of girth 5, derived from the integrality of eigenvalue multiplicities
on the adjacency matrix `A` satisfying `A² + A − (k − 1)I = J − I`.

**Status**: fully proven via `srg_k_sq_plus_one_degree_classification'` in
[Moore57.Foundations.GraphTheory.HoffmanSingleton](../../Foundations/GraphTheory/HoffmanSingleton.lean).
Was previously an axiom; now a theorem.
-/

namespace Moore57

/-- **Local Hoffman-Singleton classification**: a strongly-regular graph
with parameters `(k² + 1, k, 0, 1)` exists only when
`k ∈ {0, 1, 2, 3, 7, 57}`.

The four "exotic" instances are: `k = 2` → C₅ pentagon; `k = 3` → Petersen;
`k = 7` → Hoffman-Singleton; `k = 57` → Moore57 (whose existence is
itself the unresolved long-standing open problem). -/
theorem srg_k_sq_plus_one_degree_classification
    {W : Type*} [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (k : ℕ)
    (hsrg : G.IsSRGWith (k * k + 1) k 0 1) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 :=
  srg_k_sq_plus_one_degree_classification' G k hsrg

end Moore57
