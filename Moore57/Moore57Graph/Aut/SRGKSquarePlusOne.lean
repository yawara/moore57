import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Local Hoffman-Singleton bound: SRG(k² + 1, k, 0, 1) classification

A strongly-regular graph with parameters `(k² + 1, k, 0, 1)` exists only
for `k ∈ {0, 1, 2, 3, 7, 57}`.

This is a "local" form of the classical Hoffman-Singleton theorem on Moore
graphs of girth 5, derived from the integrality of eigenvalue multiplicities
on the adjacency matrix `A` satisfying `A² + A − (k − 1)I = J − I`.

**Status**: stated as an axiomatic input for now. Filling this in requires
real-symmetric-matrix spectral theory (eigenvalue/multiplicity integrality)
which is not yet in Mathlib in a usable form for SRGs. The proof is a
classical textbook result (Hoffman-Singleton 1960; see Cameron-van Lint Ch3).

This axiom is purely about graph theory — it has no Moore57-specific
content. Discharging it would automatically make all our σ_fix-dependent
results unconditional.
-/

namespace Moore57

/-- **Local Hoffman-Singleton classification**: a strongly-regular graph
with parameters `(k² + 1, k, 0, 1)` exists only when
`k ∈ {0, 1, 2, 3, 7, 57}`.

The four "exotic" instances are: `k = 2` → C₅ pentagon; `k = 3` → Petersen;
`k = 7` → Hoffman-Singleton; `k = 57` → Moore57 (whose existence is
itself the unresolved long-standing open problem). -/
axiom srg_k_sq_plus_one_degree_classification
    {W : Type*} [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (k : ℕ)
    (_hsrg : G.IsSRGWith (k * k + 1) k 0 1) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57

end Moore57
