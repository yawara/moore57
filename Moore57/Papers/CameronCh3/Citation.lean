/-!
# Citation: Cameron, *Permutation Groups*, Chapter 3

Peter J. Cameron,
*Permutation Groups*, Chapter 3, "Coherent configurations",
Cambridge University Press, 1999.
DOI (chapter): [10.1017/CBO9780511623677.004](https://doi.org/10.1017/CBO9780511623677.004).

Local extracted text: `tmp/pdfs/cameron_ch3_coherent_configurations.txt`.

## Result map

| Statement / Section                                            | Location                                  |
|----------------------------------------------------------------|-------------------------------------------|
| §3.1 Introduction — coherent configurations                    | `Section01_Introduction.lean`             |
| §3.2 Algebraic theory — basis & intersection algebras          | `Section02_AlgebraicTheory.lean`          |
| §3.3 Association schemes (Theorem 3.5, 3.6)                    | `Section03_AssociationSchemes.lean`       |
| §3.4 Algebra of schemes (Theorem 3.8–3.10)                     | `Section04_AlgebraOfSchemes.lean`         |
| **§3.5 Strongly regular graphs (Theorem 3.11, 3.12)**          | `Section05_StronglyRegularGraphs.lean`    |
| §3.6 Hoffman–Singleton graph                                   | `Section06_HoffmanSingleton.lean`         |
| **§3.7 Automorphisms (Theorem 3.13: no vtx-trans Moore57)**    | `Section07_Automorphisms.lean`            |
| §3.8 Valency bounds (Theorem 3.14–3.16)                        | `Section08_ValencyBounds.lean`            |
| §3.9 Distance-transitive graphs (Theorem 3.17–3.19)            | `Section09_DistanceTransitive.lean`       |
| §3.10 Multiplicity bounds (Theorem 3.20–3.22, Krein cond.)     | `Section10_MultiplicityBounds.lean`       |
| §3.11 Duality (Theorem 3.23–3.24)                              | `Section11_Duality.lean`                  |
| §3.12 Wielandt's theorem (Theorem 3.25)                        | `Section12_Wielandt.lean`                 |
| Top-level re-export                                            | `MainTheorem.lean`                        |

## Relevance for Moore57

The chapter provides the modern (post-Higman) framework of association
schemes and coherent configurations that subsumes the rank-3
permutation-group infrastructure of Higman 1964 §§1–5. Two Moore57-load-bearing
results live here:

* **Theorem 3.12.** A Moore graph of diameter 2 has order in
  `{5, 10, 50, 3250}` and valency in `{2, 3, 7, 57}`. (Subsumes
  Higman 1964 §6 Theorem 1 in the SRG framework.)

* **Theorem 3.13.** There is no vertex-transitive Moore graph of diameter
  2 and valency 57. (Strictly stronger than Aschbacher 1971's main
  theorem: vertex-transitivity is weaker than rank-3, so ruling out
  vertex-transitive already rules out rank-3.)

Theorem 3.13's proof (Steps 1–5) lines up with existing Moore57
infrastructure:

* Step 1 (fix set is star or Moore subgraph) — Aschbacher 1971 Lem 1.1,
  applied to the induced subgraph on `Fix(g)`.
* Step 2 (interchanges adjacent ⇒ 56 fixed) —
  `aut_involution_fixedVertexCount_eq_56_of_adjacent_moved`.
* Step 1 ∪ Step 2 strengthened: ANY non-trivial involution interchanges
  some adjacent pair, hence fixes 56 — `aut_involution_exists_adjacent_moved`
  + `aut_involution_fixedVertexCount_eq_56`. This collapses Steps 1–4
  into the unconditional "every involution fixes exactly 56".
* Step 5 (Sylow / parity argument): in part covered by Macaj–Širáň 2010
  §2 Lem 2 (`4 ∤ |Aut Γ|`); the full parity contradiction is a [skeleton]
  pending the alternating-group intersection step.
-/
