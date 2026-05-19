import Moore57.Papers.CameronCh3.Citation
import Moore57.Papers.CameronCh3.Section01_Introduction
import Moore57.Papers.CameronCh3.Section02_AlgebraicTheory
import Moore57.Papers.CameronCh3.Section03_AssociationSchemes
import Moore57.Papers.CameronCh3.Section04_AlgebraOfSchemes
import Moore57.Papers.CameronCh3.Section05_StronglyRegularGraphs
import Moore57.Papers.CameronCh3.Section06_HoffmanSingleton
import Moore57.Papers.CameronCh3.Section07_Automorphisms
import Moore57.Papers.CameronCh3.Section08_ValencyBounds
import Moore57.Papers.CameronCh3.Section09_DistanceTransitive
import Moore57.Papers.CameronCh3.Section10_MultiplicityBounds
import Moore57.Papers.CameronCh3.Section11_Duality
import Moore57.Papers.CameronCh3.Section12_Wielandt
import Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Lemma2_Involution

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Cameron Ch.3 — top-level re-export

This file exposes the chapter's load-bearing Moore57 results under
`Moore57.Papers.CameronCh3`:

* **§3.5 Theorem 3.12** — Moore (k, 2) graph classification
  `k ∈ {2, 3, 7, 57}` (skeleton; arithmetic core proven via
  `Higman1964.theorem1_arithmetic_core`). Moore57 instances:
  `theorem3_12_moore57_valence`, `theorem3_12_moore57_order`,
  `theorem3_12_moore57_isSRG` all proven (wrap existing).
* **§3.7 Theorem 3.13** — No vertex-transitive Moore (57, 2) graph.
  The full statement `theorem3_13_no_vertex_transitive_moore57_proven`
  is proven by wrapping `MacajSiran2010.S2.cor_lem2_no_vertex_transitive_aut`.

These results subsume:

* Higman 1964 §6 Theorem 1 (Theorem 3.12 in modern SRG form).
* Aschbacher 1971 Main Theorem (Theorem 3.13 in modern vertex-transitive
  form, strictly stronger than rank-3 non-existence).
-/

open Moore57

namespace Moore57.Papers.CameronCh3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 3.13 (no vertex-transitive Moore57) — full proven statement.**

There is no vertex-transitive automorphism group of a Moore graph of
diameter 2 and valency 57. Wraps
`MacajSiran2010.S2.cor_lem2_no_vertex_transitive_aut`.

The Section07_Automorphisms.lean version `theorem3_13_no_vertex_transitive_moore57`
is the paper-section-level placeholder; this is the actual proven form. -/
theorem theorem3_13_no_vertex_transitive_moore57_proven (hΓ : IsMoore57 Γ)
    (G : Subgroup (Equiv.Perm V)) [DecidablePred (· ∈ G)]
    (hG : ∀ σ ∈ G, ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hVtrans : MulAction.IsPretransitive G V) : False :=
  Moore57.Papers.MacajSiran2010.S2.cor_lem2_no_vertex_transitive_aut
    hΓ G hG hVtrans

end Moore57.Papers.CameronCh3
