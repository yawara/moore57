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
* **§3.7 Theorem 3.13** — No vertex-transitive Moore (57, 2) graph
  (skeleton). Steps 1–4 collapsed via the unconditional Moore57
  result `aut_involution_fixedVertexCount_eq_56`; Step 5 (parity /
  alternating intersection) remains skeleton.

These results subsume:

* Higman 1964 §6 Theorem 1 (Theorem 3.12 in modern SRG form).
* Aschbacher 1971 Main Theorem (Theorem 3.13 in modern vertex-transitive
  form, strictly stronger than rank-3 non-existence).

For Moore57 formalisation, Theorem 3.13 is the natural top-level target
because Moore57's existing involution machinery (`Aut.InvolutionFixIsK155`)
is the proof of Cameron Steps 1–4.
-/
