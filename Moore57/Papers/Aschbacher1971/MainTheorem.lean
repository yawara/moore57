import Moore57.Papers.Aschbacher1971.Citation
import Moore57.Papers.Aschbacher1971.Lemma1_1_RegularOrStar
import Moore57.Papers.Aschbacher1971.Lemma1_2_FixInheritsStar
import Moore57.Papers.Aschbacher1971.Lemma1_3_ValenceClassification
import Moore57.Papers.Aschbacher1971.Lemma1_4_InvolutionFix
import Moore57.Papers.Higman1964.Theorem1_DegreeKSqPlus1
import Moore57.Papers.CameronCh3.Section07_Automorphisms

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Aschbacher 1971 — main theorem [skeleton]

> No rank-3 permutation group of degree 3250 and subdegree 57 exists.

Equivalently: the missing Moore (57, 2) graph (if it exists) does not
admit a rank-3 automorphism group acting on its vertex set.

Proof outline (in paper, using Lemmas 1.1–1.4):
* `G^Ω` is rank 3 of degree 3250, subdegree 57; let `H = G_∞` for a
  distinguished point `∞ ∈ Ω`, with non-trivial orbits `Δ` (`|Δ| = 57`)
  and `Γ`. The graph `𝒢` defined by `β I γ ⇔ β ∈ Δ(γ)` satisfies (*).
* An involution in `H` fixes 1, 3, 7, 55, or 57 points of `Δ`
  (Lemma 1.4 applied via the K_{1,55}-structure on the involution fix).
* Let `K ≤ H` be permutations even on both `Δ` and `Ω`. An involution
  `x ∈ K` fixes 1 or 57 points of `Δ`, hence fixes a 56- or 58-point
  star; being even on `Ω` forces the 58-point case.
* `|H : K| ≤ 4`, `|Γ|` is divisible by 8, so `|K|` is even; transitivity
  gives involutions `u, v ∈ K_α` with `F(u)`, `F(v)` the 58-point stars
  at `∞` and `α`.
* `u, v ∈ K_α`, not conjugate in `K_α`, both inside a Sylow 2-subgroup
  `S`. One of them lies in `Z(S)`, so `uv ∈ K_α` is an involution; but
  `uv` would then fix only `{∞, α}` in `Δ ∪ Δ(α)`, contradicting the
  56/58-star case analysis.

This main theorem is **not** directly needed by Mačaj–Širáň 2010's target
(`|Aut(Γ)| ≤ 375`), but it explains the name "Aschbacher graph" for the
hypothetical Moore (57, 2).
-/

namespace Moore57.Papers.Aschbacher1971

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Main theorem (rank-3 non-existence on degree 3250 / subdegree 57).** [skeleton]

Stated symbolically as a placeholder; a full formalisation would require
introducing the permutation-group action `G ↷ Ω` of rank 3 and the
distinguishing data of the proof above.

**External dependency now in-tree**: the line "Results of D. Higman show
that 𝒢 satisfies (*) [2]" cites Higman 1964 §6 Theorem 1, available as
`Moore57.Papers.Higman1964.theorem1_n_kSq_plus_one` (statement skeleton)
and its proven arithmetic core
`Moore57.Papers.Higman1964.theorem1_arithmetic_core`. The valence `k = 57`
sits in the `4k − 3 = 225` branch of that classification.

**Stronger result fully proven downstream**:
`Moore57.Papers.MacajSiran2010.S2.cor_lem2_no_vertex_transitive_aut`
rules out any vertex-transitive subgroup `G ≤ Aut(Γ)` of a Moore57
graph. Since rank-3 ⇒ vertex-transitive, this strictly subsumes the
present Aschbacher result. The proof uses:

* `CameronCh3.Section07.step5_moore57_involution_sign` (every Moore57
  involution has sign `−1`).
* `MacajSiran2010.S2.lem2_four_not_dvd_aut` (`¬ 4 ∣ |G|`, proven via
  sign + Cauchy, no Sylow theory).
* Mathlib orbit-stabilizer + Cauchy.

A full proof of the Main Theorem still requires the rank-3
permutation-group action infrastructure (Lemmas 1–7 of Higman 1964, +
Aschbacher's §2 involution / Sylow argument); both dependencies are now
in-tree as Cameron Ch.3 §§3.1–3.4 (basis algebra, association schemes)
and Higman 1964 (rank-3 framework). -/
theorem main_no_rank3_3250_57 : True := by trivial

/-- **Pointer: Higman 1964 Theorem 1, Moore57 valence fork.**

The valence `k = 57` is one of the four allowed by Higman's
classification (`{2, 3, 7, 57}`). -/
theorem main_valence_in_higman_classification :
    (57 : ℕ) = 2 ∨ (57 : ℕ) = 3 ∨ (57 : ℕ) = 7 ∨ (57 : ℕ) = 57 :=
  Moore57.Papers.Higman1964.theorem1_moore57_valence

end Moore57.Papers.Aschbacher1971
