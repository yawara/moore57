import Moore57.Papers.Aschbacher1971.Citation
import Moore57.Papers.Aschbacher1971.Lemma1_1_RegularOrStar
import Moore57.Papers.Aschbacher1971.Lemma1_2_FixInheritsStar
import Moore57.Papers.Aschbacher1971.Lemma1_3_ValenceClassification
import Moore57.Papers.Aschbacher1971.Lemma1_4_InvolutionFix
import Moore57.Papers.Higman1964.Theorem1_DegreeKSqPlus1
import Moore57.Papers.CameronCh3.Section07_Automorphisms
import Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Lemma2_Involution

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Aschbacher 1971 — main theorem [deferred-heavy]

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

/-- **Main theorem (rank-3 non-existence on degree 3250 / subdegree 57).** [deferred-heavy]

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

/-- **Main theorem (proven form, via vertex-transitivity).**

The rank-3 hypothesis implies vertex-transitivity (rank-3 transitive
groups are 2-transitive on orbital partitions, hence in particular
transitive on `Ω`). Hence the stronger
`MacajSiran2010.S2.cor_lem2_no_vertex_transitive_aut` already rules
out any rank-3 permutation group of degree 3250 on a Moore57 graph.

This wrapper exposes the vertex-transitivity form directly. -/
theorem main_no_vertex_transitive_3250_57
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : Moore57.IsMoore57 Γ)
    (G : Subgroup (Equiv.Perm V)) [DecidablePred (· ∈ G)]
    (hG : ∀ σ ∈ G, ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hVtrans : MulAction.IsPretransitive G V) : False :=
  Moore57.Papers.MacajSiran2010.S2.cor_lem2_no_vertex_transitive_aut
    hΓ G hG hVtrans

/-- **Pointer: Higman 1964 Theorem 1, Moore57 valence fork.**

The valence `k = 57` is one of the four allowed by Higman's
classification (`{2, 3, 7, 57}`). -/
theorem main_valence_in_higman_classification :
    (57 : ℕ) = 2 ∨ (57 : ℕ) = 3 ∨ (57 : ℕ) = 7 ∨ (57 : ℕ) = 57 :=
  Moore57.Papers.Higman1964.theorem1_moore57_valence

/-! ### Aschbacher Cor (D4.1): SRG arithmetic + involution dichotomy

The combined corollary form: from the SRG eigenvalue/multiplicity
chain (Lem 6/7 + Thm 1, i.e., `theorem1_case_two_full_conditional`)
and the involution-fix dichotomy (Lem 1.4 algebraic core
`asc1_4_arithmetic_core`), the (k, f) pair for a Moore SRG with
involution satisfies:

* `k ∈ {3, 7, 57}` (the Case II Higman classification, modulo k = 2
  Case I), AND
* `f ∈ {k − 1, k + 1}` (the involution fix dichotomy).

This is the precise form of the joint arithmetic constraint needed
for Aschbacher's §2 case analysis (which then uses Sylow + sign to
exclude the k = 57 sub-case).  -/

/-- **Aschbacher Cor (D4.1, combined classification)**: under the Case II
arithmetic + involution quadratic, the `(k, f)` pair is fully classified.
[done]

Inputs:
* `4·k = e² + 3` (perfect square discriminant — Case II Lem 7).
* `2·(e·f₂) = k·(k·(e + 1) − 2)` (integer multiplicity formula in ℤ —
  Lem 7 Moore-parameter specialisation).
* `k ≥ 2` (non-degenerate rank-3 subdegree).
* `(f − k − 1)(f − k + 1) = 0` (involution fix quadratic — Lem 1.4
  algebraic core).

Conclusion: `k ∈ {3, 7, 57} ∧ f ∈ {k − 1, k + 1}`. -/
theorem asc_cor_combined_classification
    {k e : ℕ} {f₂ f : ℤ}
    (he_sq : 4 * k = e * e + 3)
    (h_mult_Z : 2 * ((e : ℤ) * f₂) =
                (k : ℤ) * ((k : ℤ) * ((e : ℤ) + 1) - 2))
    (h_k_ge_2 : 2 ≤ k)
    (h_invol_quad : (f - (k : ℤ) - 1) * (f - (k : ℤ) + 1) = 0) :
    (k = 3 ∨ k = 7 ∨ k = 57) ∧ (f = (k : ℤ) - 1 ∨ f = (k : ℤ) + 1) :=
  ⟨Moore57.Papers.Higman1964.theorem1_case_two_full_conditional
     he_sq h_mult_Z h_k_ge_2,
   asc1_4_arithmetic_core f (k : ℤ) h_invol_quad⟩

/-- **Aschbacher Cor Moore57 instance**: for `(k, f) = (57, 56)`, the
combined classification holds (k = 57 from Higman Thm 1; f = k − 1 from
Lem 1.4 part 1).  [done] -/
theorem asc_cor_moore57_instance :
    ((57 : ℕ) = 3 ∨ (57 : ℕ) = 7 ∨ (57 : ℕ) = 57) ∧
    ((56 : ℤ) = (57 : ℤ) - 1 ∨ (56 : ℤ) = (57 : ℤ) + 1) := by
  refine ⟨?_, ?_⟩
  · right; right; rfl
  · left; norm_num

end Moore57.Papers.Aschbacher1971
