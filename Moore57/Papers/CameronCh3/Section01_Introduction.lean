import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Cameron Ch.3 §3.1 — Coherent configurations (definitions)

A coherent configuration on a set `Ω` is a pair `(Ω, 𝓡)` where `𝓡` is
a set of binary relations on `Ω` satisfying:

* (CC1) `𝓡` is a partition of `Ω²`.
* (CC2) A subset of `𝓡` is a partition of the diagonal.
* (CC3) `𝓡` is closed under transposition.
* (CC4) For `i, j, k ∈ {1, …, r}` and `(α, β) ∈ R_k`, the number of
  points `γ ∈ Ω` with `(α, γ) ∈ R_i` and `(γ, β) ∈ R_j` depends only on
  `i, j, k` (the *intersection numbers* `p_{ij}^k`).

If `G` is a permutation group on `Ω` and `𝓡` is the set of orbitals of
`G`, then `(Ω, 𝓡)` is the coherent configuration of `G`. Higman's
language is recovered: the orbits `Δ(α), Γ(α), …` are the row-sections
of `𝓡`, and `p_{ij}^k` are the intersection numbers of Higman 1964 §2
Lemma 2 in the rank-3 case.

In matrix form (Theorem 3.1): a set of 0/1 matrices `{A_1, …, A_r}` is
the set of basis matrices of a coherent configuration iff `(CC1*)`–`(CC4*)`
hold, where `(CC4*)` is `A_i · A_j = Σ_k p_{ij}^k A_k`. The C-span `V(𝓐)`
is then the *basis algebra* (centraliser algebra in the group case).

[out-of-scope]
-/

namespace Moore57.Papers.CameronCh3

/-- **Definition: coherent configuration.** [out-of-scope]

A coherent configuration is the data of a finite set `Ω` together with a
partition `𝓡` of `Ω²` satisfying conditions (CC1)–(CC4). -/
def IsCoherentConfiguration : True := trivial

/-- **Theorem 3.1 (matrix form).** [out-of-scope]

`{A_1, …, A_r}` is the basis matrix set of a coherent configuration iff:

* (CC1*) `Σ_i A_i = J` (all-ones).
* (CC2*) A subset of `{A_i}` sums to `I`.
* (CC3*) `{A_i^T}` is a permutation of `{A_i}`.
* (CC4*) For each `i, j`, `A_i · A_j ∈ ℕ-span({A_k})`. -/
theorem theorem3_1_matrix_form : True := by trivial

end Moore57.Papers.CameronCh3
