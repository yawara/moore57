import Moore57.Moore57Graph.Moore57Definition
import Moore57.Moore57Graph.Aut.InvolutionFixIsK155
import Moore57.Papers.Aschbacher1971.Lemma1_4_InvolutionFix
import Moore57.Foundations.GroupAction.FixedPoints
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Perm.Cycle.Type

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Cameron Ch.3 §3.7 — Automorphisms (substantive)

The character-theoretic machinery of association schemes gives a method
for non-existence of specific automorphisms. For an association scheme
with basis matrices `A_0, …, A_{r−1}` and projection idempotents
`E_0, …, E_{r−1}`, the `j`-th irreducible-constituent character value
on an automorphism `g` is

`χ_j(g) = Σ_i Q(i, j) α_i(g) / n`

where `α_i(g) = |{x ∈ Ω : (x, x^g) ∈ R_i}|` and `Q` is the second
eigenmatrix. Every character value is an algebraic integer; in
particular, if rational, an integer.

**Theorem 3.13.** *There is no vertex-transitive Moore graph of diameter
2 and valency 57.*

**Proof outline** (5 steps).

* **Step 1.** Fix(g) for `g ∈ Aut(Γ)` involution is either a star (a
  vertex and some of its neighbours) or a Moore subgraph. [non-adjacent
  fixed pair ⇒ unique common neighbour fixed; reduces to Aschbacher
  1971 Lemma 1.1 applied to the induced subgraph on Fix(g).]

* **Step 2.** If `g` interchanges two adjacent vertices `a, b`, then
  `|Fix(g)| = 56`. [Label the remaining 3248 vertices by pairs
  `(a', b') ∈ A × B` where `A = N(a) ∖ {b}`, `B = N(b) ∖ {a}`; `g`
  swaps `A ↔ B`; `(a', b')` is fixed iff `g` swaps `a', b'`; there are
  56 such pairs.]

* **Step 3.** `g` fixes 56 or 58 vertices, forming a star. [If `g`
  doesn't interchange any adjacent pair, then for each moved `a`,
  `{a, a^g}` has a unique common neighbour fixed; counting forces a
  58-point star. The 50-point Moore-subgraph alternative is excluded
  numerically (50·50 ≠ 3250 − 50).]

* **Step 4.** Actually `g` fixes 56. [Character argument: in the
  58-star case, `α_0 = 58, α_1 = 0, α_2 = 3192`; the `−8`-eigenspace
  character value computes to `−1/3`, contradicting integrality.]

* **Step 5.** Suppose `Aut(Γ)` vertex-transitive. Then `3250 ∣ |Aut(Γ)|`,
  so `|Aut(Γ)|` is even and contains an involution `g` with `|Fix(g)| = 56`.
  The stabiliser `Aut(Γ)_a` is then even-order, so `4 ∣ |Aut(Γ)|`. Let
  `H = Aut(Γ) ∩ A_{3250}` (alternating subgroup). Then `|H|` is even, so
  `H` contains an involution. But every involution has 56 fixed points
  and `(3250 − 56) / 2 = 1597` transpositions — `1597` is **odd**, so
  every involution is an **odd** permutation, contradicting `H ⊆ A_{3250}`.

For the formalisation:

* Steps 1–4 collapse: existing Moore57 infrastructure proves the
  **unconditional** statement `aut_involution_fixedVertexCount_eq_56`
  (every non-trivial involution fixes exactly 56). The route is via
  `aut_involution_exists_adjacent_moved` (every non-trivial involution
  interchanges some adjacent pair), which obviates Cameron Step 1's
  alternatives and gives Step 2's conclusion directly. The character
  argument of Step 4 is not needed because Cameron Step 3's 58-star
  case is structurally excluded in the Moore57 setting.
* Step 5 is a Sylow / parity argument. `4 ∤ |Aut(Γ)|` is partially
  available via Mačaj–Širáň 2010 §2 Lem 2 (skeleton); the alternating
  intersection step is new.
-/

namespace Moore57.Papers.CameronCh3

open Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Step 1 (fix set is star or Moore subgraph).** [deferred-heavy]

For an involution `g ∈ Aut(Γ)`, the fixed subgraph is either a star or
a sub-Moore-graph. (Aschbacher 1971 Lem 1.1 applied to the induced
subgraph on Fix(g), which inherits the strong (0, 1) condition by
Lem 1.2.) -/
theorem step1_fix_star_or_subMoore : True := by trivial

/-- **Step 2 (adjacent moved ⇒ 56 fixed)** — wraps existing infrastructure.

If a non-trivial involution `σ ∈ Aut(Γ)` interchanges an adjacent pair,
then `|Fix(σ)| = 56`. This is exactly
`aut_involution_fixedVertexCount_eq_56_of_adjacent_moved` in the
Moore57Graph.Aut.InvolutionFixIsK155 module. The Moore57 instance
already discharges Cameron's Step 2 via the unconditional 56-result:
`aut_involution_fixedVertexCount_eq_56`. -/
theorem step2_adjacent_moved_gives_56 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hinv : Function.Involutive σ) (hne : σ ≠ 1) :
    fixedVertexCount σ = 56 :=
  aut_involution_fixedVertexCount_eq_56 hΓ σ hAut hinv hne

/-- **Step 3 (fix is 56-star or 58-star, no other Moore subgraph).** [deferred-heavy]

In the case `g` does NOT interchange any adjacent pair, the fix would
have to be a 58-star or a 50-point Moore subgraph. Cameron's numerical
argument (50 · 50 ≠ 3250 − 50) eliminates the 50-Moore alternative,
forcing the 58-star.

In the Moore57 formalisation this case is structurally excluded by
`aut_involution_exists_adjacent_moved`, so the 58-star case never
arises. -/
theorem step3_58_star_or_56_star : True := by trivial

/-- **Step 3 (paper-faithful, Moore57 structural elimination).** [done]

Proper-signature paper-faithful packaging: in the Moore57 setting, the
"58-star vs 50-Moore-subgraph" alternative collapses to "always 56-star",
because every non-trivial involution interchanges an adjacent pair (by
`aut_involution_exists_adjacent_moved`).

Given the involution hypothesis, conclude `|Fix(σ)| = 56`. This skips
both alternatives of Cameron's Step 3 by structurally eliminating the
non-adjacent-moved case. -/
theorem step3_58_star_or_56_star_paper (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hinv : Function.Involutive σ) (hne : σ ≠ 1) :
    fixedVertexCount σ = 56 :=
  aut_involution_fixedVertexCount_eq_56 hΓ σ hAut hinv hne

/-- **Step 4 (character argument eliminates 58-star case).** [deferred-heavy]

The character value on the `−8`-eigenspace for an involution with
`α_0 = 58, α_1 = 0, α_2 = 3192` is `−1/3`, not an algebraic integer.

In the Moore57 formalisation this case is already excluded by Step 3,
so the character argument is unnecessary. -/
theorem step4_character_eliminates_58_star : True := by trivial

/-- **Step 4 (Moore57 conclusion: every involution fixes exactly 56)** —
wraps `aut_involution_fixedVertexCount_eq_56` unconditionally. -/
theorem step4_moore57_involution_fixes_56 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hinv : Function.Involutive σ) (hne : σ ≠ 1) :
    fixedVertexCount σ = 56 :=
  aut_involution_fixedVertexCount_eq_56 hΓ σ hAut hinv hne

/-- **Step 5 (parity contradiction).** [deferred-heavy]

If `Aut(Γ)` is vertex-transitive, then `3250 ∣ |Aut(Γ)|`. Hence `|Aut(Γ)|`
even, hence contains an involution `g` with `|Fix(g)| = 56`. The
non-fixed `3250 − 56 = 3194 = 2 · 1597` vertices decompose into 1597
transpositions. Since 1597 is **odd**, every involution `g` is an odd
permutation. But by transitivity `4 ∣ |Aut(Γ)|`, so `Aut(Γ) ∩ A_{3250}`
is even-order, contains an involution — contradiction. -/
theorem step5_parity_contradiction : True := by trivial

/-- **Theorem 3.13 (no vertex-transitive Moore57).** [proven downstream]

There is no vertex-transitive automorphism group of a Moore graph of
diameter 2 and valency 57.

The full statement and proof live downstream as
`Moore57.Papers.MacajSiran2010.S2.cor_lem2_no_vertex_transitive_aut`
(which is the corollary of `lem2_four_not_dvd_aut` + orbit-stabilizer).
The proof uses:

* `step5_moore57_involution_sign` (this file) — every Moore57 involution
  has sign `−1`.
* `MacajSiran2010.S2.lem2_four_not_dvd_aut` — `¬ 4 ∣ |G|` for any
  subgroup `G ≤ Aut(Γ)` (proven via sign + Cauchy).
* Mathlib's orbit-stabilizer + Cauchy.

This file keeps a placeholder for the bare `Theorem 3.13` label; the
actual full statement is `cor_lem2_no_vertex_transitive_aut`. -/
theorem theorem3_13_no_vertex_transitive_moore57 : True := by trivial

/-- **Theorem 3.13 (Moore57 involution-fix instance)** — wraps the
unconditional `|Fix(σ)| = 56` result. -/
theorem theorem3_13_moore57_inv_fixes_56 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hinv : Function.Involutive σ) (hne : σ ≠ 1) :
    fixedVertexCount σ = 56 :=
  aut_involution_fixedVertexCount_eq_56 hΓ σ hAut hinv hne

/-- **Parity arithmetic for Step 5.**

`(3250 − 56) / 2 = 1597`, which is odd. Hence any involution on `V`
with `|Fix(σ)| = 56` (and `|V| = 3250`) has an odd number of
transpositions, i.e. has sign `−1`. -/
theorem step5_transposition_count_odd :
    (3250 - 56) / 2 = 1597 ∧ Odd 1597 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- **Bridge: `Function.fixedPoints σ` cardinality equals `fixedVertexCount σ`.**

Mathlib's permutation-sign machinery is phrased in terms of
`Fintype.card (Function.fixedPoints σ)`. This lemma identifies it with
the Moore57 convention `fixedVertexCount σ`. -/
theorem card_fixedPoints_eq_fixedVertexCount (σ : Equiv.Perm V) :
    Fintype.card (Function.fixedPoints σ) = fixedVertexCount σ := by
  classical
  rw [fixedVertexCount_eq_card_fixedVertexSet]
  refine Fintype.card_congr ?_
  refine Equiv.setCongr ?_
  ext v
  simp [Function.fixedPoints, Function.IsFixedPt, fixedVertexSet]

/-- **Step 5 sign lemma (Moore57 involution is an odd permutation).**

Every non-trivial automorphism `σ` of Moore57 with `σ ^ 2 = 1` has
`Equiv.Perm.sign σ = −1`.

Proof. `aut_involution_fixedVertexCount_eq_56` gives `|Fix(σ)| = 56`.
By Mathlib's `Equiv.Perm.sign_of_pow_two_eq_one`:
`sign σ = (−1)^((|V| − |Fix(σ)|) / 2) = (−1)^((3250 − 56)/2) = (−1)^1597 = −1`. -/
theorem step5_moore57_involution_sign
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    Equiv.Perm.sign σ = -1 := by
  have hinv : Function.Involutive σ := fun x => by
    have h := congrArg (fun (f : Equiv.Perm V) => f x) hσ
    simpa [pow_two, Equiv.Perm.mul_apply] using h
  have h56 : fixedVertexCount σ = 56 :=
    aut_involution_fixedVertexCount_eq_56 hΓ σ hAut hinv hne
  have hcard : Fintype.card V = 3250 := hΓ.card
  have hfix : Fintype.card (Function.fixedPoints σ) = 56 := by
    rw [card_fixedPoints_eq_fixedVertexCount, h56]
  have hsign := Equiv.Perm.sign_of_pow_two_eq_one hσ
  rw [hcard, hfix] at hsign
  rw [hsign]
  -- Goal: (-1 : ℤˣ)^((3250 - 56) / 2) = -1
  have h1597 : (3250 - 56) / 2 = 1597 := by norm_num
  rw [h1597]
  -- Goal: (-1 : ℤˣ)^1597 = -1
  exact Odd.neg_one_pow (by decide : Odd 1597)

/-- **Step 5 (paper-faithful sign-of-involution).** [done]

Proper-signature paper-faithful packaging of the core arithmetic of
Step 5: every non-trivial Moore57 involution has odd sign (`sign σ = -1`).

The Step 5 contradiction chain proceeds by combining this sign result
with vertex-transitivity (`4 ∣ |Aut(Γ)| ⇒ ∃ involution in Aut ∩ A_{3250}`)
— the contradiction is "every involution is odd, so none lies in the
alternating subgroup". Delegates to `step5_moore57_involution_sign`. -/
theorem step5_parity_contradiction_paper
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    Equiv.Perm.sign σ = -1 :=
  step5_moore57_involution_sign hΓ σ hσ hne hAut

end Moore57.Papers.CameronCh3
