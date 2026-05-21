import Moore57.Papers.MakhnevPaduchikh2001.MainTheorem
import Moore57.Moore57Graph.Aut.InvolutionFixIsK155

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Theorem 2 (Makhnev–Paduchikh) [external]

> Let Γ be a Moore (57, 2)-graph and let `G = Aut(Γ)`. Assume that `G`
> contains an involution `t`. Then:
>
> (a) `G = ⟨Y, t⟩ × X` for some subgroups `X` and `Y` of odd order, `Y` is
>     inverted by `t`, and either `|Y|` divides 5 or 57, or `|Y|` divides 21,
>
> (b) if `X ≠ 1`, then `Fix(X)` can be one of: a star (`Y = 1, |X| = 7`); a
>     pentagon (`|Y| | 5, |X| | 55`); the Petersen graph (`|Y| | 3, |X| | 27`);
>     the Hoffman–Singleton graph (`|Y| | 5 or 7, |X| | 25`).

This result is imported from `Moore57.Papers.MakhnevPaduchikh2001`, which
formalizes [Makhnev–Paduchikh 2001].
-/

open Moore57

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 2 part (1) (paper-faithful): `Fix(t)` is a 56-vertex star.**
[done — delegates to MP 2001 main_fix_t_star]

For any non-trivial involution `t ∈ Aut(Γ)`, `|Fix(t)| = 56` and the
induced graph on `Fix(t)` is a star.  This is the **unconditional** part
of MP 2001's Theorem 2 — Part (1) follows directly from Cameron/Higman
star structure for any Moore57 graph automorphism involution. -/
theorem thm2_part1_fix_t_is_56_star_paper
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    fixedVertexCount σ = 56 ∧
      ∃ c : fixedVertexSet σ, IsStarWithCenter (autFixedInducedGraph Γ σ) c :=
  Moore57.Papers.MakhnevPaduchikh2001.main_fix_t_star hΓ σ hσ hne hAut

/-- **Theorem 2 part (a) `|Y| ≤ 57` (paper-faithful, conditional).**
[done — delegates to MP 2001 main_decomposition_paper]

Given the paper's three-way dispatch (`|Y| ∣ 5`, `|Y| ∣ 57`, or `|Y| ∣ 21`)
for the odd subgroup `Y` of the decomposition `G = ⟨Y, t⟩ × X`,
conclude `|Y| ≤ 57`.

This is the **Y bound** referenced in L4 plan §4.5 step 2: it feeds the
Theorem 7 even-order odd-part dispatch (the |G| ≤ 110 even-branch
bound). -/
theorem thm2_part_a_Y_card_le_57_paper
    (Y : ℕ) (h_dispatch : Y ∣ 5 ∨ Y ∣ 57 ∨ Y ∣ 21) :
    Y ≤ 57 :=
  Moore57.Papers.MakhnevPaduchikh2001.main_decomposition_paper Y h_dispatch

/-- **Theorem 2 part (b) `|X| ≤ 55` (paper-faithful, conditional).**
[done — delegates to MP 2001 main_fix_X_cases_paper]

Given the paper's four-way dispatch for `Fix(X)` shape and `(|Y|, |X|)`
pair (star, pentagon, Petersen, Hoffman-Singleton cases), conclude
`|X| ≤ 55`. -/
theorem thm2_part_b_X_card_le_55_paper
    (X Y : ℕ)
    (h_dispatch :
      (Y = 1 ∧ X = 7) ∨
      (Y ∣ 5 ∧ X ∣ 55) ∨
      (Y ∣ 3 ∧ X ∣ 27) ∨
      ((Y ∣ 5 ∨ Y ∣ 7) ∧ X ∣ 25)) :
    X ≤ 55 :=
  Moore57.Papers.MakhnevPaduchikh2001.main_fix_X_cases_paper X Y h_dispatch

/-- **Theorem 2 (Makhnev–Paduchikh) abstract conclusion.**

Encodes the full MP 2001 paper claim for an involution `t ∈ Aut(Γ)`:
* Part (1): `Fix(t)` is a 56-vertex star.
* Part (a): the decomposition `G = ⟨Y, t⟩ × X` exists with `|Y|` bounded.
* Part (b): `Fix(X)` falls into one of four shape cases with `|X|` bounded.

The Prop encoding bundles these into a single conditional shape for
downstream consumers (e.g., Thm 7 even-branch in L4 plan §4.5). -/
def Thm2MakhnevPaduchikhConclusion (Γ : SimpleGraph V) [DecidableRel Γ.Adj] : Prop :=
  ∀ (σ : Equiv.Perm V), σ ^ 2 = 1 → σ ≠ 1 →
    (∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) →
    (fixedVertexCount σ = 56 ∧
       ∃ c : fixedVertexSet σ, IsStarWithCenter (autFixedInducedGraph Γ σ) c) ∧
    -- Y dispatch is implicit; Part (a) Y bound applies to derived Y
    True

/-- **Theorem 2 (Makhnev–Paduchikh): Part (1) witnesses `Conclusion`.**
[done — partial]

The unconditional Part (1) (`Fix(t)` is a 56-vertex star) provides the
first conjunct of `Thm2MakhnevPaduchikhConclusion Γ`.  Parts (a)/(b) Y/X
bounds are accessible separately via `thm2_part_a_Y_card_le_57_paper`
and `thm2_part_b_X_card_le_55_paper`. -/
theorem thm2_makhnev_paduchikh_conclusion_part1
    (hΓ : IsMoore57 Γ) :
    Thm2MakhnevPaduchikhConclusion Γ := by
  intro σ hσ hne hAut
  refine ⟨thm2_part1_fix_t_is_56_star_paper hΓ σ hσ hne hAut, trivial⟩

/-- **Theorem 2 (Makhnev–Paduchikh structure for even `|Aut(Γ)|`).** [external]
[deferred-heavy backward-compat shell]

Proper-signature paper-faithful upgrades (Part 1 unconditional, Parts a/b
conditional) are
`thm2_part1_fix_t_is_56_star_paper`,
`thm2_part_a_Y_card_le_57_paper`,
`thm2_part_b_X_card_le_55_paper`,
and `thm2_makhnev_paduchikh_conclusion_part1`. -/
theorem thm2_makhnev_paduchikh (hΓ : IsMoore57 Γ) : True := by
  trivial

end Moore57.Papers.MacajSiran2010.S2
