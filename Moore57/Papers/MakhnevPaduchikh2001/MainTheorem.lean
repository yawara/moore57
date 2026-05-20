import Moore57.Papers.MakhnevPaduchikh2001.Citation
import Moore57.Papers.MakhnevPaduchikh2001.Lemma01_StrongFix
import Moore57.Papers.MakhnevPaduchikh2001.Lemma02_InvolutionFix
import Moore57.Papers.MakhnevPaduchikh2001.Lemma03_OddPrimeFix
import Moore57.Papers.MakhnevPaduchikh2001.Lemma04_InvolutionGood
import Moore57.Papers.MakhnevPaduchikh2001.Lemmas05_to_09_Structure

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Makhnev–Paduchikh 2001 — main theorem

> Let Γ be the Aschbacher graph and `G = Aut(Γ)`. Assume that `G` contains
> an involution `t`. Then:
>
> (1) `Fix(t)` is a star with 56 vertices;
>
> (2) `G = ⟨Y, t⟩ × X` for some subgroups `X` and `Y` of odd order, `Y` is
>     inverted by `t`, and either `|Y|` divides 5 or 57, or `|Y|` divides
>     21 (and for `|Y| = 21`, `|Fix(y)| = 37` for an order-7 element
>     `y ∈ Y`);
>
> (3) if `X ≠ 1` then `Fix(X)` is one of: a star (`Y = 1, |X| = 7`); a
>     pentagon (`|Y| | 5, |X| | 55`); Petersen's graph (`|Y| | 3, |X| | 27`);
>     Hoffman–Singleton's graph (`|Y| | 5 or 7, |X| | 25`).

Imported by `Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Theorem2_MakhnevPaduchikh`.

Status:
* Part (1) `|Fix(t)| = 56` + star structure is **wrapped** from
  `Moore57.Moore57Graph.Aut.InvolutionFixIsK155` (Cameron/Higman).
* Parts (2) and (3) (group decomposition + `Fix(X)` cases) remain
  skeletons — they need substantial new formalization of the
  involution-centralizer / odd-order subgroup decomposition argument.
-/

open Moore57

namespace Moore57.Papers.MakhnevPaduchikh2001

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Convert `σ ^ 2 = 1` to `Function.Involutive σ`. -/
private theorem _involutive_of_sq_eq_one'' {σ : Equiv.Perm V} (hσ : σ ^ 2 = 1) :
    Function.Involutive σ := fun x => by
  have h := congrArg (fun (f : Equiv.Perm V) => f x) hσ
  simpa [pow_two, Equiv.Perm.mul_apply] using h

/-- **Main theorem (1) (`Fix(t)` is a 56-vertex star).**
For any non-trivial involution `t ∈ Aut(Γ)`, `|Fix(t)| = 56` and `Fix(t)` is
a star (centered at some vertex). -/
theorem main_fix_t_star (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    fixedVertexCount σ = 56 ∧
      ∃ c : fixedVertexSet σ, IsStarWithCenter (autFixedInducedGraph Γ σ) c := by
  have hinv : Function.Involutive σ := _involutive_of_sq_eq_one'' hσ
  refine ⟨?_, ?_⟩
  · exact aut_involution_fixedVertexCount_eq_56 hΓ σ hAut hinv hne
  · exact aut_involution_fixedInducedGraph_isStarWithCenter hΓ σ hAut hinv hne

/-- **Main theorem (2) (decomposition `G = ⟨Y, t⟩ × X`).** [deferred-heavy]

Backward-compat True-stub.  Proper-signature `|Y|` bound form is
`main_decomposition_paper` (defined after `main_decomposition_Y_card_le_57`
below). -/
theorem main_decomposition (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Main theorem (2) `|Y|` arithmetic bound**. [done]

Given the paper's structural conclusion `|Y| ∣ 5 ∨ |Y| ∣ 57 ∨ |Y| ∣ 21`
(the three possibilities for the odd subgroup `Y` of `G = ⟨Y, t⟩ × X`),
conclude `|Y| ≤ 57`.

This is the arithmetic envelope of the `|Y|` constraints. The maximum
is `|Y| = 57` (the `|Y| ∣ 57` branch). -/
theorem main_decomposition_Y_card_le_57
    (Y : ℕ) (h : Y ∣ 5 ∨ Y ∣ 57 ∨ Y ∣ 21) :
    Y ≤ 57 := by
  rcases h with h | h | h
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 5) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 57) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 21) h; omega

/-- **Main theorem (2) (paper-faithful conditional Y bound).** [done]

Proper-signature paper-faithful packaging of the `|Y|` bound: given the
paper's three-way dispatch (`|Y| ∣ 5`, `|Y| ∣ 57`, or `|Y| ∣ 21`) for the
odd subgroup `Y` of the decomposition `G = ⟨Y, t⟩ × X`, conclude
`|Y| ≤ 57`. -/
theorem main_decomposition_paper
    (Y : ℕ) (h_dispatch : Y ∣ 5 ∨ Y ∣ 57 ∨ Y ∣ 21) :
    Y ≤ 57 :=
  main_decomposition_Y_card_le_57 Y h_dispatch

/-- **Main theorem (3) (`Fix(X)` cases when `X ≠ 1`).** [deferred-heavy] -/
theorem main_fix_X_cases (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Main theorem (3) `|X|` arithmetic dispatch**. [done]

Given the paper's four-way dispatch for `Fix(X)` shape and `|X|`:
* Star case: `|Y| = 1, |X| = 7`.
* Pentagon case: `|Y| ∣ 5, |X| ∣ 55`.
* Petersen case: `|Y| ∣ 3, |X| ∣ 27`.
* Hoffman-Singleton case: `|Y| ∣ 5 or 7, |X| ∣ 25`.

Conclude `|X| ∣ 55 ∨ |X| ∣ 27 ∨ |X| ∣ 25 ∨ |X| = 7`, which captures
the four `|X|`-bound possibilities. -/
theorem main_fix_X_cases_arithmetic
    (X Y : ℕ)
    (h_dispatch :
      (Y = 1 ∧ X = 7) ∨
      (Y ∣ 5 ∧ X ∣ 55) ∨
      (Y ∣ 3 ∧ X ∣ 27) ∨
      ((Y ∣ 5 ∨ Y ∣ 7) ∧ X ∣ 25)) :
    X ∣ 55 ∨ X ∣ 27 ∨ X ∣ 25 ∨ X = 7 := by
  rcases h_dispatch with ⟨_, hX⟩ | ⟨_, hX⟩ | ⟨_, hX⟩ | ⟨_, hX⟩
  · right; right; right; exact hX
  · left; exact hX
  · right; left; exact hX
  · right; right; left; exact hX

/-- **Main theorem (3) `|X|` numeric bound**. [done]

The `|X|` dispatch gives `|X| ≤ 55`. -/
theorem main_fix_X_cases_card_le_55
    (X Y : ℕ)
    (h_dispatch :
      (Y = 1 ∧ X = 7) ∨
      (Y ∣ 5 ∧ X ∣ 55) ∨
      (Y ∣ 3 ∧ X ∣ 27) ∨
      ((Y ∣ 5 ∨ Y ∣ 7) ∧ X ∣ 25)) :
    X ≤ 55 := by
  rcases main_fix_X_cases_arithmetic X Y h_dispatch with h | h | h | h
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 55) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 27) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 25) h; omega
  · omega

end Moore57.Papers.MakhnevPaduchikh2001
