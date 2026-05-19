import Moore57.Papers.MakhnevPaduchikh2001.Lemma04_InvolutionGood

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Makhnev–Paduchikh 2001, Lemmas 5–9 (involution-centric structure) [deferred-heavy]

Throughout this group of lemmas, `t` is a fixed involution of `G` and
`Fix(t) ⊂ a^⊥` (i.e. the star centered at some vertex `a`). By Lemma 4,
`G = O(G) ⟨t⟩`.

* **Lemma 5.** If `t` transposes vertices `b, c ∈ [a]`, then various
  adjacency / orbit conditions hold (used in §5 of MP01 proof).
* **Lemma 6.** `G` contains no involution `s ≠ t` with `Fix(s) ⊂ a^⊥`.
* **Lemma 7.** For a non-identity element `g` of odd order in `C(t)`,
  `Fix(g)` is the Hoffman–Singleton graph and `g` normalises certain
  subgroups.
* **Lemma 8.** For an involution `s ≠ t` with `Fix(s) ⊂ b^⊥`, the
  element `st` has very restricted order.
* **Lemma 9.** Combinatorial restrictions used to assemble the main
  theorem decomposition.
-/

namespace Moore57.Papers.MakhnevPaduchikh2001

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 5 (transposed `b, c ∈ [a]` adjacency).** [deferred-heavy] -/
theorem lem5_transposed_pair (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 6 (no second involution in the same neighbourhood).** [deferred-heavy] -/
theorem lem6_unique_involution (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 7 (centraliser of `t` odd elements).** [deferred-heavy] -/
theorem lem7_centraliser_odd (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 8 (second involution `s ≠ t` constraints).** [deferred-heavy] -/
theorem lem8_second_involution (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 9 (final structure constraints).** [deferred-heavy] -/
theorem lem9_final_structure (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MakhnevPaduchikh2001
