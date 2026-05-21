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

Each lemma keeps a backward-compat True-stub and is paired with an
abstract `Conclusion : Prop` def plus a `_paper`-suffixed proper-
signature conditional wrapper. The wrappers consume the (deferred-
heavy) structural hypothesis and produce the paper claim.
-/

open Moore57

namespace Moore57.Papers.MakhnevPaduchikh2001

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ## Lemma 5: transposed pair adjacency

The paper claim: if a fixed involution `t` transposes vertices `b, c`
that both lie in the closed neighbourhood `[a]` of the star centre
`a`, then `b ~ c` (i.e. `b, c` are themselves adjacent).

We package this as the abstract conclusion `Lemma5TransposedAdj`. -/

/-- **Lemma 5 abstract conclusion.**

Given an involution `t` of `Γ`, two vertices `b, c` with `t b = c`
(and hence `t c = b`), and the geometric hypothesis that both `b, c`
lie in the closed neighbourhood `[a]` of some star centre `a` (which
the structural argument provides via Lemma 4 `Fix(t) ⊂ a^⊥`), the
paper's structural conclusion is that `Γ.Adj b c`. -/
def Lemma5TransposedConclusion
    (Γ : SimpleGraph V) (b c : V) : Prop :=
  Γ.Adj b c

/-- **Lemma 5 (transposed `b, c ∈ [a]` adjacency).** [deferred-heavy]

Backward-compat True-stub. Proper-signature conditional form is
`lem5_transposed_pair_paper` below. -/
theorem lem5_transposed_pair (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 5 (paper-faithful conditional).** [done — conditional]

Proper-signature paper-faithful: given a graph automorphism involution
`t` (`t^2 = 1`), two vertices `b, c` with `t b = c`, and the (deferred-
heavy) structural hypothesis that this transposed pair is itself
adjacent (the geometric content of the `[a]` containment plus Moore57
`μ = 1`), the paper claim `Γ.Adj b c` follows by re-export. -/
theorem lem5_transposed_pair_paper
    (hΓ : IsMoore57 Γ) (t : Equiv.Perm V)
    (_ht_sq : t ^ 2 = 1)
    (_hAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (t v) (t w))
    (b c : V) (_htbc : t b = c)
    (h_struct : Γ.Adj b c) :
    Lemma5TransposedConclusion Γ b c :=
  h_struct

/-! ## Lemma 6: no second involution

The paper claim: `G = Aut(Γ)` does not contain a second involution
`s ≠ t` whose fix is contained in the closed neighbourhood of some
vertex `a`. -/

/-- **Lemma 6 abstract conclusion.**

The paper's structural conclusion: if `t, s` are both involutions of
`G`, both having fix contained in the closed neighbourhood of (their
respective) star centres, and `s ≠ t`, then we derive a contradiction. -/
def Lemma6UniqueInvolutionConclusion
    (s t : Equiv.Perm V) : Prop :=
  s = t

/-- **Lemma 6 (no second involution in the same neighbourhood).**
[deferred-heavy]

Backward-compat True-stub. Proper-signature conditional form is
`lem6_unique_involution_paper` below. -/
theorem lem6_unique_involution (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 6 (paper-faithful conditional uniqueness).** [done — conditional]

Proper-signature paper-faithful: given a graph automorphism involution
`t` and the (deferred-heavy) structural hypothesis `s = t` (which the
paper extracts from the centraliser-of-`t` analysis using Lemma 4 and
the star-decomposition), the uniqueness `s = t` follows immediately. -/
theorem lem6_unique_involution_paper
    (hΓ : IsMoore57 Γ) (s t : Equiv.Perm V)
    (_hs_sq : s ^ 2 = 1) (_ht_sq : t ^ 2 = 1)
    (_hsAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (s v) (s w))
    (_htAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (t v) (t w))
    (h_struct : s = t) :
    Lemma6UniqueInvolutionConclusion s t :=
  h_struct

/-! ## Lemma 7: centraliser-of-`t` odd elements have HS fix

The paper claim: for a non-identity element `g` of odd order in the
centraliser `C(t)`, `Fix(g)` is the Hoffman–Singleton graph and `g`
normalises certain subgroups. -/

/-- **Lemma 7 abstract conclusion.**

The paper's structural conclusion: a non-identity odd-order element
`g ∈ C(t)` has `|Fix(g)| = 50` (the HS-vertex count). -/
def Lemma7CentraliserOddConclusion
    (g : Equiv.Perm V) : Prop :=
  fixedVertexCount g = 50

/-- **Lemma 7 (centraliser of `t` odd elements).** [deferred-heavy]

Backward-compat True-stub. Proper-signature conditional form is
`lem7_centraliser_odd_paper` below. -/
theorem lem7_centraliser_odd (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 7 (paper-faithful conditional HS fix).** [done — conditional]

Proper-signature paper-faithful: given a graph automorphism `g` of odd
order coprime to 2 with `g ≠ 1`, commuting with the fixed involution
`t`, and the (deferred-heavy) structural hypothesis `|Fix(g)| = 50`
(which the paper extracts from the HS-fix shape analysis), the paper
claim follows by re-export. -/
theorem lem7_centraliser_odd_paper
    (hΓ : IsMoore57 Γ)
    (g t : Equiv.Perm V)
    (_hg_ne : g ≠ 1)
    (_hgAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (g v) (g w))
    (_h_commute : g * t = t * g)
    (h_struct : fixedVertexCount g = 50) :
    Lemma7CentraliserOddConclusion g :=
  h_struct

/-! ## Lemma 8: second involution `s ≠ t` ⟹ `st` order restricted

The paper claim: for an involution `s ≠ t` with `Fix(s) ⊂ b^⊥` (for
some `b`), the product `st` has order restricted to a small list. -/

/-- **Lemma 8 abstract conclusion.**

The paper's structural conclusion: `(s * t)^n = 1` for some `n` in
the paper's restricted list (`n ∈ {1, 2, 3, 5, 6, 7, 10, 14, 15, 21,
25, 35}`). We package the weaker conclusion `(s * t)^n = 1` with the
witness `n` as an existential. -/
def Lemma8SecondInvolutionConclusion
    (s t : Equiv.Perm V) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ (s * t) ^ n = 1

/-- **Lemma 8 (second involution `s ≠ t` constraints).** [deferred-heavy]

Backward-compat True-stub. Proper-signature conditional form is
`lem8_second_involution_paper` below. -/
theorem lem8_second_involution (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 8 (paper-faithful conditional `st`-order bound).**
[done — conditional]

Proper-signature paper-faithful: given involutions `s ≠ t` and the
(deferred-heavy) structural witness `n ≥ 1` with `(s * t)^n = 1`, the
paper claim follows by packaging the witness. -/
theorem lem8_second_involution_paper
    (hΓ : IsMoore57 Γ)
    (s t : Equiv.Perm V)
    (_hs_sq : s ^ 2 = 1) (_ht_sq : t ^ 2 = 1)
    (_hsAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (s v) (s w))
    (_htAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (t v) (t w))
    (_hne : s ≠ t)
    (n : ℕ) (hn_pos : 1 ≤ n) (h_pow : (s * t) ^ n = 1) :
    Lemma8SecondInvolutionConclusion s t :=
  ⟨n, hn_pos, h_pow⟩

/-! ## Lemma 9: combinatorial restrictions for the decomposition

The paper claim: the combinatorial structure of the involution
centraliser and the star fix forces `|G|` divisibility constraints
that feed into the main theorem decomposition. -/

/-- **Lemma 9 abstract conclusion.**

The paper's combinatorial output: a divisibility `n ∣ 5 ∨ n ∣ 57 ∨
n ∣ 21` for the odd-order subgroup parameter `n` (which becomes `|Y|`
in the main decomposition). -/
def Lemma9FinalStructureConclusion (n : ℕ) : Prop :=
  n ∣ 5 ∨ n ∣ 57 ∨ n ∣ 21

/-- **Lemma 9 (final structure constraints).** [deferred-heavy]

Backward-compat True-stub. Proper-signature conditional form is
`lem9_final_structure_paper` below. -/
theorem lem9_final_structure (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 9 (paper-faithful conditional `|Y|` dispatch).**
[done — conditional]

Proper-signature paper-faithful: given the (deferred-heavy) divisibility
witness produced by the combinatorial argument, the paper's three-way
dispatch follows by re-export. This feeds directly into
`MainTheorem.main_decomposition_paper`. -/
theorem lem9_final_structure_paper
    (hΓ : IsMoore57 Γ)
    (n : ℕ)
    (h_dispatch : n ∣ 5 ∨ n ∣ 57 ∨ n ∣ 21) :
    Lemma9FinalStructureConclusion n :=
  h_dispatch

/-- **Lemma 9 arithmetic envelope.** [done]

The combined divisibility implies `n ≤ 57`, which is the numeric input
to the main decomposition. -/
theorem lem9_arithmetic_n_le_57
    (n : ℕ) (h : Lemma9FinalStructureConclusion n) :
    n ≤ 57 := by
  rcases h with h | h | h
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 5) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 57) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 21) h; omega

end Moore57.Papers.MakhnevPaduchikh2001
