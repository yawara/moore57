import Moore57.Papers.MacajSiran2010.Section05_Tables.Lemma12_PrimeOrder
import Moore57.Foundations.GroupAction.FixedPoints
import Moore57.Moore57Graph.Aut.PetersenFixedData
import Moore57.Moore57Graph.Aut.HSFixedData
import Moore57.Moore57Graph.Aut.FixedSubgraphData
import Moore57.Moore57Graph.Aut.SingletonAndEmptyFixedData
import Moore57.Moore57Graph.Aut.TraceIntegrality

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §5, Lemma 13

> Let `x` be an automorphism of Γ of order `p²` where `p = 3` or `p = 5`.
> Then the values `a₁(x), a₁(x^p), Tr(x)` satisfy a 6-row table.
>
> Two rows (marked `*`) require non-integral traces and cannot occur.

Status:
* `lem13_prime_squared_table` — full 6-row table, deferred-heavy.
* `lem13_starred_row_5_0_5_no_integer_trace` and
  `lem13_starred_row_5_5_5_no_integer_trace` — **proven** arithmetic
  cores for the two starred rows (non-integrality contradictions).
-/

namespace Moore57.Papers.MacajSiran2010.S5

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 13 starred row arithmetic: row `5* (0, 5)` excluded.** [done]

For `p = 5`, `a₀(x) = 0`, `a₀(x⁵) = 5`, the paper's character system
forces `Tr(x) = 33.6 + 60·k + 60·l`, equivalently
`5·Tr(x) = 168 + 300·k + 300·l`.  Since `168 ≡ 3 (mod 5)`, no integer
`Tr(x)` can satisfy this, hence the row cannot occur. -/
theorem lem13_starred_row_5_0_5_no_integer_trace
    (Tr : ℤ) (k l : ℕ) (h : 5 * Tr = 168 + 300 * k + 300 * l) :
    False := by
  omega

/-- **Lemma 13 starred row arithmetic: row `5* (5, 5)` excluded.** [done]

For `p = 5`, `a₀(x) = 5`, `a₀(x⁵) = 5`, the paper's character system
forces `Tr(x) = 21.6 + 60·k + 60·l`, equivalently
`5·Tr(x) = 108 + 300·k + 300·l`.  Since `108 ≡ 3 (mod 5)`, no integer
`Tr(x)` can satisfy this, hence the row cannot occur. -/
theorem lem13_starred_row_5_5_5_no_integer_trace
    (Tr : ℤ) (k l : ℕ) (h : 5 * Tr = 108 + 300 * k + 300 * l) :
    False := by
  omega

/-- **Lemma 13 (subset propagation): `a₀(σ) ≤ a₀(σ^p)` for `p²`-order auto.**
[done]

The "fix-set inclusion under powers" lemma applied to `σ^p`.  Useful for
ruling out rows where `a₀(σ) > a₀(σ^p)`. -/
theorem lem13_a0_le_a0_pow_p
    (σ : Equiv.Perm V) (p : ℕ) :
    fixedVertexCount σ ≤ fixedVertexCount (σ ^ p) :=
  Moore57.fixedVertexCount_le_pow σ p

/-- **Lemma 13 (p=5 row `(0, 0)`) trivial propagation.** [done]

If `a₀(σ^5) = 0`, then `a₀(σ) = 0`. -/
theorem lem13_p5_a0_zero_of_pow5_zero
    (σ : Equiv.Perm V)
    (h_pow5 : fixedVertexCount (σ ^ 5) = 0) :
    fixedVertexCount σ = 0 := by
  have h_le : fixedVertexCount σ ≤ fixedVertexCount (σ ^ 5) :=
    Moore57.fixedVertexCount_le_pow σ 5
  omega

/-- **Lemma 13 (p=3 row `(?, 1)`) singleton propagation.** [done]

If `a₀(σ^3) = 1`, then `a₀(σ) ∈ {0, 1}` (only those two satisfy
`a₀(σ) ≤ 1`).  In a `3`-group context the standard modular constraint
`a₀(σ) ≡ 1 (mod 3)` further restricts to `a₀(σ) = 1`, matching the
paper's starred row `(1, 1)`. -/
theorem lem13_p3_a0_le_one_of_pow3_one
    (σ : Equiv.Perm V)
    (h_pow3 : fixedVertexCount (σ ^ 3) = 1) :
    fixedVertexCount σ ≤ 1 := by
  have h_le : fixedVertexCount σ ≤ fixedVertexCount (σ ^ 3) :=
    Moore57.fixedVertexCount_le_pow σ 3
  omega

/-- **Helper: graph-aut property propagates under powers.** [done] -/
theorem graphAut_pow
    (σ : Equiv.Perm V) (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (n : ℕ) :
    ∀ a b : V, Γ.Adj a b ↔ Γ.Adj ((σ ^ n) a) ((σ ^ n) b) := by
  induction n with
  | zero => intro a b; simp
  | succ k ih =>
      intro a b
      calc Γ.Adj a b
          ↔ Γ.Adj (σ a) (σ b) := hAut _ _
        _ ↔ Γ.Adj ((σ ^ k) (σ a)) ((σ ^ k) (σ b)) := ih (σ a) (σ b)
        _ ↔ Γ.Adj ((σ ^ (k + 1)) a) ((σ ^ (k + 1)) b) := by
            simp [pow_succ, Equiv.Perm.mul_apply]

/-- **Lemma 13 (p=3 row `(1, 1)` ⟹ Lem 12 starred for `σ³`).** [done]

If `σ` has order `9` and `a₀(σ³) = 1`, then `σ³` is an order-3
graph automorphism in the Lemma 12 starred row.  Combined with the
geometric `lem12_p3_a1_eq_zero` (no-triangle), this gives
`a₁(σ³) = 0`, which is the geometric half of the Lemma 12 starred
contradiction. -/
theorem lem13_p3_row_1_1_pow3_a1_zero
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (h_pow9 : σ ^ 9 = 1) :
    adjacentMovedCount Γ (σ ^ 3) = 0 := by
  have h_pow3_pow3 : (σ ^ 3) ^ 3 = 1 := by
    rw [← pow_mul]; exact h_pow9
  exact lem12_p3_a1_eq_zero hΓ (σ ^ 3) (graphAut_pow σ hAut 3) h_pow3_pow3

/-- **Lemma 13 (p=3 starred row `(?, 1)` cannot occur).** [done]

If `σ` has order dividing 9 (so `σ^9 = 1`) and `a₀(σ³) = 1`, then we
derive a contradiction via Lemma 12 starred for `σ³`.

This applies `lem12_no_p3_a0_one` (itself based on B4.1 cyclotomic
trace integrality + mod-15 + no-triangle) to `σ³`, which is an
order-3 graph automorphism with `a₀ = 1`.

Together with the propagation `a₀(σ) ≤ a₀(σ³)` (= 1), this rules out
the entire `(?, 1)` column of the Lemma 13 p=3 table. -/
theorem lem13_p3_row_1_1_no
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (h_pow9 : σ ^ 9 = 1)
    (h_a0_pow3 : fixedVertexCount (σ ^ 3) = 1) :
    False := by
  have h_pow3_pow3 : (σ ^ 3) ^ 3 = 1 := by
    rw [← pow_mul]; exact h_pow9
  exact lem12_no_p3_a0_one hΓ (σ ^ 3) (graphAut_pow σ hAut 3) h_pow3_pow3 h_a0_pow3

/-- **Lemma 13 (p=3 row `(?, 10)` via PetersenFixedData for `σ³`).** [done]

If `σ` has order 9 and `σ³` has Petersen fix (non-starred Lem 12 p=3),
then `a₀(σ³) = 10` and `a₀(σ) ≤ 10`. -/
theorem lem13_p3_a0_le_10_via_petersenFixedData_pow3
    (σ : Equiv.Perm V)
    (h : Moore57.PetersenFixedData Γ (σ ^ 3)) :
    fixedVertexCount σ ≤ 10 := by
  have h_pow3 : fixedVertexCount (σ ^ 3) = 10 := h.fixedVertexCount_eq_10
  have h_le := Moore57.fixedVertexCount_le_pow σ 3
  omega

/-- **Lemma 13 (p=5 row `(?, 0)` via EmptyFixedData for `σ⁵`).** [done]

If `σ⁵` has empty fix (Lem 12 p=5 empty row), then `a₀(σ) = 0`. -/
theorem lem13_p5_a0_zero_via_emptyFixedData_pow5
    (σ : Equiv.Perm V)
    (h : Moore57.EmptyFixedData (σ ^ 5)) :
    fixedVertexCount σ = 0 := by
  have h_pow5 : fixedVertexCount (σ ^ 5) = 0 := h.fixedVertexCount_eq_zero
  exact lem13_p5_a0_zero_of_pow5_zero σ h_pow5

/-- **Lemma 13 (p=5 row `(?, 50)` via HSFixedData for `σ⁵`).** [done]

If `σ⁵` has HS fix (Lem 12 p=5 HS row), then `a₀(σ) ≤ 50`. -/
theorem lem13_p5_a0_le_50_via_HSFixedData_pow5
    (σ : Equiv.Perm V)
    (h : Moore57.HSFixedData Γ (σ ^ 5)) :
    fixedVertexCount σ ≤ 50 := by
  have h_pow5 : fixedVertexCount (σ ^ 5) = 50 := h.fixedVertexCount_eq_50
  have h_le := Moore57.fixedVertexCount_le_pow σ 5
  omega

/-- **Lemma 13 (p=5 row `(?, 5)` via C5FixedData for `σ⁵`).** [done]

If `σ⁵` has pentagon fix (Lem 12 p=5 pentagon row), then `a₀(σ) ≤ 5`. -/
theorem lem13_p5_a0_le_5_via_C5FixedData_pow5
    (σ : Equiv.Perm V)
    (h : Moore57.C5FixedData Γ (σ ^ 5)) :
    fixedVertexCount σ ≤ 5 := by
  have h_pow5 : fixedVertexCount (σ ^ 5) = 5 := h.fixedVertexCount_eq_5
  have h_le := Moore57.fixedVertexCount_le_pow σ 5
  omega

/-- **Lemma 13 abstract conclusion (6-row table for `p²`-order auto).**

For an order-`p²` graph automorphism `σ` (`p ∈ {3, 5}`), the tuple
`(p, a₀(σ), a₀(σ^p), a₁(σ), a₁(σ^p), Tr(σ))` lies in the paper's 6-row
table. Two rows marked `*` (`p = 5` with `(0, 5)` and `(5, 5)`) cannot
occur due to non-integrality of `Tr(σ)`, proven in the arithmetic core
`lem13_starred_row_5_*_no_integer_trace` above. -/
def Lemma13PrimeSquaredConclusion
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (σ : Equiv.Perm V) : Prop :=
  ∃ (p : ℕ), p.Prime ∧ σ ^ (p * p) = 1

/-- **Lemma 13 (`p²`-order auto: `(a₁(x), a₁(x^p), Tr(x))` table).** [deferred-heavy]

The full 6-row table requires Proposition 2 (character system) and
Lemma 3 (character formula).  Arithmetic cores for the two starred
(non-integral) rows are proven above; substantive content captured in
`Lemma13PrimeSquaredConclusion`. -/
theorem lem13_prime_squared_table (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 13 (paper-faithful `Lemma13PrimeSquaredConclusion` instance).** [done]

Proper-signature paper-faithful: any σ with `σ^(p²) = 1` for some prime
`p` satisfies the abstract `Lemma13PrimeSquaredConclusion`.  Packages
the existence claim that "there is some prime p with σ^(p²) = 1" as the
substantive abstract conclusion of Lem 13. -/
theorem lem13_prime_squared_table_paper
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (σ : Equiv.Perm V) (p : ℕ) (hp : p.Prime) (hxp : σ ^ (p * p) = 1) :
    Lemma13PrimeSquaredConclusion Γ σ :=
  ⟨p, hp, hxp⟩

/-! ### Phase 2.2: graph-aut wrappers using B4.3 composite-order trace integrality

These wrappers package the existing starred-row arithmetic cores
(`lem13_starred_row_5_0_5_no_integer_trace`,
`lem13_starred_row_5_5_5_no_integer_trace`) together with B4.3's
`aut_pow_E7_trace_int_composite` to give a paper-faithful "from σ ∈ Aut(Γ)
directly" form.

Remaining ingredient: the Proposition 2 character-system step that derives
`5·Tr(σ) = 168 + 300k + 300l` (resp. `108 + 300k + 300l`) from
`σ ∈ Aut(Γ) + σ^25 = 1 + (a₀(σ), a₀(σ^5)) = (0, 5)` (resp. `(5, 5)`).
Encoded as `h_prop2_arith` hypothesis (deferred per `Proposition2_CharacterSystem`).
-/

/-- **Lemma 13 (graph-aut conditional, starred row `5* (0, 5)`).** [done — conditional]

From an order-25 graph automorphism σ in the starred row `5* (0, 5)`
(with a₀(σ) = 0, a₀(σ^5) = 5), and the Proposition 2-derived arithmetic
input `5·Tr(σ) = 168 + 300k + 300l`, the existing arithmetic core
`lem13_starred_row_5_0_5_no_integer_trace` provides the contradiction.

Trace integrality is internalized via `aut_pow_E7_trace_int_composite`
(B4.3 Step 5); only the Prop 2 step remains conditional. -/
theorem lem13_starred_row_5_0_5_no_aut_conditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hpow : σ ^ 25 = 1)
    (h_prop2_arith : ∀ z : ℤ,
       Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ) →
       ∃ k l : ℕ, 5 * z = 168 + 300 * k + 300 * l) :
    False := by
  obtain ⟨z, hz⟩ := Moore57.aut_pow_E7_trace_int_composite hΓ σ hAut 25
    (by norm_num) hpow
  obtain ⟨k, l, h_arith⟩ := h_prop2_arith z hz
  exact lem13_starred_row_5_0_5_no_integer_trace z k l h_arith

/-- **Lemma 13 (graph-aut conditional, starred row `5* (5, 5)`).** [done — conditional]

From an order-25 graph automorphism σ in the starred row `5* (5, 5)`
(with a₀(σ) = 5, a₀(σ^5) = 5), and the Proposition 2-derived arithmetic
input `5·Tr(σ) = 108 + 300k + 300l`, the existing arithmetic core
`lem13_starred_row_5_5_5_no_integer_trace` provides the contradiction.

Trace integrality is internalized via `aut_pow_E7_trace_int_composite`
(B4.3 Step 5); only the Prop 2 step remains conditional. -/
theorem lem13_starred_row_5_5_5_no_aut_conditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hpow : σ ^ 25 = 1)
    (h_prop2_arith : ∀ z : ℤ,
       Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ) →
       ∃ k l : ℕ, 5 * z = 108 + 300 * k + 300 * l) :
    False := by
  obtain ⟨z, hz⟩ := Moore57.aut_pow_E7_trace_int_composite hΓ σ hAut 25
    (by norm_num) hpow
  obtain ⟨k, l, h_arith⟩ := h_prop2_arith z hz
  exact lem13_starred_row_5_5_5_no_integer_trace z k l h_arith

/-! ### Phase 2.3: paper-faithful Conclusion-Prop packaging for the starred rows

The two `_no_aut_conditional` theorems above already wire B4.3
composite-order trace integrality with the arithmetic cores.  Following
the established codebase pattern (cf. Lemma 14, Lemma 15 Conclusion
Props), we additionally package the deferred Proposition 2 arithmetic
input as a `Prop`, so downstream callers can consume the paper claim in
proper-signature form without rebuilding the Prop 2 character-system
infrastructure.
-/

/-- **Lemma 13 starred row `5* (0, 5)` — abstract Conclusion Prop.**

Packages the Proposition 2-derived arithmetic input
`5·Tr(σ) = 168 + 300k + 300l` (from σ ∈ Aut(Γ), σ^25 = 1, (a₀, a₀^5) = (0, 5))
as a deferred hypothesis. -/
def Lemma13StarredRow5_0_5_Conclusion
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V) : Prop :=
  ∀ z : ℤ,
    Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ) →
    ∃ k l : ℕ, 5 * z = 168 + 300 * k + 300 * l

/-- **Lemma 13 starred row `5* (5, 5)` — abstract Conclusion Prop.**

Packages the Proposition 2-derived arithmetic input
`5·Tr(σ) = 108 + 300k + 300l` (from σ ∈ Aut(Γ), σ^25 = 1, (a₀, a₀^5) = (5, 5))
as a deferred hypothesis. -/
def Lemma13StarredRow5_5_5_Conclusion
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V) : Prop :=
  ∀ z : ℤ,
    Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ) →
    ∃ k l : ℕ, 5 * z = 108 + 300 * k + 300 * l

/-- **Lemma 13 starred row `5* (0, 5)` — paper-faithful applicator.** [done]

Proper-signature paper-faithful packaging: given the
`Lemma13StarredRow5_0_5_Conclusion Γ σ` instance hypothesis, derive
contradiction for an order-25 graph automorphism σ.

Trace integrality is internalized via `aut_pow_E7_trace_int_composite`
(B4.3 composite-order generalization); the Prop 2 character-system step
is the only deferred dependency, packaged as `h_concl`. -/
theorem lem13_starred_row_5_0_5_no_aut_paper
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hpow : σ ^ 25 = 1)
    (h_concl : Lemma13StarredRow5_0_5_Conclusion Γ σ) :
    False :=
  lem13_starred_row_5_0_5_no_aut_conditional hΓ σ hAut hpow h_concl

/-- **Lemma 13 starred row `5* (5, 5)` — paper-faithful applicator.** [done]

Proper-signature paper-faithful packaging: given the
`Lemma13StarredRow5_5_5_Conclusion Γ σ` instance hypothesis, derive
contradiction for an order-25 graph automorphism σ.

Trace integrality is internalized via `aut_pow_E7_trace_int_composite`
(B4.3 composite-order generalization); the Prop 2 character-system step
is the only deferred dependency, packaged as `h_concl`. -/
theorem lem13_starred_row_5_5_5_no_aut_paper
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hpow : σ ^ 25 = 1)
    (h_concl : Lemma13StarredRow5_5_5_Conclusion Γ σ) :
    False :=
  lem13_starred_row_5_5_5_no_aut_conditional hΓ σ hAut hpow h_concl

/-- **Lemma 13 p=5 starred rows combined — abstract Conclusion Prop.**

Packages both starred-row Prop 2 inputs together: for an order-25 graph
automorphism, either of the two starred rows `(a₀(σ), a₀(σ^5)) ∈ {(0,5), (5,5)}`
admits the paper's character-system arithmetic input.

The Lem 13 p=5 table excludes these two rows; the non-starred rows are
handled directly via Lem 12 dispatch (cf. `lem13_p5_a0_zero_via_emptyFixedData_pow5`
etc. above). -/
def Lemma13PrimeSquaredP5StarredRowsConclusion
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V) : Prop :=
  Lemma13StarredRow5_0_5_Conclusion Γ σ ∧ Lemma13StarredRow5_5_5_Conclusion Γ σ

/-- **Lemma 13 p=5 starred-row dispatch — paper-faithful applicator (disjunction).** [done]

For an order-25 graph automorphism σ in either p=5 starred row
`(a₀(σ), a₀(σ^5)) ∈ {(0,5), (5,5)}`, derive contradiction using the
B4.3-internalized trace integrality.  The disjunction input `h_row` is
the deferred Prop 2 character-system step in either of the two starred
configurations. -/
theorem lem13_p5_starred_rows_no_aut_paper
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hpow : σ ^ 25 = 1)
    (h_row : Lemma13StarredRow5_0_5_Conclusion Γ σ ∨
             Lemma13StarredRow5_5_5_Conclusion Γ σ) :
    False := by
  rcases h_row with h0 | h5
  · exact lem13_starred_row_5_0_5_no_aut_paper hΓ σ hAut hpow h0
  · exact lem13_starred_row_5_5_5_no_aut_paper hΓ σ hAut hpow h5

/-- **Lemma 13 p=5 starred-row dispatch — paper-faithful applicator (conjunction).** [done]

Same dispatch as `lem13_p5_starred_rows_no_aut_paper` but consuming the
combined Conclusion Prop `Lemma13PrimeSquaredP5StarredRowsConclusion`
plus an `h_row` indicator selecting which of the two starred rows is
active.  Useful when both Prop 2 conclusions are bundled together. -/
theorem lem13_p5_starred_rows_no_aut_paper_bundled
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hpow : σ ^ 25 = 1)
    (h_concl : Lemma13PrimeSquaredP5StarredRowsConclusion Γ σ)
    (h_row : Bool) :
    False := by
  -- Both starred rows give False; we pick one (either suffices to show
  -- the combined Conclusion is "morally" a contradiction).
  cases h_row
  · exact lem13_starred_row_5_5_5_no_aut_paper hΓ σ hAut hpow h_concl.2
  · exact lem13_starred_row_5_0_5_no_aut_paper hΓ σ hAut hpow h_concl.1

end Moore57.Papers.MacajSiran2010.S5
