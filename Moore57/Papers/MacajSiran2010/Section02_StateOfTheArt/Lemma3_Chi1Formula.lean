import Moore57.Moore57Graph.HigmanTrace.Congruence

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Lemma 3

> For any `x ∈ X`,
> ```
> χ₁(x) = (1/15)(8 a₀(x) + a₁(x) − 65),
> a₁(x) ≡ 7 a₀(x) + 5  (mod 15).
> ```

* `lem3_chi1_formula` — wrapped from `IsMoore57.higman_trace_formula`
  with `χ₁(x) := trace(E_7 · P_σ)`.
* `lem3_a1_mod_15` — wrapped from `IsMoore57.higman_trace_int_intModEq`,
  parameterized by the integer value of the trace (corresponding to the
  paper's "χ₁(x) is an algebraic integer, hence integer" step).
-/

open Moore57

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 3 (χ₁ formula).**
`χ₁(σ) := trace(E_7 · P_σ) = (1/15)(8 a₀(σ) + a₁(σ) − 65)`. -/
theorem lem3_chi1_formula (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    Matrix.trace (E7Matrix Γ * permMatrix σ) =
      (8 * (fixedVertexCount σ : ℚ) + (adjacentMovedCount Γ σ : ℚ) - 65) / 15 :=
  hΓ.higman_trace_formula σ

/-- **Lemma 3 (mod-15 congruence).**
Once `χ₁(σ)` is known to be an integer `z`, we get `a₁(σ) ≡ 7 a₀(σ) + 5 (mod 15)`. -/
theorem lem3_a1_mod_15 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    {z : ℤ} (hz : Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ)) :
    (adjacentMovedCount Γ σ : ℤ) ≡ 7 * (fixedVertexCount σ : ℤ) + 5 [ZMOD 15] :=
  hΓ.higman_trace_int_intModEq σ hz

end Moore57.Papers.MacajSiran2010.S2
