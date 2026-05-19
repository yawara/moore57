import Moore57.Moore57Graph.Moore57Definition
import Moore57.Moore57Graph.Aut.FixedCount
import Moore57.Moore57Graph.Aut.OrderElevenIsC5

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Makhnev–Paduchikh 2001, Lemma 3

> Let `X` be a subgroup of odd prime order in `G = Aut(Γ)`. Then one of the
> following holds:
>
> (1) Fix(X) is empty and `|X|` divides `5 · 13`;
>
> (2) `|Fix(X)| = 1` and `|X|` divides `3 · 19`;
>
> (3) Fix(X) is a star, `|Fix(X)| ≥ 2`, and `|X|` divides `7`;
>
> (4) Fix(X) is a pentagon and `|X|` divides `5 · 11`;
>
> (5) Fix(X) is Petersen's graph and `|X|` divides `3`;
>
> (6) Fix(X) is Hoffman–Singleton's graph and `|X|` divides `5`.

Status:
* The full 6-way classification is a skeleton (= Mačaj–Širáň Lem 4, depends
  on the Aschbacher fix-classification).
* Two specific rows are wrapped from existing Moore57 infrastructure:
  - Order 19 (case 2): `lem3_order19_case2`.
  - Order 11 (case 4): `lem3_order11_case4`.
-/

open Moore57

namespace Moore57.Papers.MakhnevPaduchikh2001

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 3 (general 6-way classification).** [deferred-heavy] -/
theorem lem3_odd_prime_fix (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 3, case (2): order 19, `|Fix| = 1`.**
Any order-19 automorphism of Moore57 has exactly one fixed vertex. -/
theorem lem3_order19_case2 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hpow : σ ^ 19 = 1) (hne : σ ≠ 1) :
    fixedVertexCount σ = 1 :=
  order19_aut_fixedVertexCount_eq_one hΓ σ hAut hpow hne

/-- **Lemma 3, case (4): order 11, `|Fix|` is a pentagon (5 vertices).**
Any order-11 automorphism of Moore57 has fixed-vertex set of size 5
(induced subgraph is the pentagon `C₅`). -/
theorem lem3_order11_case4 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hpow : σ ^ 11 = 1) (hne : σ ≠ 1) :
    fixedVertexCount σ = 5 :=
  aut_order_eleven_fixedVertexCount_eq_five hΓ σ hAut hpow hne

end Moore57.Papers.MakhnevPaduchikh2001
