import Moore57.Moore57Graph.Aut.OrderThreeCandidates
import Moore57.Moore57Graph.Aut.SingletonAndEmptyFixedData
import Moore57.Moore57Graph.Aut.PetersenFixedData
import Moore57.Moore57Graph.Aut.OrderNineteenSingletonFix

/-!
# Shape classification for an order-3 Moore57 automorphism (Tier 3)

Paper-reference: Mačaj–Širáň 2010, §6, Lemma 17.

> Let `X` be a 3-group of automorphisms of Γ.  Then either
> (1) `Fix(X)` is isomorphic to the Petersen graph, or
> (2) `Fix(X)` is a singleton.

For the prime case `σ^3 = 1, σ ≠ 1`, this file packages the dichotomy
output by `OrderThreeCandidates.lean` (`|Fix(σ)| ∈ {1, 10}`) into a
**proof-relevant** disjunction:

* `SingletonFixedData σ` (case (2) input), **or**
* a "Petersen-shape SRG witness": `|Fix(σ)| = 10` *and* the σ-fixed
  induced subgraph is `IsSRGWith 10 3 0 1`.

The latter is the SRG signature of the Petersen graph but **not** the
explicit `PetersenFixedData` (which additionally requires identifying
the 10 vertices via `Fin 10` matching the explicit `petersenGraph`
adjacency).  Promoting `IsSRGWith 10 3 0 1` to `PetersenFixedData`
requires the Petersen uniqueness theorem ("the unique SRG(10, 3, 0, 1)
up to isomorphism is the Petersen graph"), which is a separate
formalization step (not in scope here).

## Status

* `aut_order_three_SingletonOrPetersenSRG_unconditional`:
  fully unconditional; the existence of one of the two branches follows
  directly from `aut_order_three_fixedVertexCount_singleton_or_petersenSRG`
  combined with `singletonFixedData_of_fixedVertexCount_eq_one`.
* `aut_order_three_SingletonFixedData_of_fixedVertexCount_eq_one`:
  the conditional case-(2) constructor (count ≤ 1 implies `count = 1`
  via `|Fix| > 0`, then `SingletonFixedData`).
* `aut_order_three_SingletonFixedData_of_lt_10`: a useful narrowing
  ("if `|Fix| < 10`, we're in case (2)") consumed by the §6 Lem 17
  arithmetic dispatch.

## Forward link to §6 Lem 17

The arithmetic step (Lem 17 case (2)): `orderOf σ ∣ 57` (from
`SingletonFixedData` + C3.4 semi-regular bridge) combined with
`σ^3 = 1` gives `orderOf σ ∣ gcd(3, 57) = 3`.

The arithmetic step (Lem 17 case (1)): `orderOf σ ∣ 54` (from
`PetersenFixedData` + C3.4 semi-regular bridge) combined with
`σ^3 = 1` gives `orderOf σ ∣ gcd(3, 54) = 3`.

Hence both branches give `orderOf σ ∣ 3` for the prime case, which is
of course immediate from `σ^3 = 1`.  The full §6 Lem 17 statement
(`|X| ∣ 27` for 3-groups in case (1) / `|X| ∣ 3` in case (2)) requires
the prime-power generalization, which is a separate lift.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Singleton (case 2) constructors -/

/-- **Singleton (case 2) from `|Fix| = 1`** [done]

For `σ : Equiv.Perm V` with `fixedVertexCount σ = 1`, the
`SingletonFixedData σ` structure is produced via the underlying
`singletonFixedData_of_fixedVertexCount_eq_one` constructor.

Reuse of the order-19 case-(2) constructor; the dependency on `σ^19 = 1`
is purely cosmetic in that constructor (only the count matters). -/
noncomputable def aut_order_three_SingletonFixedData_of_fixedVertexCount_eq_one
    (σ : Equiv.Perm V) (h_count : fixedVertexCount σ = 1) :
    SingletonFixedData σ :=
  singletonFixedData_of_fixedVertexCount_eq_one σ h_count

/-! ### Two-way classification: SingletonFixedData ∨ Petersen-SRG -/

/-- **Unconditional Lem 17 dichotomy (prime case)**: [done]

Given:
* `hΓ : IsMoore57 Γ`,
* `σ : Equiv.Perm V` with `σ^3 = 1` and `σ ≠ 1`,
* `smul_adj` (σ is a graph automorphism),

either
* `SingletonFixedData σ` (case (2)), or
* `|Fix(σ)| = 10` *and* the σ-fixed induced graph is `IsSRGWith 10 3 0 1`
  (case (1), Petersen-SRG signature).

The output is a `Sum`/`Or` of the two case-data records.  No
hypothesis on `|Fix(σ)|` is required. -/
noncomputable def aut_order_three_SingletonOrPetersenSRG_unconditional
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_three : σ ^ 3 = 1) (hne : σ ≠ 1) :
    SingletonFixedData σ ⊕'
      (PLift (fixedVertexCount σ = 10) ×'
        PLift ((autFixedInducedGraph Γ σ).IsSRGWith 10 3 0 1)) := by
  classical
  -- Use Classical.choice / by_cases on the count to dispatch.
  by_cases h_count_one : fixedVertexCount σ = 1
  · -- Case (2): singleton.
    exact PSum.inl (singletonFixedData_of_fixedVertexCount_eq_one σ h_count_one)
  · -- Otherwise we must be in case (1).  Derive `|Fix| = 10 ∧ SRG(10,3,0,1)`.
    -- Use `Or.resolve_left` to extract the right branch propositionally.
    have hor :=
      aut_order_three_fixedVertexCount_singleton_or_petersenSRG
        hΓ σ smul_adj pow_three hne
    have hpets : fixedVertexCount σ = 10 ∧
        (autFixedInducedGraph Γ σ).IsSRGWith 10 3 0 1 :=
      hor.resolve_left h_count_one
    exact PSum.inr ⟨PLift.up hpets.1, PLift.up hpets.2⟩

/-- **Mod-narrowed dichotomy (prime case)**: [done]

Given `σ^3 = 1, σ ≠ 1`, the σ-fixed-vertex count is *exactly* `1` (case 2)
or `10` (case 1).  This is a thin re-export of
`aut_order_three_fixedVertexCount_eq_one_or_ten` from `OrderThreeCandidates`
specialised as a paper-named dispatch. -/
theorem aut_order_three_fixedVertexCount_singleton_or_petersen
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_three : σ ^ 3 = 1) (hne : σ ≠ 1) :
    fixedVertexCount σ = 1 ∨ fixedVertexCount σ = 10 :=
  aut_order_three_fixedVertexCount_eq_one_or_ten hΓ σ smul_adj pow_three hne

/-! ### Singleton (case 2) narrowing via small fix-count -/

/-- **Singleton-case narrowing via `|Fix| < 10`**: [done]

For `σ^3 = 1, σ ≠ 1` on Moore57 with `|Fix(σ)| < 10`, the dichotomy
forces `|Fix| = 1` (singleton case), and the `SingletonFixedData`
constructor applies. -/
noncomputable def aut_order_three_SingletonFixedData_of_lt_10
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_three : σ ^ 3 = 1) (hne : σ ≠ 1)
    (h_small : fixedVertexCount σ < 10) :
    SingletonFixedData σ := by
  have hdich :=
    aut_order_three_fixedVertexCount_singleton_or_petersen
      hΓ σ smul_adj pow_three hne
  have h_count_one : fixedVertexCount σ = 1 := by
    rcases hdich with h1 | h10
    · exact h1
    · omega
  exact singletonFixedData_of_fixedVertexCount_eq_one σ h_count_one

/-- **Petersen-SRG case narrowing via `|Fix| ≥ 10`** (or equivalently `≠ 1`):
[done]

For `σ^3 = 1, σ ≠ 1` on Moore57 with `|Fix(σ)| ≠ 1`, the dichotomy
forces `|Fix| = 10` and the σ-fixed induced graph is `IsSRGWith 10 3 0 1`. -/
theorem aut_order_three_petersenSRG_of_ne_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_three : σ ^ 3 = 1) (hne : σ ≠ 1)
    (h_ne1 : fixedVertexCount σ ≠ 1) :
    fixedVertexCount σ = 10 ∧
      (autFixedInducedGraph Γ σ).IsSRGWith 10 3 0 1 := by
  rcases aut_order_three_fixedVertexCount_singleton_or_petersenSRG
    hΓ σ smul_adj pow_three hne with h1 | hpets
  · exact absurd h1 h_ne1
  · exact hpets

/-! ### `orderOf σ ∣ 3` (paper Lem 17 prime case conclusion)

Both branches of Lem 17 deliver `orderOf σ ∣ 3` for the prime case
`σ^3 = 1`.  This follows trivially from `σ^3 = 1` itself, without the
SRG/Petersen machinery.  The shape classification above is the
prerequisite for the *prime-power* `σ^(3^k) = 1` lift, where the
arithmetic narrowing `orderOf σ ∣ 54 → 27` (Petersen) or
`orderOf σ ∣ 57 → 3` (singleton) becomes nontrivial. -/

omit [Fintype V] [DecidableEq V] in
/-- **Lem 17 prime-case `orderOf σ ∣ 3`** [done]

Immediate from `σ^3 = 1` (no SRG/Petersen narrowing required).  This is
the prime-level shadow of the §6 Lem 17 conclusion; the prime-power case
requires the shape classification above plus the C3.4 semi-regular
orbit divisibility. -/
theorem aut_order_three_orderOf_dvd_3
    (σ : Equiv.Perm V) (pow_three : σ ^ 3 = 1) :
    orderOf σ ∣ 3 :=
  orderOf_dvd_of_pow_eq_one pow_three

end Moore57
