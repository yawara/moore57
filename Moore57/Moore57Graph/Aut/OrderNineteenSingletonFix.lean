import Moore57.Moore57Graph.Aut.SingletonAndEmptyFixedData
import Moore57.Moore57Graph.Aut.FixedCount

/-!
# Construction of `SingletonFixedData` for an order-19 Moore57 automorphism

Paper-reference: Mačaj–Širáň 2010, §6, Lemma 19 case (2).

> Let `p > 5` be a prime and let `X` be a group of automorphisms of Γ of
> order `p^k`.  Case (2) of Lemma 19 asserts `Fix(X)` is a singleton and
> `X ≅ Z₁₉`.

For an automorphism `σ : Equiv.Perm V` of a Moore57 graph with `σ^19 = 1`
and `σ ≠ 1`, the *paper-asserted* shape of Fix is a singleton:
`Fix(σ) = {v}`.  This file provides the **constructor**
`aut_order_nineteen_SingletonFixedData` that, given the geometric
fix-singleton fact `fixedVertexCount σ = 1`, packages it as a
`SingletonFixedData σ` structure (the input expected by the §6 Lem 19
case (2) chain).

## Status: fully unconditional

Unlike the order-13 case (which still needs `fixedVertexCount σ = 0` as a
hypothesis because the shape-classification chain is not yet in place),
the **order-19 case is fully unconditional**: the upstream theorem
`order19_aut_fixedVertexCount_eq_one`
(`Moore57.Moore57Graph.Aut.FixedCount`) discharges `fixedVertexCount σ = 1`
directly from `σ^19 = 1 ∧ σ ≠ 1 ∧ smul_adj`.  Hence the constructor
`aut_order_nineteen_SingletonFixedData` is on the same "unconditional"
footing as `aut_order_eleven_C5FixedData` (for the pentagon case).

## Design parallel

| File                              | Output              | Status         |
|-----------------------------------|---------------------|----------------|
| `OrderElevenIsC5.lean`            | `C5FixedData`       | unconditional  |
| `OrderNineteenSingletonFix.lean`  | `SingletonFixedData`| unconditional  |
| `OrderThirteenEmptyFix.lean`      | `EmptyFixedData`    | conditional    |

The Lem 19 case (2) chain consumes the `SingletonFixedData σ` output and
feeds it into:

1. `singleton_orderOf_dvd_57_of_semiRegular` (C3.4 bridge on `N(v) \ {v}`),
2. `lem19_case2_orderOf_dvd_19_of_singleton_fix` (arithmetic core,
   `19^k ∣ 57 ⟹ 19^k ∈ {1, 19}`),

giving the paper-faithful Lem 19 case (2) conclusion `orderOf σ ∣ 19`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Constructor for `SingletonFixedData` from `fixedVertexCount σ = 1` -/

/-- **SingletonFixedData from fix-singleton count.** [done]

Given any permutation `σ : Equiv.Perm V` whose σ-fixed-vertex count is
`1`, construct the canonical `SingletonFixedData σ` structure.  The
unique fixed vertex `v`, its σ-fixedness `σ v = v`, and the uniqueness
property `∀ x, σ x = x → x = v` are all read off from the standard
Finset-cardinality characterization (`fixedVertexCount σ = 1` ↔ the
σ-fixed Finset is a singleton).

This is the underlying constructor used by
`aut_order_nineteen_SingletonFixedData` (specialised to `σ^19 = 1` plus
the 19-prime fix-singleton fact). -/
noncomputable def singletonFixedData_of_fixedVertexCount_eq_one
    (σ : Equiv.Perm V) (h_count : fixedVertexCount σ = 1) :
    SingletonFixedData σ := by
  classical
  -- Extract the singleton finset from `fixedVertexCount σ = 1`.
  have hsingleton :
      ∃ v : V, ((Finset.univ : Finset V).filter (fun w => σ w = w)) = {v} := by
    rw [fixedVertexCount] at h_count
    exact Finset.card_eq_one.mp h_count
  -- Use `Classical.choose` since we need `Type`-level data, not propositional cases.
  let v : V := hsingleton.choose
  have hv : ((Finset.univ : Finset V).filter (fun w => σ w = w)) = {v} :=
    hsingleton.choose_spec
  refine
    { v := v
      v_fixed := ?_
      span := ?_ }
  · -- σ v = v: read off from `v ∈ filter (σ w = w)`.
    have hmem : v ∈ ((Finset.univ : Finset V).filter (fun w => σ w = w)) := by
      rw [hv]; exact Finset.mem_singleton.mpr rfl
    exact (Finset.mem_filter.mp hmem).2
  · -- Uniqueness: if `σ x = x` then `x ∈ filter (σ w = w) = {v}`.
    intro x hx
    have hmem : x ∈ ((Finset.univ : Finset V).filter (fun w => σ w = w)) := by
      simp [hx]
    rw [hv, Finset.mem_singleton] at hmem
    exact hmem

/-! ### Lemma 19 case (2) input: `SingletonFixedData` from `σ^19 = 1`

The constructor `aut_order_nineteen_SingletonFixedData` is the §6 Lem 19
case (2) data-packaging step: given a `σ^19 = 1, σ ≠ 1` Moore57 graph
automorphism, produce the `SingletonFixedData σ` structure that feeds
into the C3.4 semi-regular bridge (giving `orderOf σ ∣ 57`) and onward
to the arithmetic core (giving `orderOf σ ∣ 19`).

Unlike the parallel `aut_order_thirteen_EmptyFixedData`, no
`fixedVertexCount σ = 1` hypothesis is required — the upstream theorem
`order19_aut_fixedVertexCount_eq_one` discharges it unconditionally from
`σ^19 = 1 ∧ σ ≠ 1 ∧ smul_adj`. -/

/-- **Lem 19 case (2) `SingletonFixedData` constructor (fully unconditional).** [done]

Given:
* `hΓ : IsMoore57 Γ` (the host graph is a Moore57 graph),
* `σ : Equiv.Perm V` with `σ^19 = 1` and `σ ≠ 1`,
* `smul_adj` (σ is a graph automorphism),

produce `SingletonFixedData σ`.  This mirrors
`aut_order_eleven_C5FixedData` (pentagon case): the underlying
`fixedVertexCount σ = 1` fact is supplied by the unconditional theorem
`order19_aut_fixedVertexCount_eq_one`, so no extra fix-shape hypothesis
is needed. -/
noncomputable def aut_order_nineteen_SingletonFixedData
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_nineteen : σ ^ 19 = 1) (hne : σ ≠ 1) :
    SingletonFixedData σ :=
  singletonFixedData_of_fixedVertexCount_eq_one σ
    (order19_aut_fixedVertexCount_eq_one hΓ σ smul_adj pow_nineteen hne)

/-- **Lem 19 case (2) input bound: `fixedVertexCount σ ≡ 1 [MOD 19]`.** [done]

Re-export of `aut_fixedVertexCount_modEq_one_of_pow_nineteen_pow` for
the prime case (`k = 1`).  Used as the modular ingredient in the
unconditional Path B chain for case (2). -/
theorem aut_order_nineteen_fixedVertexCount_modEq_one
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (pow_nineteen : σ ^ 19 = 1) :
    fixedVertexCount σ ≡ 1 [MOD 19] := by
  have h_pow_pow : σ ^ (19 : ℕ) ^ 1 = 1 := by simpa using pow_nineteen
  exact aut_fixedVertexCount_modEq_one_of_pow_nineteen_pow hΓ σ 1 h_pow_pow

/-- **Lem 19 case (2) `SingletonFixedData` via small fix-count.** [done]

If `fixedVertexCount σ ≤ 19`, the mod-19 constraint
`fixedVertexCount σ ≡ 1 [MOD 19]` forces `fixedVertexCount σ = 1`, and
the `SingletonFixedData` constructor applies (via
`singletonFixedData_of_fixedVertexCount_eq_one`, without invoking the
heavier `order19_aut_fixedVertexCount_eq_one`).  Mirrors the §6 Lem 16
case (2) `lem16_case2_19group_fix_singleton_if_small` shape-narrowing.

Note: this variant does not require `σ ≠ 1` (the `≤ 19` hypothesis already
prevents the trivial case where `Fix = V`). -/
noncomputable def aut_order_nineteen_SingletonFixedData_of_small_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (pow_nineteen : σ ^ 19 = 1)
    (h_small : fixedVertexCount σ ≤ 19) :
    SingletonFixedData σ := by
  have h_count_one : fixedVertexCount σ = 1 := by
    have hmod := aut_order_nineteen_fixedVertexCount_modEq_one hΓ σ pow_nineteen
    rw [Nat.ModEq] at hmod
    omega
  exact singletonFixedData_of_fixedVertexCount_eq_one σ h_count_one

end Moore57
