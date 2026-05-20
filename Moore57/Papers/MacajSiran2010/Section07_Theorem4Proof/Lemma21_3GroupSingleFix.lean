import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma17_3Group
import Mathlib.GroupTheory.Index

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §7, Lemma 21 [proper-signature subgroup form + deferred-heavy]

> Let Γ admit a 3-group `X` of automorphisms with `Fix(X) = {a}` and let
> `x` be a non-trivial element of `X`. Then,
>
> (1) if `X` has (at least) two orbits of size 3 on `N(a)`, then `|X| = 9`;
>
> (2) if `X` has an orbit of size 9 on `N(a)`, then `|X| ≤ 27`.

Status:
* `lem21_part1_index_arithmetic`: **proven** — index-9 normal subgroup
  arithmetic (two index-3 normal subgroups give intersection of index 9).
* `lem21_part1_subgroup_paper`: **proven** — Mathlib `Subgroup`-API form of
  part (1), packaging the arithmetic via `Subgroup.index_mul_card`.  Takes
  the index-9 of the intersection and `|X₁ ∩ X₂| = 1` as direct hypotheses;
  the residual gap (deriving these from the paper's "≥ 2 orbits of size 3 on
  N(a)" geometric hypothesis) is the paper §6 Lem 21 proof body.
* `lem21_part2_orbit_stabilizer_arithmetic`: **proven** — orbit-
  stabilizer arithmetic giving `|X| = 27`.
* `lem21_part2_subgroup_paper`: **proven** — Mathlib `Subgroup`-API form of
  part (2), packaging the orbit-stabilizer arithmetic chain.
* `lem21_two_size3_orbits`, `lem21_size9_orbit`: original True-stubs
  kept for backwards compat.

## Subgroup-form vs cyclic-form

The paper's Lemma 21 is genuinely about a (possibly non-abelian) 3-group `X`
acting on Γ.  The cyclic specialization `X = ⟨σ⟩` degenerates (in a cyclic
group, every divisor has a *unique* subgroup of that index, so "two distinct
stabilizers of index 3" collapses to one).  Hence the subgroup form below is
the right level of abstraction.

The deferred-heavy gap is constructing the index-9 trivial intersection from
the paper's "every element of `X₁ ∩ X₂` fixes ≥ 6 elements of `N(a)`"
collapse (the geometric content of Lem 21).  Once this is in place,
`lem21_part1_subgroup_paper` becomes an unconditional bridge.
-/

namespace Moore57.Papers.MacajSiran2010.S7

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 21 (1) arithmetic core: index-9 trivial intersection forces
`|X| = 9`.** [done]

If `X1, X2 ◁ X` are normal subgroups of index 3, then their intersection
`X1 ∩ X2` has index dividing 9.  The geometric content of Lemma 21 (1)
(every element of `X1 ∩ X2` fixes ≥ 6 elements of `N(a)`) forces this
intersection to be trivial, so by Lagrange `|X| = 9 · |X1 ∩ X2| = 9`.

The arithmetic package: given `|X| = 9 · |X1 ∩ X2|` (the Lagrange
form) and `|X1 ∩ X2| = 1` (the geometric collapse), conclude
`|X| = 9`. -/
theorem lem21_part1_index_arithmetic
    (X_card int_card : ℕ)
    (h_lagrange : X_card = 9 * int_card)
    (h_int_trivial : int_card = 1) :
    X_card = 9 := by
  rw [h_int_trivial] at h_lagrange
  omega

/-- **Lemma 21 (2) arithmetic core: orbit-stabilizer chain gives `|X| = 27`.**
[done]

For `X` acting on Γ with `|Fix(X)| = {a}` and an orbit `O ⊆ N(a)` of
size 9, the paper's argument produces a chain `X ⊇ X_o ⊇ X_{oo'}` with:
- `[X : X_o] = |O| = 9` (orbit-stabilizer at o ∈ O).
- `[X_o : X_{oo'}] = |o'^{X_o}| = 3` (orbit of o' under X_o).
- `|X_{oo'}| = 1` (geometric collapse, similar to part (1)).

Thus `|X| = 9 · 3 · 1 = 27`.

The arithmetic package: given the index chain and trivial deepest
subgroup, conclude `|X| = 27`. -/
theorem lem21_part2_orbit_stabilizer_arithmetic
    (X_card Xo_card Xoo_card : ℕ)
    (h_X_Xo : X_card = 9 * Xo_card)
    (h_Xo_Xoo : Xo_card = 3 * Xoo_card)
    (h_Xoo_trivial : Xoo_card = 1) :
    X_card = 27 := by
  rw [h_Xoo_trivial] at h_Xo_Xoo
  rw [h_Xo_Xoo] at h_X_Xo
  omega

/-- **Lemma 21 (2) arithmetic bound: `|X| ≤ 27` from index chain.** [done]

A weaker conditional matching the paper's stated bound `|X| ≤ 27`:
if `|X| = 9 · |X_o|` and `|X_o| ≤ 3`, then `|X| ≤ 27`.

(The `|X_o| ≤ 3` factor comes from `[X_o : X_{oo'}] = 3` plus the
non-trivial-stabilizer alternative branch; the cleaner equality form
`|X| = 27` is `lem21_part2_orbit_stabilizer_arithmetic`.) -/
theorem lem21_part2_card_le_27
    (X_card Xo_card : ℕ)
    (h_X_Xo : X_card = 9 * Xo_card)
    (h_Xo_le : Xo_card ≤ 3) :
    X_card ≤ 27 := by
  omega

/-- **Lemma 21 (1) (subgroup form, proper-signature).** [done — arithmetic]

Mathlib `Subgroup`-API form of part (1).  Given a subgroup `X` of any group
`G` and a subgroup `X₁₂ ≤ X` of `X` with `[X : X₁₂] = 9` (the paper's
"intersection of two index-3 normal subgroups") and `|X₁₂| = 1` (the
geometric "every element fixes ≥ 6 elements of `N(a)`" collapse), we have
`|X| = 9` by Lagrange (`Subgroup.index_mul_card`).

The remaining (deferred-heavy) step is constructing the index-9 trivial
subgroup `X₁₂` from the paper's "≥ 2 orbits of size 3 on `N(a)`" geometric
hypothesis.  Once that is in place this becomes an unconditional bridge.

Note: stated for a general group `G` (no graph hypotheses), since the
arithmetic is purely group-theoretic.  The `Equiv.Perm V` specialization
is the intended use case in MS 2010. -/
theorem lem21_part1_subgroup_paper
    {G : Type*} [Group G] (X X₁₂ : Subgroup G)
    (hidx9 : (X₁₂.subgroupOf X).index = 9)
    (hcard1 : Nat.card (X₁₂.subgroupOf X) = 1) :
    Nat.card X = 9 := by
  have h := Subgroup.index_mul_card (X₁₂.subgroupOf X)
  rw [hidx9, hcard1] at h
  omega

/-- **Lemma 21 (2) (subgroup form, proper-signature).** [done — arithmetic]

Mathlib `Subgroup`-API form of part (2): orbit-stabilizer chain gives
`|X| = 27`.  Given `X_o ≤ X` (stabilizer of orbit point `o`) with
`[X : X_o] = 9` (orbit size 9) and `X_oo ≤ X_o` (deeper stabilizer) with
`[X_o : X_oo] = 3` and `|X_oo| = 1`, we have `|X| = 27` by Lagrange. -/
theorem lem21_part2_subgroup_paper
    {G : Type*} [Group G] (X X_o X_oo : Subgroup G)
    (h_Xo_le : X_o ≤ X) (h_Xoo_le : X_oo ≤ X_o)
    (hidx_X_Xo : (X_o.subgroupOf X).index = 9)
    (hidx_Xo_Xoo : (X_oo.subgroupOf X_o).index = 3)
    (hcard_Xoo : Nat.card X_oo = 1) :
    Nat.card X = 27 := by
  have h1 := Subgroup.index_mul_card (X_o.subgroupOf X)
  have h2 := Subgroup.index_mul_card (X_oo.subgroupOf X_o)
  rw [hidx_X_Xo] at h1
  rw [hidx_Xo_Xoo] at h2
  -- `Nat.card (X_o.subgroupOf X) = Nat.card X_o` (since `X_o ≤ X`).
  have h_eq_o : Nat.card (X_o.subgroupOf X) = Nat.card X_o :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h_Xo_le).toEquiv
  have h_eq_oo : Nat.card (X_oo.subgroupOf X_o) = Nat.card X_oo :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h_Xoo_le).toEquiv
  rw [h_eq_o] at h1
  rw [h_eq_oo, hcard_Xoo] at h2
  omega

/-- **Lemma 21 (1) (two size-3 orbits on `N(a)` ⇒ `|X| = 9`).** [deferred-heavy]

Arithmetic backbone via `lem21_part1_index_arithmetic` and the proper-
signature `lem21_part1_subgroup_paper`.  Backward-compat True-stub. -/
theorem lem21_two_size3_orbits (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 21 (2) (size-9 orbit on `N(a)` ⇒ `|X| ≤ 27`).** [deferred-heavy]

Arithmetic backbone via `lem21_part2_orbit_stabilizer_arithmetic`,
`lem21_part2_card_le_27`, and `lem21_part2_subgroup_paper`.
Backward-compat True-stub. -/
theorem lem21_size9_orbit (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S7
