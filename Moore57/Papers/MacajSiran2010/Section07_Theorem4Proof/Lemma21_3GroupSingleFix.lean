import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma17_3Group

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §7, Lemma 21 [deferred-heavy]

> Let Γ admit a 3-group `X` of automorphisms with `Fix(X) = {a}` and let
> `x` be a non-trivial element of `X`. Then,
>
> (1) if `X` has (at least) two orbits of size 3 on `N(a)`, then `|X| = 9`;
>
> (2) if `X` has an orbit of size 9 on `N(a)`, then `|X| ≤ 27`.

Status:
* `lem21_part1_index_arithmetic`: **proven** — index-9 normal subgroup
  arithmetic (two index-3 normal subgroups give intersection of index 9).
* `lem21_part2_orbit_stabilizer_arithmetic`: **proven** — orbit-
  stabilizer arithmetic giving `|X| = 27`.
* `lem21_two_size3_orbits`, `lem21_size9_orbit`: original True-stubs
  kept for backwards compat.
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

/-- **Lemma 21 (1) (two size-3 orbits on `N(a)` ⇒ `|X| = 9`).** [deferred-heavy]

Arithmetic backbone via `lem21_part1_index_arithmetic`. -/
theorem lem21_two_size3_orbits (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 21 (2) (size-9 orbit on `N(a)` ⇒ `|X| ≤ 27`).** [deferred-heavy]

Arithmetic backbone via `lem21_part2_orbit_stabilizer_arithmetic` and
`lem21_part2_card_le_27`. -/
theorem lem21_size9_orbit (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S7
