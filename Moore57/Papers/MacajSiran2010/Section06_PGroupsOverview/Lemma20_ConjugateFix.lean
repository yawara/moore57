import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Lemma 20

> Let `O` be an orbit of an action of a group `X` on a set and let `X_o` be
> a stabilizer of an element `o ∈ O`. Let `Conj(X_o)` be the number of
> conjugates of `X_o` in `X`. Then
> ```
> |Fix(X_o) ∩ O| · Conj(X_o) = |O|.
> ```

This is a general orbit-stabilizer / conjugate counting fact, not specific
to Γ.

## Lean formalization

We use the standard correspondences in Mathlib:

* `|Fix(X_o) ∩ O| = [N_G(X_o) : X_o]` — the orbit-stabilizer theorem
  applied to the `N_G(X_o)`-action on `α`, since `o` is `X_o`-fixed and
  every point in `Fix(X_o) ∩ O` is `n · o` for some `n ∈ N_G(X_o)`.
* `Conj(X_o) = [G : N_G(X_o)]` — orbit-stabilizer for the conjugation
  action of `G` on subgroups.
* `|O| = [G : X_o]` — `MulAction.index_stabilizer`.

The identity then reduces to the tower formula
`[N_G(X_o) : X_o] · [G : N_G(X_o)] = [G : X_o]`, which is
`Subgroup.relIndex_mul_index` applied to `X_o ≤ N_G(X_o)`.
-/

namespace Moore57.Papers.MacajSiran2010.S6

open MulAction Subgroup

variable {G : Type*} [Group G]

/-- **Lemma 20** in its abstract index form: for any subgroup `H` of `G`,
`[N_G(H) : H] · [G : N_G(H)] = [G : H]`.  This is the algebraic core
behind the orbit-conjugate counting identity. -/
theorem lem20_index_form (H : Subgroup G) :
    H.relIndex (normalizer (H : Set G)) * (normalizer (H : Set G)).index = H.index :=
  Subgroup.relIndex_mul_index Subgroup.le_normalizer

/-- **Lemma 20** (Mačaj–Širáň 2010, fix-conjugate orbit count).
For a group `G` acting on a set `α` and any `o : α`,
`[N_G(stab o) : stab o] · [G : N_G(stab o)] = |orbit G o|`.

* `[N_G(stab o) : stab o]` is `|Fix(stab o) ∩ orbit G o|` —
  the size of the `N_G(stab o)`-orbit of `o`, equal to the points in
  `orbit G o` fixed by `stab o`.
* `[G : N_G(stab o)]` is the number of conjugates of `stab o` in `G`.
* `|orbit G o|` is the orbit's cardinality.
-/
theorem lem20_fix_conjugate {α : Type*} [MulAction G α] (o : α) :
    (stabilizer G o).relIndex (normalizer (stabilizer G o : Set G)) *
        (normalizer (stabilizer G o : Set G)).index = (orbit G o).ncard := by
  rw [← MulAction.index_stabilizer]
  exact lem20_index_form (stabilizer G o)

end Moore57.Papers.MacajSiran2010.S6
