import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Rank and orbital structure for permutation groups

Higman 1964 (Mač–Sir §1) studies rank-3 permutation groups via the
**orbital structure** — the orbits of the diagonal `G`-action on `Ω × Ω`.

Mathlib has the basic `MulAction.orbit` and `MulAction.orbitRel`
machinery, plus the `Prod.mulAction` diagonal action on `Ω × Ω`, but
does **not** package the orbital quotient nor the rank concept.  This
file provides the minimal foundation:

## Main definitions

* `Moore57.orbital G Ω` — quotient of `Ω × Ω` by the diagonal G-action.
* `Moore57.permRank G Ω` — the rank of the action = `|orbital G Ω|`.

## Notes (D1-D2 scope)

This file provides D2.0 (`orbital` + `permRank` definitions).
Subsequent pieces (paired orbital `Δ'(a)`, self-paired criterion,
rank-3 specialisation) are not yet built — they are documented as
future work in `proofs/moore57_roadmap_post_easy_wins.md` §D.
-/

namespace Moore57

variable (G Ω : Type*) [Group G] [MulAction G Ω]

/-- The **orbitals** of a `G`-action on `Ω`: orbits of the diagonal action
on `Ω × Ω`.

In Higman's notation, the orbitals partition `Ω × Ω` into `G`-invariant
relations.  For `Ω = G/H` (a transitive action), the orbital count equals
the number of `(H, H)`-double cosets, also known as the rank of the action. -/
def orbital : Type _ :=
  Quotient (MulAction.orbitRel G (Ω × Ω))

/-- The **rank** of a permutation group action: the number of orbitals
(= orbits of `G` on `Ω × Ω`).

The action is called *rank-3* when this number equals 3, which is the
case Higman 1964 analyses. -/
noncomputable def permRank : ℕ :=
  Nat.card (orbital G Ω)

/-- Convenience alias: two pairs are in the same orbital iff the first lies in
the diagonal-action orbit of the second.

Unfolding through `MulAction.orbitRel_apply` + `MulAction.mem_orbit_iff`:
`SameOrbital G Ω a b ↔ ∃ g : G, g • b = a`. -/
def SameOrbital (a b : Ω × Ω) : Prop :=
  MulAction.orbitRel G (Ω × Ω) a b

theorem sameOrbital_iff_mem_orbit (a b : Ω × Ω) :
    SameOrbital G Ω a b ↔ a ∈ MulAction.orbit G b :=
  MulAction.orbitRel_apply

theorem sameOrbital_iff (a b : Ω × Ω) :
    SameOrbital G Ω a b ↔ ∃ g : G, g • b = a := by
  rw [sameOrbital_iff_mem_orbit]
  exact MulAction.mem_orbit_iff

end Moore57
