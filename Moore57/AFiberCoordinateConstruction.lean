import Moore57.AFiberCoordinates
import Moore57.BranchFiberMatching

/-!
# Constructing A-side fiber coordinates from branch matchings

This file packages the existing perfect matchings between distinct branch
fibers into the `AFiberCoordinates` structure.
-/

namespace Moore57

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Construct A-side fiber coordinates from an indexed family of distinct
branches adjacent to a fixed center.

The coordinate set is the base fiber over `a 0`.  The chart at `0` is the
identity, and every other chart is the perfect matching equivalence from the
base fiber to the corresponding branch fiber.
-/
noncomputable def ofBranches
    (hΓ : IsMoore57 Γ) (u : V) (a : ZMod 19 → V)
    (hub : ∀ i : ZMod 19, Γ.Adj u (a i)) (hinj : Function.Injective a) :
    AFiberCoordinates Γ where
  u := u
  a := a
  hub := hub
  a_injective := hinj
  P := {x : V // x ∈ branchFiber Γ u (a 0)}
  P_fintype := inferInstance
  coord := fun i => by
    by_cases hi : i = 0
    · subst i
      exact Equiv.refl _
    · exact hΓ.branchFiberMatchingEquiv (hub 0) (hub i) (by
        intro h
        exact hi (hinj h).symm)

@[simp] theorem ofBranches_u
    (hΓ : IsMoore57 Γ) (u : V) (a : ZMod 19 → V)
    (hub : ∀ i : ZMod 19, Γ.Adj u (a i)) (hinj : Function.Injective a) :
    (ofBranches hΓ u a hub hinj).u = u :=
  rfl

@[simp] theorem ofBranches_a
    (hΓ : IsMoore57 Γ) (u : V) (a : ZMod 19 → V)
    (hub : ∀ i : ZMod 19, Γ.Adj u (a i)) (hinj : Function.Injective a) :
    (ofBranches hΓ u a hub hinj).a = a :=
  rfl

@[simp] theorem ofBranches_coord_zero
    (hΓ : IsMoore57 Γ) (u : V) (a : ZMod 19 → V)
    (hub : ∀ i : ZMod 19, Γ.Adj u (a i)) (hinj : Function.Injective a) :
    (ofBranches hΓ u a hub hinj).coord 0 = Equiv.refl _ :=
  rfl

end AFiberCoordinates

end Moore57
