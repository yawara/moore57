import Moore57.Moore57Graph.AFiber.CoordinateConstruction
import Moore57.D19OnMoore57.AFiber.AFiberCoordinateOrbit
import Moore57.Moore57Graph.AFiber.MatchingPerm
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCDataFromCenter

/-!
# `matchingEquiv` is the identity for the default `ofBranches` coordinates

The default coordinate construction `AFiberCoordinates.ofBranches` chooses the
chart at each branch index by the canonical perfect matching from the base
fiber.  In this coordinate scheme the matching-as-coordinate-permutation is
trivial: for every nonzero offset `d`,

    matchingEquiv h.isMoore (ofBranches ...) 0 d hd = Equiv.refl P.

This file proves that identity.  It is the structural ingredient that lets the
natural-language `D₁₉` argument's matching `A_d`-statements translate into the
Lean default-base setup: in default-base coordinates the matching is folded
into the chart, so the Lean matching-permutation is trivial while
`rotationCoordPerm` (the rotation-induced coordinate change) carries the
natural-language matching content.
-/

namespace Moore57

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- For the default `ofBranches` coordinate construction, the chart at a
nonzero branch index is the canonical perfect matching from the base fiber. -/
theorem ofBranches_coord_of_ne_zero
    (hΓ : IsMoore57 Γ) (u : V) (a : ZMod 19 → V)
    (hub : ∀ i : ZMod 19, Γ.Adj u (a i)) (hinj : Function.Injective a)
    {d : ZMod 19} (hd : d ≠ 0) :
    (ofBranches hΓ u a hub hinj).coord d =
      hΓ.branchFiberMatchingEquiv (hub 0) (hub d)
        ((ofBranches hΓ u a hub hinj).a_ne (fun hzero => hd hzero.symm)) := by
  simp only [ofBranches]
  split_ifs with hi
  · exact (hd hi).elim
  · rfl

/-- For the default `ofBranches` coordinate construction, the matching
between fiber `0` and fiber `d` (`d ≠ 0`) is the identity permutation of `P`.

This is a structural fact about the chosen chart: the chart at `d` is itself
the branch-fiber matching, so composing it with the canonical matching used
inside `matchingEquiv` cancels out. -/
theorem ofBranches_matchingEquiv_zero_apply
    (hΓ : IsMoore57 Γ) (u : V) (a : ZMod 19 → V)
    (hub : ∀ i : ZMod 19, Γ.Adj u (a i)) (hinj : Function.Injective a)
    {d : ZMod 19} (hd : (0 : ZMod 19) ≠ d)
    (p : (ofBranches hΓ u a hub hinj).P) :
    AFiberCoordinates.matchingEquiv hΓ (ofBranches hΓ u a hub hinj) 0 d hd p =
      p := by
  classical
  have hd' : d ≠ 0 := fun hzero => hd hzero.symm
  rw [AFiberCoordinates.matchingEquiv_apply,
    ofBranches_coord_zero hΓ u a hub hinj,
    ofBranches_coord_of_ne_zero hΓ u a hub hinj hd']
  exact (hΓ.branchFiberMatchingEquiv (hub 0) (hub d) _).symm_apply_apply p

/-- Equivalence form of `ofBranches_matchingEquiv_zero_apply`: the matching
permutation between fiber `0` and fiber `d` (`d ≠ 0`) for the default
`ofBranches` coordinates is the identity equivalence. -/
theorem ofBranches_matchingEquiv_zero_eq_refl
    (hΓ : IsMoore57 Γ) (u : V) (a : ZMod 19 → V)
    (hub : ∀ i : ZMod 19, Γ.Adj u (a i)) (hinj : Function.Injective a)
    {d : ZMod 19} (hd : (0 : ZMod 19) ≠ d) :
    AFiberCoordinates.matchingEquiv hΓ (ofBranches hΓ u a hub hinj) 0 d hd =
      Equiv.refl _ := by
  apply Equiv.ext
  intro p
  simpa using
    ofBranches_matchingEquiv_zero_apply hΓ u a hub hinj hd p

/-- Corollary for `ofRotationOrbit`: the matching equivalence between fiber
`0` and any nonzero fiber is the identity. -/
theorem ofRotationOrbit_matchingEquiv_zero_apply
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    (hinj : Function.Injective fun i : ZMod 19 => h.rotation i a0)
    {d : ZMod 19} (hd : (0 : ZMod 19) ≠ d)
    (p : (ofRotationOrbit h u a0 hu hub0 hinj).P) :
    AFiberCoordinates.matchingEquiv h.isMoore
        (ofRotationOrbit h u a0 hu hub0 hinj) 0 d hd p = p := by
  exact ofBranches_matchingEquiv_zero_apply h.isMoore u
    (fun i : ZMod 19 => h.rotation i a0)
    (fun i => h.adj_rotation_of_fixed_center hu hub0 i) hinj hd p

/-- Corollary for `ofRotationOrbitOfMoved`: the matching equivalence between
fiber `0` and any nonzero fiber is the identity. -/
theorem ofRotationOrbitOfMoved_matchingEquiv_zero_apply
    (h : D19ActsOnMoore57 V Γ) (u a0 : V)
    (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (hub0 : Γ.Adj u a0)
    {d₀ : ZMod 19} (hd₀ : d₀ ≠ 0) (hmove : h.rotation d₀ a0 ≠ a0)
    {d : ZMod 19} (hd : (0 : ZMod 19) ≠ d)
    (p : (ofRotationOrbitOfMoved h u a0 hu hub0 hd₀ hmove).P) :
    AFiberCoordinates.matchingEquiv h.isMoore
        (ofRotationOrbitOfMoved h u a0 hu hub0 hd₀ hmove) 0 d hd p = p := by
  exact ofRotationOrbit_matchingEquiv_zero_apply h u a0 hu hub0 _ hd p

end AFiberCoordinates

/-- Labeling-level corollary: for any `BranchOrbitABCReflectionLabeling`,
the matching equivalence between reference fiber and any nonzero fiber is
the identity permutation of `P`.

This is the structural fact that lets the natural-language Lemma 6.1 statement
"$A_h(p) \in E \iff A_{2h}(p) = θp$" translate directly to the Lean
default-base labeling.  The Lean's `matchingEquiv` is folded into the chart
choice, so the apparent identity here is the price of the convention. -/
theorem BranchOrbitABCFromCenter.toAFiberCoordinates_matchingEquiv_zero_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    {h : D19ActsOnMoore57 V Γ}
    (data : BranchOrbitABCFromCenter h)
    {d : ZMod 19} (hd : (0 : ZMod 19) ≠ d)
    (p : data.toAFiberCoordinates.P) :
    AFiberCoordinates.matchingEquiv h.isMoore data.toAFiberCoordinates 0 d hd p =
      p :=
  AFiberCoordinates.ofRotationOrbitOfMoved_matchingEquiv_zero_apply
    h data.u data.a0 data.u_fixed data.a0_adj (by decide) data.a0_moved hd p

end Moore57
