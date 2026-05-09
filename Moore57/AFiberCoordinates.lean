import Moore57.D19Contradiction

/-!
# Section 3: coordinates on the A-side fibers

This file records the minimal coordinate data used for the A-side branch
fibers.  The field `P` is the abstract coordinate set for the base fiber, and
`coord i` identifies the same coordinate set with each fiber over `a i`.
-/

namespace Moore57

/-- A minimal coordinate system for the A-side branch fibers around `u`.

The vertices `a i` are the A-side branches adjacent to `u`; the single finite
type `P` is used as coordinates on every fiber `branchFiber Γ u (a i)`.
-/
structure AFiberCoordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] where
  /-- The fixed center vertex. -/
  u : V
  /-- The A-side branch indexed by `ZMod 19`. -/
  a : ZMod 19 → V
  /-- Every A-side branch is adjacent to the center. -/
  hub : ∀ i : ZMod 19, Γ.Adj u (a i)
  /-- The A-side branches are distinct. -/
  a_injective : Function.Injective a
  /-- The common coordinate set for the A-side fibers. -/
  P : Type*
  /-- The coordinate set is finite. -/
  P_fintype : Fintype P
  /-- The coordinate chart on each A-side fiber. -/
  coord : ∀ i : ZMod 19, P ≃ {x : V // x ∈ branchFiber Γ u (a i)}

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The base A-fiber over `a 0`. -/
abbrev baseFiber (h : AFiberCoordinates Γ) : Finset V :=
  branchFiber Γ h.u (h.a 0)

/-- Distinct indices give distinct A-side branches. -/
theorem a_ne (h : AFiberCoordinates Γ) {i j : ZMod 19} (hij : i ≠ j) :
    h.a i ≠ h.a j := by
  intro haij
  exact hij (h.a_injective haij)

/-- A coordinate point indeed lies in the corresponding branch fiber. -/
theorem coord_mem (h : AFiberCoordinates Γ) (i : ZMod 19) (p : h.P) :
    ((h.coord i p : {x : V // x ∈ branchFiber Γ h.u (h.a i)}) : V) ∈
      branchFiber Γ h.u (h.a i) :=
  (h.coord i p).property

/-- Every A-side branch fiber has cardinality `56` in a Moore57 graph. -/
theorem fiber_card (h : AFiberCoordinates Γ) (hΓ : IsMoore57 Γ) (i : ZMod 19) :
    (branchFiber Γ h.u (h.a i)).card = 56 :=
  hΓ.branchFiber_card (h.hub i)

/-- The coordinate set has cardinality `56` in a Moore57 graph. -/
theorem card_P (h : AFiberCoordinates Γ) (hΓ : IsMoore57 Γ) :
    @Fintype.card h.P h.P_fintype = 56 := by
  letI := h.P_fintype
  calc
    Fintype.card h.P =
        Fintype.card ({x : V // x ∈ branchFiber Γ h.u (h.a 0)}) :=
      Fintype.card_congr (h.coord 0)
    _ = (branchFiber Γ h.u (h.a 0)).card := by
      rw [Fintype.card_coe]
    _ = 56 :=
      h.fiber_card hΓ 0

end AFiberCoordinates

end Moore57
