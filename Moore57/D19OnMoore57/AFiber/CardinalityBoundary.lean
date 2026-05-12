import Moore57.D19OnMoore57.AFiber.OnlyContributionConstant

/-!
# A-fiber cardinality boundary

This file names the final A-fiber cardinality boundary assumption: the
selected A-fiber union has filtered cardinality `38` for every nonzero
rotation step.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Boundary package for the final A-fiber-cardinality assumption on a selected
union of A-fibers. -/
structure AFiberCardinality38Boundary
    (h : D19ActsOnMoore57 V Γ) (coords : AFiberCoordinates.{u, uP} Γ)
    (indices : Finset (ZMod 19)) where
  /-- The selected A-fiber side has cardinality `38` after filtering by
  adjacency to every nonzero rotation step. -/
  card_eq_thirtyEight :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      fixedAFiberAFiberCard h (coords.fiberUnion indices) d = 38

namespace AFiberCardinality38Boundary

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {indices : Finset (ZMod 19)}

/-- Build the boundary package from the direct cardinality statement. -/
def of_card_eq_thirtyEight
    (card_eq_thirtyEight :
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        fixedAFiberAFiberCard h (coords.fiberUnion indices) d = 38) :
    AFiberCardinality38Boundary h coords indices where
  card_eq_thirtyEight := card_eq_thirtyEight

/-- Projection theorem exposing the named boundary cardinality statement. -/
theorem fixedAFiberAFiberCard_eq_thirtyEight
    (boundary : AFiberCardinality38Boundary h coords indices)
    (d : ZMod 19) (hd : d ≠ 0) :
    fixedAFiberAFiberCard h (coords.fiberUnion indices) d = 38 :=
  boundary.card_eq_thirtyEight d hd

/-- Convert the boundary package to the existing A-fiber-only contribution
record for any orbit-base input and reflected rotation parameter. -/
noncomputable def toAFiberOnlyContribution38Data
    (boundary : AFiberCardinality38Boundary h coords indices)
    (input : OrbitBaseSelectionInput h) (k : ZMod 19) :
    AFiberOnlyContribution38Data h input k (coords.fiberUnion indices) :=
  AFiberOnlyContribution38Data.of_card_eq_thirtyEight
    boundary.card_eq_thirtyEight

@[simp]
theorem toAFiberOnlyContribution38Data_aFiberContribution
    (boundary : AFiberCardinality38Boundary h coords indices)
    (input : OrbitBaseSelectionInput h) (k d : ZMod 19) :
    (boundary.toAFiberOnlyContribution38Data input k).aFiberContribution d =
      38 :=
  rfl

/-- The boundary package is exactly the direct A-fiber-cardinality statement. -/
theorem nonempty_iff_card_eq_thirtyEight :
    Nonempty (AFiberCardinality38Boundary h coords indices) ↔
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        fixedAFiberAFiberCard h (coords.fiberUnion indices) d = 38 := by
  constructor
  · rintro ⟨boundary⟩
    exact boundary.card_eq_thirtyEight
  · intro hcard
    exact ⟨of_card_eq_thirtyEight hcard⟩

/-- The boundary package is equivalent, at the `Nonempty` level, to the
existing A-fiber-only contribution record for any chosen input and `k`. -/
theorem nonempty_iff_aFiberOnlyContribution38Data
    (input : OrbitBaseSelectionInput h) (k : ZMod 19) :
    Nonempty (AFiberCardinality38Boundary h coords indices) ↔
      Nonempty
        (AFiberOnlyContribution38Data h input k
          (coords.fiberUnion indices)) := by
  constructor
  · rintro ⟨boundary⟩
    exact ⟨boundary.toAFiberOnlyContribution38Data input k⟩
  · rintro ⟨data⟩
    refine ⟨of_card_eq_thirtyEight ?_⟩
    intro d hd
    rw [fixedAFiberAFiberCard, data.aFiber_contribution d hd]
    exact data.aFiber_eq_thirtyEight d hd

end AFiberCardinality38Boundary

end Moore57
