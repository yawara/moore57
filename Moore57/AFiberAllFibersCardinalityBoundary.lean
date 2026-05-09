import Moore57.AFiberMatchingSupportEquations

/-!
# All-fiber A-cardinality boundary constructors

This file specializes the matching-equation constructors for
`AFiberCardinality38Boundary` to the full family of nineteen A-fibers.
-/

namespace Moore57

open Finset

noncomputable section

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instAFiberAllFibersCardinalityBoundaryPFintype
    (coords : AFiberCoordinates.{u, uP} Γ) : Fintype coords.P :=
  coords.P_fintype

local instance instAFiberAllFibersCardinalityBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

theorem zmod19_univ_card :
    (Finset.univ : Finset (ZMod 19)).card = 19 := by
  simp [ZMod.card]

namespace AFiberCardinality38Boundary

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}

/-- Full-A-fiber constructor from the statement that every matching-rotation
permutation has exactly two fixed coordinates. -/
noncomputable def of_allFibers_matchingRotationPerm_support_compl_card_eq_two
    (rot : AFiberRotationEquivariance h coords)
    (hfixed :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        (rot.matchingRotationPerm d i hd).supportᶜ.card = 2) :
    AFiberCardinality38Boundary h coords
      (Finset.univ : Finset (ZMod 19)) :=
  of_matchingRotationPerm_support_compl_card_eq_two
    rot zmod19_univ_card (by
      intro d hd i _hi
      exact hfixed d hd i)

/-- Full-A-fiber constructor from explicit matching-equation sums. -/
noncomputable def of_allFibers_matchingEquationFilterCardSum
    (rot : AFiberRotationEquivariance h coords)
    (hsum :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∑ i : ZMod 19,
          ((Finset.univ : Finset coords.P).filter fun p =>
            AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
                (index_ne_add_of_ne_zero hd) p =
              rot.coordPerm d i p).card = 38) :
    AFiberCardinality38Boundary h coords
      (Finset.univ : Finset (ZMod 19)) :=
  of_matchingEquationFilterCardSum rot (by
    intro d hd
    simpa using hsum d hd)

/-- Full-A-fiber constructor from the statement that every explicit matching
equation has exactly two coordinate solutions. -/
noncomputable def of_allFibers_matchingEquationFilterCard_eq_two
    (rot : AFiberRotationEquivariance h coords)
    (hfixed :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        ((Finset.univ : Finset coords.P).filter fun p =>
          AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
              (index_ne_add_of_ne_zero hd) p =
            rot.coordPerm d i p).card = 2) :
    AFiberCardinality38Boundary h coords
      (Finset.univ : Finset (ZMod 19)) :=
  of_matchingEquationFilterCard_eq_two
    rot zmod19_univ_card (by
      intro d hd i _hi
      exact hfixed d hd i)

end AFiberCardinality38Boundary

end

end Moore57
