import Moore57.AFiberContributionOnlyCriteria

/-!
# A-fiber-only constant contribution constructor

This file provides a constructor for the A-fiber-only contribution data when
the A-fiber filtered cardinality is directly known to be constantly `38`.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace AFiberOnlyContribution38Data

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {aPart : Finset V}

/-- Build A-fiber-only contribution data from the direct statement that every
nonzero A-fiber filtered cardinality is `38`. -/
def of_card_eq_thirtyEight
    (aFiber_card_eq_thirtyEight :
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        (aPart.filter fun y =>
          Γ.Adj y (h.rotation d y)).card = 38) :
    AFiberOnlyContribution38Data h input k aPart where
  aFiberContribution := fun _ => 38
  aFiber_contribution := by
    intro d hd
    exact aFiber_card_eq_thirtyEight d hd
  aFiber_eq_thirtyEight := by
    intro d hd
    rfl

end AFiberOnlyContribution38Data

end Moore57
