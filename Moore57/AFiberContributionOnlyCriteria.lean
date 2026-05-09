import Moore57.AFiberContributionCardinalityCriteria
import Moore57.FixedResidualContributionZero

/-!
# A-fiber-only contribution criteria

This file packages the common case where the canonical fixed residual side has
zero contribution automatically, so the fixed/A-fiber contribution data can be
built from the A-fiber side alone.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Contribution data where the canonical fixed side is handled by the zero
fixed-residual contribution theorem, leaving only the A-fiber side to supply. -/
structure AFiberOnlyContribution38Data
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) (aPart : Finset V) where
  aFiberContribution : ZMod 19 → ℕ
  aFiber_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      (aPart.filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        aFiberContribution d
  aFiber_eq_thirtyEight :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      aFiberContribution d = 38

namespace AFiberOnlyContribution38Data

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {aPart : Finset V}

/-- Convert A-fiber-only contribution data to the full fixed/A-fiber
contribution record, with the fixed side definitionally set to zero. -/
noncomputable def toFixedAFiberContribution38Data
    (data : AFiberOnlyContribution38Data h input k aPart) :
    FixedAFiberContribution38Data h input k aPart where
  fixedContribution := fun _ => 0
  aFiberContribution := data.aFiberContribution
  fixed_contribution := by
    intro d hd
    exact rotationOneFixedResidualPart_filter_adjacent_rotation_card_eq_zero
      h input k d hd
  aFiber_contribution := data.aFiber_contribution
  contribution_sum := by
    intro d hd
    simp [data.aFiber_eq_thirtyEight d hd]

@[simp]
theorem toFixedAFiberContribution38Data_fixedContribution
    (data : AFiberOnlyContribution38Data h input k aPart)
    (d : ZMod 19) :
    data.toFixedAFiberContribution38Data.fixedContribution d = 0 := rfl

@[simp]
theorem toFixedAFiberContribution38Data_aFiberContribution
    (data : AFiberOnlyContribution38Data h input k aPart)
    (d : ZMod 19) :
    data.toFixedAFiberContribution38Data.aFiberContribution d =
      data.aFiberContribution d := rfl

end AFiberOnlyContribution38Data

namespace FixedAFiberContribution38Data

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {aPart : Finset V}

/-- Constructor wrapper from A-fiber-only contribution data. -/
noncomputable def of_aFiberOnly
    (data : AFiberOnlyContribution38Data h input k aPart) :
    FixedAFiberContribution38Data h input k aPart :=
  data.toFixedAFiberContribution38Data

end FixedAFiberContribution38Data

end Moore57
