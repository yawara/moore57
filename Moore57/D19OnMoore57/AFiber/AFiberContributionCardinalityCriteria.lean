import Moore57.D19OnMoore57.AFiber.AFiberContributionDecomposition

/-!
# Fixed/A-fiber contribution criteria from concrete cardinalities

This file gives a final-boundary friendly wrapper around
`FixedAFiberContribution38Data`: instead of asking users to provide arbitrary
`fixedContribution` and `aFiberContribution` functions, it names the concrete
filtered cardinality functions and then converts them to the existing data
record.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The concrete fixed-side contribution cardinality for a rotation step. -/
noncomputable def fixedAFiberFixedCard
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) : ZMod 19 → ℕ :=
  fun d =>
    ((rotationOneFixedResidualPart h input k).filter fun y =>
      Γ.Adj y (h.rotation d y)).card

/-- The concrete A-fiber-side contribution cardinality for a rotation step. -/
noncomputable def fixedAFiberAFiberCard
    (h : D19ActsOnMoore57 V Γ) (aPart : Finset V) : ZMod 19 → ℕ :=
  fun d =>
    (aPart.filter fun y => Γ.Adj y (h.rotation d y)).card

/-- The fixed-side contribution cardinality is bounded by the fixed residual
part cardinality. -/
theorem fixedAFiberFixedCard_le_part_card
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k d : ZMod 19) :
    fixedAFiberFixedCard h input k d ≤
      (rotationOneFixedResidualPart h input k).card := by
  simpa [fixedAFiberFixedCard] using
    (Finset.card_filter_le (rotationOneFixedResidualPart h input k)
      (fun y => Γ.Adj y (h.rotation d y)))

/-- The A-fiber-side contribution cardinality is bounded by the A-part
cardinality. -/
theorem fixedAFiberAFiberCard_le_part_card
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) (aPart : Finset V) :
    fixedAFiberAFiberCard h aPart d ≤ aPart.card := by
  simpa [fixedAFiberAFiberCard] using
    (Finset.card_filter_le aPart
      (fun y => Γ.Adj y (h.rotation d y)))

/-- Contribution data stated in terms of named cardinality functions.

The `fixedCard` and `aFiberCard` fields are intended to be concrete
cardinality functions, with the two equality fields recording that they are the
filtered cardinalities of the corresponding fixed/A-fiber sides. -/
structure FixedAFiberContributionCardinalityData
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) (aPart : Finset V) where
  fixedCard : ZMod 19 → ℕ
  aFiberCard : ZMod 19 → ℕ
  fixedCard_eq :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      fixedCard d = fixedAFiberFixedCard h input k d
  aFiberCard_eq :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      aFiberCard d = fixedAFiberAFiberCard h aPart d
  card_sum :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      fixedCard d + aFiberCard d = 38

namespace FixedAFiberContributionCardinalityData

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {aPart : Finset V}

/-- The named cardinality data implies the concrete filtered-cardinality sum. -/
theorem concrete_card_sum
    (data : FixedAFiberContributionCardinalityData h input k aPart) :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      fixedAFiberFixedCard h input k d +
        fixedAFiberAFiberCard h aPart d =
        38 := by
  intro d hd
  rw [← data.fixedCard_eq d hd, ← data.aFiberCard_eq d hd]
  exact data.card_sum d hd

/-- Convert named cardinality data to the existing fixed/A-fiber contribution
data record. -/
noncomputable def toContribution38Data
    (data : FixedAFiberContributionCardinalityData h input k aPart) :
    FixedAFiberContribution38Data h input k aPart where
  fixedContribution := data.fixedCard
  aFiberContribution := data.aFiberCard
  fixed_contribution := by
    intro d hd
    exact (data.fixedCard_eq d hd).symm
  aFiber_contribution := by
    intro d hd
    exact (data.aFiberCard_eq d hd).symm
  contribution_sum := data.card_sum

@[simp]
theorem toContribution38Data_fixedContribution
    (data : FixedAFiberContributionCardinalityData h input k aPart)
    (d : ZMod 19) :
    data.toContribution38Data.fixedContribution d = data.fixedCard d := rfl

@[simp]
theorem toContribution38Data_aFiberContribution
    (data : FixedAFiberContributionCardinalityData h input k aPart)
    (d : ZMod 19) :
    data.toContribution38Data.aFiberContribution d = data.aFiberCard d := rfl

/-- Constructor using the concrete filtered cardinalities themselves. -/
noncomputable def ofConcreteCardSum
    (card_sum :
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        fixedAFiberFixedCard h input k d +
          fixedAFiberAFiberCard h aPart d =
          38) :
    FixedAFiberContributionCardinalityData h input k aPart where
  fixedCard := fixedAFiberFixedCard h input k
  aFiberCard := fixedAFiberAFiberCard h aPart
  fixedCard_eq := by
    intro d hd
    rfl
  aFiberCard_eq := by
    intro d hd
    rfl
  card_sum := card_sum

/-- Constructor for the common case where both side cardinalities are constant
over all nonzero rotation steps. -/
noncomputable def ofConstantCards
    (fixedN aFiberN : ℕ)
    (fixed_card :
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        fixedAFiberFixedCard h input k d = fixedN)
    (aFiber_card :
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        fixedAFiberAFiberCard h aPart d = aFiberN)
    (card_sum : fixedN + aFiberN = 38) :
    FixedAFiberContributionCardinalityData h input k aPart where
  fixedCard := fun _ => fixedN
  aFiberCard := fun _ => aFiberN
  fixedCard_eq := by
    intro d hd
    exact (fixed_card d hd).symm
  aFiberCard_eq := by
    intro d hd
    exact (aFiber_card d hd).symm
  card_sum := by
    intro d hd
    exact card_sum

/-- Fixed-cardinality data inherits the elementary `Finset.card_filter_le`
bound on the fixed side. -/
theorem fixedCard_le_part_card
    (data : FixedAFiberContributionCardinalityData h input k aPart)
    (d : ZMod 19) (hd : d ≠ 0) :
    data.fixedCard d ≤ (rotationOneFixedResidualPart h input k).card := by
  rw [data.fixedCard_eq d hd]
  exact fixedAFiberFixedCard_le_part_card h input k d

/-- A-fiber-cardinality data inherits the elementary `Finset.card_filter_le`
bound on the A-fiber side. -/
theorem aFiberCard_le_part_card
    (data : FixedAFiberContributionCardinalityData h input k aPart)
    (d : ZMod 19) (hd : d ≠ 0) :
    data.aFiberCard d ≤ aPart.card := by
  rw [data.aFiberCard_eq d hd]
  exact fixedAFiberAFiberCard_le_part_card h d aPart

end FixedAFiberContributionCardinalityData

namespace FixedAFiberContribution38Data

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {aPart : Finset V}

/-- Constructor wrapper from named concrete-cardinality data. -/
noncomputable def of_cardinalityData
    (data : FixedAFiberContributionCardinalityData h input k aPart) :
    FixedAFiberContribution38Data h input k aPart :=
  data.toContribution38Data

/-- Constructor wrapper from the concrete filtered-cardinality sum. -/
noncomputable def ofConcreteCardSum
    (card_sum :
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        fixedAFiberFixedCard h input k d +
          fixedAFiberAFiberCard h aPart d =
          38) :
    FixedAFiberContribution38Data h input k aPart :=
  (FixedAFiberContributionCardinalityData.ofConcreteCardSum
    (h := h) (input := input) (k := k) (aPart := aPart) card_sum).toContribution38Data

/-- Constructor wrapper for constant fixed/A-fiber contribution cardinalities. -/
noncomputable def ofConstantCards
    (fixedN aFiberN : ℕ)
    (fixed_card :
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        fixedAFiberFixedCard h input k d = fixedN)
    (aFiber_card :
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        fixedAFiberAFiberCard h aPart d = aFiberN)
    (card_sum : fixedN + aFiberN = 38) :
    FixedAFiberContribution38Data h input k aPart :=
  (FixedAFiberContributionCardinalityData.ofConstantCards
    (h := h) (input := input) (k := k) (aPart := aPart)
    fixedN aFiberN fixed_card aFiber_card card_sum).toContribution38Data

end FixedAFiberContribution38Data

end Moore57
