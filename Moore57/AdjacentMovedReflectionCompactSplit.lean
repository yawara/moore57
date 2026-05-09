import Moore57.AdjacentMovedReflectionCompactCriteria

/-!
# Compact reflection-copy criteria with split complement residual

This file refines the compact complement-residual witness by allowing the
canonical residual to be supplied as a disjoint union of two pieces, such as the
fixed-vertex side and an `A`-side contribution.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A compact complement-residual reflection-copy criterion whose canonical
residual is split into two disjoint finsets.

The final compact residual contribution is proved from the two filtered
contributions using `Finset.card_union_of_disjoint`. -/
structure AdjacentMovedReflectionComplementResidualSplit38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  cross_disjoint :
    ∀ q r : Fin 56,
      Disjoint
        (h.rotationOrbitFinset (input.base q))
        (h.rotationOrbitFinset
          (h.smul (DihedralGroup.sr k) (input.base r)))
  fixedPart : Finset V
  aPart : Finset V
  parts_disjoint : Disjoint fixedPart aPart
  residual_eq :
    reflectionCopyResidual h input.base k = fixedPart ∪ aPart
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      (fixedPart.filter fun y => Γ.Adj y (h.rotation d y)).card +
          (aPart.filter fun y => Γ.Adj y (h.rotation d y)).card =
        38

namespace AdjacentMovedReflectionComplementResidualSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- The two split residual pieces are disjoint after filtering by any
predicate. -/
theorem filter_parts_disjoint
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input)
    (p : V → Prop) [DecidablePred p] :
    Disjoint (w.fixedPart.filter p) (w.aPart.filter p) :=
  Disjoint.mono (Finset.filter_subset p w.fixedPart)
    (Finset.filter_subset p w.aPart) w.parts_disjoint

/-- The filtered cardinality of the canonical complement residual is the sum of
the filtered cardinalities of its two supplied pieces. -/
theorem residual_filter_card
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input)
    (p : V → Prop) [DecidablePred p] :
    ((reflectionCopyResidual h input.base w.k).filter p).card =
      (w.fixedPart.filter p).card + (w.aPart.filter p).card := by
  classical
  rw [w.residual_eq, Finset.filter_union]
  exact Finset.card_union_of_disjoint (w.filter_parts_disjoint p)

/-- Forget the split presentation to the compact complement-residual
criterion. -/
noncomputable def toComplementResidual38Witness
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    AdjacentMovedReflectionComplementResidual38Witness h input where
  k := w.k
  cross_disjoint := w.cross_disjoint
  residual_contribution := by
    intro d hd
    rw [w.residual_filter_card (fun y => Γ.Adj y (h.rotation d y))]
    exact w.residual_contribution d hd

/-- Convert the split compact complement-residual witness to the existing
constant-residual reflection-copy witness. -/
noncomputable def toConstantResidual38Witness
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    AdjacentMovedReflectionConstantResidual38Witness h input.base :=
  w.toComplementResidual38Witness.toConstantResidual38Witness

/-- Convert the split compact complement-residual witness to the reflection-copy
partition witness. -/
noncomputable def toReflectionCopyPartition38Witness
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    AdjacentMovedReflectionCopyPartition38Witness h input.base :=
  w.toComplementResidual38Witness.toReflectionCopyPartition38Witness

/-- Convert the split compact complement-residual witness to the two-copy
witness. -/
noncomputable def toTwoCopyPartition38Witness
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    AdjacentMovedTwoCopyPartition38Witness h input.base :=
  w.toComplementResidual38Witness.toTwoCopyPartition38Witness

/-- The split compact complement-residual witness gives the adjacent-moved
decomposition with residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    D19AdjacentMovedDecomposition h input.base fixedOrAContribution38 :=
  w.toComplementResidual38Witness.toDecomposition

end AdjacentMovedReflectionComplementResidualSplit38Witness

namespace AdjacentMovedReflectionComplementResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for the split compact complement-residual criterion. -/
noncomputable def of_splitComplementResidual
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    AdjacentMovedReflectionComplementResidual38Witness h input :=
  w.toComplementResidual38Witness

end AdjacentMovedReflectionComplementResidual38Witness

namespace AdjacentMovedReflectionConstantResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the split compact complement-residual criterion to
the constant-residual reflection-copy criterion. -/
noncomputable def of_compactSplitComplementResidual
    (w : AdjacentMovedReflectionComplementResidualSplit38Witness h input) :
    AdjacentMovedReflectionConstantResidual38Witness h input.base :=
  w.toConstantResidual38Witness

end AdjacentMovedReflectionConstantResidual38Witness

end Moore57
