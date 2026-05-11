import Moore57.D19OnMoore57.AdjacentMoved.AdjacentMovedReflectionConstantResidual

/-!
# Reflection-copy criteria with split constant residual

This file refines the constant-residual reflection-copy witness by allowing the
residual finset to be supplied as a disjoint union of two pieces, such as the
fixed-vertex side and an `A`-side contribution.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A constant-residual reflection-copy criterion whose residual is split into
two disjoint finsets.

The final residual contribution is proved from the two filtered contributions
using `Finset.card_union_of_disjoint`. -/
structure AdjacentMovedReflectionResidualSplit38Witness
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V) where
  k : ZMod 19
  fixedPart : Finset V
  aPart : Finset V
  parts_disjoint : Disjoint fixedPart aPart
  pairwise_disjoint :
    ((Finset.univ : Finset (Fin 2 × Fin 56)) :
      Set (Fin 2 × Fin 56)).PairwiseDisjoint
        (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i))
  fixedPart_disjoint :
    ∀ i : Fin 2 × Fin 56,
      Disjoint
        (h.rotationOrbitFinset (reflectionCopyBase h base k i))
        fixedPart
  aPart_disjoint :
    ∀ i : Fin 2 × Fin 56,
      Disjoint
        (h.rotationOrbitFinset (reflectionCopyBase h base k i))
        aPart
  cover :
    (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion
          (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i)) ∪
        (fixedPart ∪ aPart) =
      (Finset.univ : Finset V)
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      (fixedPart.filter fun y => Γ.Adj y (h.rotation d y)).card +
          (aPart.filter fun y => Γ.Adj y (h.rotation d y)).card =
        38

namespace AdjacentMovedReflectionResidualSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- The residual finset obtained by joining the two residual pieces. -/
def residual (w : AdjacentMovedReflectionResidualSplit38Witness h base) :
    Finset V :=
  w.fixedPart ∪ w.aPart

/-- The two split residual pieces are disjoint after filtering by any
predicate. -/
theorem filter_parts_disjoint
    (w : AdjacentMovedReflectionResidualSplit38Witness h base)
    (p : V → Prop) [DecidablePred p] :
    Disjoint (w.fixedPart.filter p) (w.aPart.filter p) :=
  Disjoint.mono (Finset.filter_subset p w.fixedPart)
    (Finset.filter_subset p w.aPart) w.parts_disjoint

/-- The filtered cardinality of the joined residual is the sum of the filtered
cardinalities of the two residual pieces. -/
theorem residual_filter_card
    (w : AdjacentMovedReflectionResidualSplit38Witness h base)
    (p : V → Prop) [DecidablePred p] :
    ((w.residual).filter p).card =
      (w.fixedPart.filter p).card + (w.aPart.filter p).card := by
  classical
  rw [residual, Finset.filter_union]
  exact Finset.card_union_of_disjoint (w.filter_parts_disjoint p)

/-- Forget the split-residual presentation to the constant-residual
reflection-copy criterion. -/
noncomputable def toConstantResidual38Witness
    (w : AdjacentMovedReflectionResidualSplit38Witness h base) :
    AdjacentMovedReflectionConstantResidual38Witness h base where
  k := w.k
  residual := w.residual
  pairwise_disjoint := w.pairwise_disjoint
  residual_disjoint := by
    intro i
    rw [residual, Finset.disjoint_left]
    intro x hx hxresidual
    rcases Finset.mem_union.mp hxresidual with hxfixed | hxa
    · exact (Finset.disjoint_left.mp (w.fixedPart_disjoint i)) hx hxfixed
    · exact (Finset.disjoint_left.mp (w.aPart_disjoint i)) hx hxa
  cover := by
    simpa [residual] using w.cover
  residual_contribution := by
    intro d hd
    rw [w.residual_filter_card (fun y => Γ.Adj y (h.rotation d y))]
    exact w.residual_contribution d hd

/-- Forget the split-residual presentation to the reflection-copy criterion. -/
noncomputable def toReflectionCopyPartition38Witness
    (w : AdjacentMovedReflectionResidualSplit38Witness h base) :
    AdjacentMovedReflectionCopyPartition38Witness h base :=
  w.toConstantResidual38Witness.toReflectionCopyPartition38Witness

/-- Forget the split-residual presentation to the two-copy witness. -/
noncomputable def toTwoCopyPartition38Witness
    (w : AdjacentMovedReflectionResidualSplit38Witness h base) :
    AdjacentMovedTwoCopyPartition38Witness h base :=
  w.toConstantResidual38Witness.toTwoCopyPartition38Witness

/-- The split-residual witness gives the adjacent-moved decomposition with
residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedReflectionResidualSplit38Witness h base) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution38 :=
  w.toConstantResidual38Witness.toDecomposition

end AdjacentMovedReflectionResidualSplit38Witness

namespace AdjacentMovedReflectionConstantResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for the split-residual reflection-copy criterion. -/
noncomputable def of_residualSplit
    (w : AdjacentMovedReflectionResidualSplit38Witness h base) :
    AdjacentMovedReflectionConstantResidual38Witness h base :=
  w.toConstantResidual38Witness

end AdjacentMovedReflectionConstantResidual38Witness

end Moore57
