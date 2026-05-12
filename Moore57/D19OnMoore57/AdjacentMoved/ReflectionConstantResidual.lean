import Moore57.D19OnMoore57.AdjacentMoved.ReflectionCopyCriteria

/-!
# Reflection-copy criteria with constant residual

This file packages the special case of
`AdjacentMovedReflectionCopyPartition38Witness` where the residual finset is
independent of the nontrivial rotation `d`.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A reflection-copy partition criterion whose residual finset is fixed for
all nontrivial rotations.

The orbit pieces are already independent of `d` in the underlying
reflection-copy criterion.  This witness additionally makes the residual
independent of `d`; only the filtered residual contribution still ranges over
the nontrivial rotations. -/
structure AdjacentMovedReflectionConstantResidual38Witness
    (h : D19ActsOnMoore57 V Γ) (base : Fin 56 → V) where
  k : ZMod 19
  residual : Finset V
  pairwise_disjoint :
    ((Finset.univ : Finset (Fin 2 × Fin 56)) :
      Set (Fin 2 × Fin 56)).PairwiseDisjoint
        (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i))
  residual_disjoint :
    ∀ i : Fin 2 × Fin 56,
      Disjoint
        (h.rotationOrbitFinset (reflectionCopyBase h base k i))
        residual
  cover :
    (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion
          (fun i => h.rotationOrbitFinset (reflectionCopyBase h base k i)) ∪
        residual =
      (Finset.univ : Finset V)
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      (residual.filter fun y => Γ.Adj y (h.rotation d y)).card = 38

namespace AdjacentMovedReflectionConstantResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Forget the constant-residual presentation to the existing reflection-copy
criterion. -/
noncomputable def toReflectionCopyPartition38Witness
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    AdjacentMovedReflectionCopyPartition38Witness h base where
  k := w.k
  residual := fun _ _ => w.residual
  pairwise_disjoint := by
    intro d hd
    simpa using w.pairwise_disjoint
  residual_disjoint := by
    intro d hd i
    simpa using w.residual_disjoint i
  cover := by
    intro d hd
    simpa using w.cover
  residual_contribution := by
    intro d hd
    simpa using w.residual_contribution d hd

/-- Forget the constant-residual presentation to the orbit-copy criterion. -/
noncomputable def toOrbitCopyPartition38Witness
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    AdjacentMovedOrbitCopyPartition38Witness h base :=
  w.toReflectionCopyPartition38Witness.toOrbitCopyPartition38Witness

/-- Forget the constant-residual presentation directly to the two-copy
witness. -/
noncomputable def toTwoCopyPartition38Witness
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    AdjacentMovedTwoCopyPartition38Witness h base :=
  w.toReflectionCopyPartition38Witness.toTwoCopyPartition38Witness

/-- The constant-residual reflection-copy witness gives the adjacent-moved
decomposition with residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution38 :=
  w.toReflectionCopyPartition38Witness.toDecomposition

end AdjacentMovedReflectionConstantResidual38Witness

namespace AdjacentMovedReflectionCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for the constant-residual reflection-copy criterion. -/
noncomputable def of_constantResidual
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    AdjacentMovedReflectionCopyPartition38Witness h base :=
  w.toReflectionCopyPartition38Witness

end AdjacentMovedReflectionCopyPartition38Witness

namespace AdjacentMovedTwoCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for the constant-residual reflection-copy criterion. -/
noncomputable def of_reflectionConstantResidual
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    AdjacentMovedTwoCopyPartition38Witness h base :=
  w.toTwoCopyPartition38Witness

end AdjacentMovedTwoCopyPartition38Witness

namespace D19AdjacentMovedDecomposition

variable {h : D19ActsOnMoore57 V Γ}
variable {base : Fin 56 → V}

/-- Constructor wrapper for a constant-residual reflection-copy adjacent-moved
decomposition. -/
noncomputable def of_reflectionConstantResidual38
    (w : AdjacentMovedReflectionConstantResidual38Witness h base) :
    D19AdjacentMovedDecomposition h base fixedOrAContribution38 :=
  w.toDecomposition

end D19AdjacentMovedDecomposition

end Moore57
