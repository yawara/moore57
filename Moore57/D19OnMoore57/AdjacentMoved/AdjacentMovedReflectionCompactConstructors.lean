import Moore57.D19OnMoore57.AdjacentMoved.AdjacentMovedReflectionCompactCriteria

/-!
# Constructor wrappers for compact reflection-copy criteria

This file exposes namespace-local constructors from the compact
complement-residual witness to the existing adjacent-moved witness layers.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace AdjacentMovedReflectionCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for the compact complement-residual criterion. -/
noncomputable def of_compactComplementResidual
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    AdjacentMovedReflectionCopyPartition38Witness h input.base :=
  w.toReflectionCopyPartition38Witness

end AdjacentMovedReflectionCopyPartition38Witness

namespace AdjacentMovedTwoCopyPartition38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for the compact complement-residual criterion. -/
noncomputable def of_compactComplementResidual
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    AdjacentMovedTwoCopyPartition38Witness h input.base :=
  w.toTwoCopyPartition38Witness

end AdjacentMovedTwoCopyPartition38Witness

namespace D19AdjacentMovedDecomposition

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for a compact complement-residual adjacent-moved
decomposition. -/
noncomputable def of_compactComplementResidual38
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    D19AdjacentMovedDecomposition h input.base fixedOrAContribution38 :=
  w.toDecomposition

end D19AdjacentMovedDecomposition

end Moore57
