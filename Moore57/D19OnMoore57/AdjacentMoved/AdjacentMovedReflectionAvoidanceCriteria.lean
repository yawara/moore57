import Moore57.D19OnMoore57.AdjacentMoved.AdjacentMovedReflectionAvoidance
import Moore57.D19OnMoore57.AdjacentMoved.AdjacentMovedReflectionCompactCriteria

/-!
# Avoidance criterion for compact reflection-copy witnesses

This file replaces the all-pairs cross-disjointness field in the compact
reflection-copy criterion by the smaller condition that every reflected base
avoids the selected rotation-orbit union.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Avoidance-based compact complement-residual reflection-copy criterion.

The avoidance condition says that no reflected selected base belongs to the
selected orbit family.  This implies the mixed original/reflected orbit
disjointness required by `AdjacentMovedReflectionComplementResidual38Witness`.
-/
structure AdjacentMovedReflectionAvoidanceComplementResidual38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((reflectionCopyResidual h input.base k).filter fun y =>
        Γ.Adj y (h.rotation d y)).card = 38

namespace AdjacentMovedReflectionAvoidanceComplementResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Convert the avoidance-based criterion to the compact complement-residual
witness. -/
noncomputable def toComplementResidual38Witness
    (w : AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input) :
    AdjacentMovedReflectionComplementResidual38Witness h input where
  k := w.k
  cross_disjoint :=
    h.cross_disjoint_of_reflection_not_mem_orbitFamilyUnion
      input w.k w.reflection_not_mem_orbitFamilyUnion
  residual_contribution := w.residual_contribution

/-- Convert the avoidance-based criterion to the constant-residual
reflection-copy witness. -/
noncomputable def toConstantResidual38Witness
    (w : AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input) :
    AdjacentMovedReflectionConstantResidual38Witness h input.base :=
  w.toComplementResidual38Witness.toConstantResidual38Witness

/-- Convert the avoidance-based criterion to the reflection-copy partition
witness. -/
noncomputable def toReflectionCopyPartition38Witness
    (w : AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input) :
    AdjacentMovedReflectionCopyPartition38Witness h input.base :=
  w.toComplementResidual38Witness.toReflectionCopyPartition38Witness

/-- Convert the avoidance-based criterion to the two-copy witness. -/
noncomputable def toTwoCopyPartition38Witness
    (w : AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input) :
    AdjacentMovedTwoCopyPartition38Witness h input.base :=
  w.toComplementResidual38Witness.toTwoCopyPartition38Witness

/-- The avoidance-based criterion gives the adjacent-moved decomposition with
residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input) :
    D19AdjacentMovedDecomposition h input.base fixedOrAContribution38 :=
  w.toComplementResidual38Witness.toDecomposition

end AdjacentMovedReflectionAvoidanceComplementResidual38Witness

namespace AdjacentMovedReflectionComplementResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for the avoidance-based compact criterion. -/
noncomputable def of_reflectionAvoidance
    (w : AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input) :
    AdjacentMovedReflectionComplementResidual38Witness h input :=
  w.toComplementResidual38Witness

end AdjacentMovedReflectionComplementResidual38Witness

end Moore57
