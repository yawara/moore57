import Moore57.AdjacentMovedReflectionAvoidanceCriteria
import Moore57.AdjacentMovedReflectionCompactSplit

/-!
# Avoidance criterion with split complement residual

This file combines the avoidance-based cross-disjointness criterion with the
split presentation of the canonical complement residual.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Avoidance-based complement-residual criterion with the canonical residual
split into two disjoint pieces. -/
structure AdjacentMovedReflectionAvoidanceSplit38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion
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

namespace AdjacentMovedReflectionAvoidanceSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Convert the avoidance split criterion to the compact split witness. -/
noncomputable def toComplementResidualSplit38Witness
    (w : AdjacentMovedReflectionAvoidanceSplit38Witness h input) :
    AdjacentMovedReflectionComplementResidualSplit38Witness h input where
  k := w.k
  cross_disjoint :=
    h.cross_disjoint_of_reflection_not_mem_orbitFamilyUnion
      input w.k w.reflection_not_mem_orbitFamilyUnion
  fixedPart := w.fixedPart
  aPart := w.aPart
  parts_disjoint := w.parts_disjoint
  residual_eq := w.residual_eq
  residual_contribution := w.residual_contribution

/-- Convert the avoidance split criterion to the avoidance compact witness. -/
noncomputable def toAvoidanceComplementResidual38Witness
    (w : AdjacentMovedReflectionAvoidanceSplit38Witness h input) :
    AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input where
  k := w.k
  reflection_not_mem_orbitFamilyUnion := w.reflection_not_mem_orbitFamilyUnion
  residual_contribution := by
    intro d hd
    exact w.toComplementResidualSplit38Witness
      |>.toComplementResidual38Witness
      |>.residual_contribution d hd

/-- Convert the avoidance split criterion to the compact complement-residual
witness. -/
noncomputable def toComplementResidual38Witness
    (w : AdjacentMovedReflectionAvoidanceSplit38Witness h input) :
    AdjacentMovedReflectionComplementResidual38Witness h input :=
  w.toComplementResidualSplit38Witness.toComplementResidual38Witness

/-- Convert the avoidance split criterion to the constant-residual
reflection-copy witness. -/
noncomputable def toConstantResidual38Witness
    (w : AdjacentMovedReflectionAvoidanceSplit38Witness h input) :
    AdjacentMovedReflectionConstantResidual38Witness h input.base :=
  w.toComplementResidual38Witness.toConstantResidual38Witness

/-- The avoidance split criterion gives the adjacent-moved decomposition with
residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedReflectionAvoidanceSplit38Witness h input) :
    D19AdjacentMovedDecomposition h input.base fixedOrAContribution38 :=
  w.toComplementResidual38Witness.toDecomposition

end AdjacentMovedReflectionAvoidanceSplit38Witness

namespace AdjacentMovedReflectionAvoidanceComplementResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for the split avoidance criterion. -/
noncomputable def of_splitAvoidance
    (w : AdjacentMovedReflectionAvoidanceSplit38Witness h input) :
    AdjacentMovedReflectionAvoidanceComplementResidual38Witness h input :=
  w.toAvoidanceComplementResidual38Witness

end AdjacentMovedReflectionAvoidanceComplementResidual38Witness

end Moore57
