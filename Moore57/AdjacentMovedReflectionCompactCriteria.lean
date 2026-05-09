import Moore57.AdjacentMovedReflectionComplementResidual
import Moore57.AdjacentMovedReflectionCrossDisjoint

/-!
# Compact reflection-copy criteria

This file packages the smallest current reflection-copy adjacent-moved
criterion over an `OrbitBaseSelectionInput`: original/reflected cross
disjointness plus the filtered count of the canonical complement residual.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Compact witness for the canonical complement-residual reflection-copy
criterion based on an orbit-base selection input.

The base/base and reflected/reflected disjointness are derived from
`OrbitBaseSelectionInput`; the mixed cases are exactly the `cross_disjoint`
field.  The residual is the complement of the copied orbit union. -/
structure AdjacentMovedReflectionComplementResidual38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  cross_disjoint :
    ∀ q r : Fin 56,
      Disjoint
        (h.rotationOrbitFinset (input.base q))
        (h.rotationOrbitFinset
          (h.smul (DihedralGroup.sr k) (input.base r)))
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((reflectionCopyResidual h input.base k).filter fun y =>
        Γ.Adj y (h.rotation d y)).card = 38

namespace AdjacentMovedReflectionComplementResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Convert the compact complement-residual witness to the existing
constant-residual reflection-copy witness. -/
noncomputable def toConstantResidual38Witness
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    AdjacentMovedReflectionConstantResidual38Witness h input.base :=
  AdjacentMovedReflectionConstantResidual38Witness.of_complementResidual
    (h := h) (base := input.base) w.k
    (h.pairwiseDisjoint_reflectionCopyBase_of_base_cross
      input w.k w.cross_disjoint)
    w.residual_contribution

/-- Convert the compact complement-residual witness to the reflection-copy
partition witness. -/
noncomputable def toReflectionCopyPartition38Witness
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    AdjacentMovedReflectionCopyPartition38Witness h input.base :=
  w.toConstantResidual38Witness.toReflectionCopyPartition38Witness

/-- Convert the compact complement-residual witness to the two-copy witness. -/
noncomputable def toTwoCopyPartition38Witness
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    AdjacentMovedTwoCopyPartition38Witness h input.base :=
  w.toConstantResidual38Witness.toTwoCopyPartition38Witness

/-- The compact complement-residual witness gives the adjacent-moved
decomposition with residual contribution constantly `38`. -/
noncomputable def toDecomposition
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    D19AdjacentMovedDecomposition h input.base fixedOrAContribution38 :=
  w.toConstantResidual38Witness.toDecomposition

end AdjacentMovedReflectionComplementResidual38Witness

namespace AdjacentMovedReflectionConstantResidual38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper for the compact complement-residual criterion. -/
noncomputable def of_compactComplementResidual
    (w : AdjacentMovedReflectionComplementResidual38Witness h input) :
    AdjacentMovedReflectionConstantResidual38Witness h input.base :=
  w.toConstantResidual38Witness

end AdjacentMovedReflectionConstantResidual38Witness

end Moore57
