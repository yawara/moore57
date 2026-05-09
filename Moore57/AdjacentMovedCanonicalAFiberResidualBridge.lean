import Moore57.AdjacentMovedReflectionCanonicalAFiberInclusions
import Moore57.AFiberOrbitMovingResidual

/-!
# Residual-containment constructors for canonical A-fiber criteria

This file gives field-level constructors for the canonical A-fiber criteria
when the reverse A-fiber/moving-residual inclusion is supplied as residual
containment plus rotation equivariance of the A-fiber coordinates.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {indices : Finset (ZMod 19)}

/-- Build the inclusion-form canonical A-fiber criterion from residual
containment and A-fiber rotation equivariance, deriving the reverse inclusion
into the canonical moving residual. -/
noncomputable def of_residualContainment
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉
          input.orbitFamilyUnion)
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h input k ⊆ coords.fiberUnion indices)
    (aFiber_subset_residual :
      coords.fiberUnion indices ⊆ reflectionCopyResidual h input.base k)
    (rot : AFiberRotationEquivariance h coords)
    (residual_contribution :
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        ((rotationOneFixedResidualPart h input k).filter fun y =>
            Γ.Adj y (h.rotation d y)).card +
          ((coords.fiberUnion indices).filter fun y =>
            Γ.Adj y (h.rotation d y)).card =
          38) :
    AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness.{u, uP}
      h input where
  k := k
  reflection_not_mem_orbitFamilyUnion :=
    reflection_not_mem_orbitFamilyUnion
  coords := coords
  indices := indices
  moving_subset_aFiber := moving_subset_aFiber
  aFiber_subset_moving :=
    rot.fiberUnion_subset_movingResidual_of_subset_residual input k indices
      aFiber_subset_residual
  residual_contribution := residual_contribution

end AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness

namespace AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {indices : Finset (ZMod 19)}

/-- Build the equality-form canonical A-fiber criterion from residual
containment and A-fiber rotation equivariance, deriving the moving/A-fiber
equality from the two inclusions. -/
noncomputable def of_residualContainment
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (input.base r) ∉
          input.orbitFamilyUnion)
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h input k ⊆ coords.fiberUnion indices)
    (aFiber_subset_residual :
      coords.fiberUnion indices ⊆ reflectionCopyResidual h input.base k)
    (rot : AFiberRotationEquivariance h coords)
    (residual_contribution :
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        ((rotationOneFixedResidualPart h input k).filter fun y =>
            Γ.Adj y (h.rotation d y)).card +
          ((coords.fiberUnion indices).filter fun y =>
            Γ.Adj y (h.rotation d y)).card =
          38) :
    AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
      h input where
  k := k
  reflection_not_mem_orbitFamilyUnion :=
    reflection_not_mem_orbitFamilyUnion
  coords := coords
  indices := indices
  moving_eq_aFiber :=
    Finset.Subset.antisymm moving_subset_aFiber
      (rot.fiberUnion_subset_movingResidual_of_subset_residual input k
        indices aFiber_subset_residual)
  residual_contribution := residual_contribution

end AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

end Moore57
