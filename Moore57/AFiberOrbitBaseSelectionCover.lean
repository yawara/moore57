import Moore57.AFiberOrbitBaseSelection
import Moore57.AdjacentMovedReflectionComplementResidual

set_option maxRecDepth 10000

/-!
# The A-fiber-generated orbit-base selection covers the A-fibers

The orbit-base selection generated from an equivariant A-fiber coordinate
system is useful as an enumeration of the A-side rotation orbits.  This file
records its exact carrier: it is the all-A-fiber union itself.  Consequently,
that particular selection cannot also serve as the non-residual orbit family
when the final residual side is meant to contain all A-fibers.
-/

namespace Moore57

open Finset

noncomputable section

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace AFiberCoordinates

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}

/-- The base field of the orbit-base input generated from A-fiber coordinates
is the base-fiber coordinate enumeration. -/
@[simp] theorem toOrbitBaseSelectionInput_base
    (rot : AFiberRotationEquivariance h coords)
    (e : Fin 56 ≃ coords.P) :
    (coords.toOrbitBaseSelectionInput rot e).base =
      coords.orbitBaseFromEquiv e :=
  rfl

/-- Membership in the rotation-orbit family generated from A-fiber coordinate
bases is exactly membership in the all-A-fiber union. -/
theorem mem_orbitFamilyUnion_orbitBaseFromEquiv_iff_mem_allFibers
    (rot : AFiberRotationEquivariance h coords)
    (e : Fin 56 ≃ coords.P) (y : V) :
    y ∈ h.orbitFamilyUnion (coords.orbitBaseFromEquiv e) ↔
      y ∈ coords.allFibers := by
  constructor
  · intro hy
    rcases
      (D19ActsOnMoore57.mem_orbitFamilyUnion (h := h) (ι := Fin 56)
        (base := coords.orbitBaseFromEquiv e) y).mp hy with
      ⟨q, i, hi⟩
    rw [← hi]
    rw [coords.mem_allFibers_iff]
    refine ⟨0 + i, ?_⟩
    simpa [orbitBaseFromEquiv] using
      rot.rotation_coord_mem_fiber i 0 (e q)
  · intro hy
    rcases (coords.mem_allFibers_iff y).mp hy with ⟨i, hyi⟩
    have hy0i : y ∈ branchFiber Γ coords.u (coords.a (0 + i)) := by
      simpa using hyi
    let p : coords.P := (coords.coord (0 + i)).symm ⟨y, hy0i⟩
    let q : Fin 56 := e.symm ((rot.coordPerm i 0).symm p)
    refine
      (D19ActsOnMoore57.mem_orbitFamilyUnion (h := h) (ι := Fin 56)
        (base := coords.orbitBaseFromEquiv e) y).mpr
      ⟨q, i, ?_⟩
    have hpq : e q = (rot.coordPerm i 0).symm p := by
      simp [q]
    calc
      h.rotation i (coords.orbitBaseFromEquiv e q) =
          ((coords.coord (0 + i) (rot.coordPerm i 0 (e q)) :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + i))}) : V) := by
        rw [orbitBaseFromEquiv]
        exact (rot.coord_coordPerm_apply_val i 0 (e q)).symm
      _ = ((coords.coord (0 + i) p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + i))}) : V) := by
        simp [hpq]
      _ = y := by
        dsimp [p]
        exact
          congrArg Subtype.val
            (Equiv.apply_symm_apply (coords.coord (0 + i)) ⟨y, hy0i⟩)

/-- The orbit-family union generated from A-fiber coordinate bases is exactly
the all-A-fiber union. -/
theorem orbitFamilyUnion_orbitBaseFromEquiv_eq_allFibers
    (rot : AFiberRotationEquivariance h coords)
    (e : Fin 56 ≃ coords.P) :
    h.orbitFamilyUnion (coords.orbitBaseFromEquiv e) =
      coords.allFibers := by
  ext y
  exact coords.mem_orbitFamilyUnion_orbitBaseFromEquiv_iff_mem_allFibers
    rot e y

/-- The downstream orbit-base input generated from A-fiber coordinates has
orbit-family union exactly `coords.allFibers`. -/
theorem toOrbitBaseSelectionInput_orbitFamilyUnion_eq_allFibers
    (rot : AFiberRotationEquivariance h coords)
    (e : Fin 56 ≃ coords.P) :
    (coords.toOrbitBaseSelectionInput rot e).orbitFamilyUnion =
      coords.allFibers := by
  simpa [OrbitBaseSelectionInput.orbitFamilyUnion] using
    coords.orbitFamilyUnion_orbitBaseFromEquiv_eq_allFibers rot e

/-- Moore-cardinality version of
`toOrbitBaseSelectionInput_orbitFamilyUnion_eq_allFibers`. -/
theorem toOrbitBaseSelectionInputOfMoore_orbitFamilyUnion_eq_allFibers
    (rot : AFiberRotationEquivariance h coords) :
    (coords.toOrbitBaseSelectionInputOfMoore rot).orbitFamilyUnion =
      coords.allFibers := by
  simpa [toOrbitBaseSelectionInputOfMoore] using
    coords.toOrbitBaseSelectionInput_orbitFamilyUnion_eq_allFibers
      rot (coords.fin56EquivOfMoore h.isMoore)

end AFiberCoordinates

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- The original selected orbit family is contained in any reflection-copy
union, because side `0` of the copy family is the original base. -/
theorem orbitFamilyUnion_subset_reflectionCopyUnion
    (base : Fin 56 → V) (k : ZMod 19) :
    h.orbitFamilyUnion base ⊆ reflectionCopyUnion h base k := by
  intro y hy
  rcases
    (D19ActsOnMoore57.mem_orbitFamilyUnion (h := h) (ι := Fin 56)
      (base := base) y).mp hy with
    ⟨q, i, hi⟩
  rw [reflectionCopyUnion]
  refine Finset.mem_biUnion.mpr ?_
  refine ⟨((0 : Fin 2), q), Finset.mem_univ _, ?_⟩
  exact (h.mem_rotationOrbitFinset (reflectionCopyBase h base k (0, q)) y).mpr
    ⟨i, by simpa [reflectionCopyBase] using hi⟩

end D19ActsOnMoore57

namespace AFiberCoordinates

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}

/-- If an orbit-base input is generated from the A-fiber coordinates, its
all-A-fiber side is disjoint from the corresponding reflection-copy residual. -/
theorem allFibers_disjoint_reflectionCopyResidual_toOrbitBaseSelectionInput
    (rot : AFiberRotationEquivariance h coords)
    (e : Fin 56 ≃ coords.P) (k : ZMod 19) :
    Disjoint coords.allFibers
      (reflectionCopyResidual h (coords.toOrbitBaseSelectionInput rot e).base k) := by
  rw [← coords.toOrbitBaseSelectionInput_orbitFamilyUnion_eq_allFibers rot e]
  exact
    LE.le.disjoint_compl_right
      (h.orbitFamilyUnion_subset_reflectionCopyUnion
        (coords.toOrbitBaseSelectionInput rot e).base k)

/-- Therefore the A-fiber-generated orbit-base input cannot have all A-fibers
contained in its reflection-copy residual. -/
theorem not_allFibers_subset_reflectionCopyResidual_toOrbitBaseSelectionInput
    (rot : AFiberRotationEquivariance h coords)
    (e : Fin 56 ≃ coords.P) (k : ZMod 19) :
    ¬ coords.allFibers ⊆
      reflectionCopyResidual h (coords.toOrbitBaseSelectionInput rot e).base k := by
  intro hsubset
  let x : V := coords.orbitBaseFromEquiv e 0
  have hxAll : x ∈ coords.allFibers := by
    rw [← coords.orbitFamilyUnion_orbitBaseFromEquiv_eq_allFibers rot e]
    refine
      (D19ActsOnMoore57.mem_orbitFamilyUnion (h := h) (ι := Fin 56)
        (base := coords.orbitBaseFromEquiv e) x).mpr ?_
    exact ⟨0, 0, by simp [x]⟩
  exact
    (Finset.disjoint_left.mp
      (coords.allFibers_disjoint_reflectionCopyResidual_toOrbitBaseSelectionInput
        rot e k))
      hxAll (hsubset hxAll)

/-- The Moore-cardinality generated A-fiber orbit-base input has its all-fiber
side disjoint from the corresponding reflection-copy residual. -/
theorem allFibers_disjoint_reflectionCopyResidual_toOrbitBaseSelectionInputOfMoore
    (rot : AFiberRotationEquivariance h coords) (k : ZMod 19) :
    Disjoint coords.allFibers
      (reflectionCopyResidual h
        (coords.toOrbitBaseSelectionInputOfMoore rot).base k) := by
  simpa [toOrbitBaseSelectionInputOfMoore] using
    coords.allFibers_disjoint_reflectionCopyResidual_toOrbitBaseSelectionInput
      rot (coords.fin56EquivOfMoore h.isMoore) k

/-- Moore-cardinality version: the A-fiber-generated orbit-base input cannot
have all A-fibers contained in its reflection-copy residual. -/
theorem not_allFibers_subset_reflectionCopyResidual_toOrbitBaseSelectionInputOfMoore
    (rot : AFiberRotationEquivariance h coords) (k : ZMod 19) :
    ¬ coords.allFibers ⊆
      reflectionCopyResidual h
        (coords.toOrbitBaseSelectionInputOfMoore rot).base k := by
  simpa [toOrbitBaseSelectionInputOfMoore] using
    coords.not_allFibers_subset_reflectionCopyResidual_toOrbitBaseSelectionInput
      rot (coords.fin56EquivOfMoore h.isMoore) k

end AFiberCoordinates

end

end Moore57
