import Moore57.D19OnMoore57.AdjacentMoved.AdjacentMovedReflectionResidualMembership
import Moore57.D19OnMoore57.Orbit.OrbitBaseSelectionInputs

/-!
# Reflection-copy residual as original/reflected orbit-family avoidance

This file repackages the membership criterion for `reflectionCopyResidual`
using the existing `orbitFamilyUnion` abstraction for both the original selected
orbit family and its reflected copy.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- The reflected copy of a selected rotation-orbit family. -/
noncomputable def reflectionOrbitFamilyUnion
    (base : Fin 56 → V) (k : ZMod 19) : Finset V :=
  h.orbitFamilyUnion fun q : Fin 56 =>
    h.smul (DihedralGroup.sr k) (base q)

/-- Membership in the reflected orbit-family union. -/
theorem mem_reflectionOrbitFamilyUnion_iff
    (base : Fin 56 → V) (k : ZMod 19) (y : V) :
    y ∈ h.reflectionOrbitFamilyUnion base k ↔
      ∃ q : Fin 56, ∃ i : ZMod 19,
        h.rotation i (h.smul (DihedralGroup.sr k) (base q)) = y := by
  simpa [reflectionOrbitFamilyUnion] using
    h.mem_orbitFamilyUnion
      (fun q : Fin 56 => h.smul (DihedralGroup.sr k) (base q)) y

/-- The reflection-copy union is the union of the original selected orbit
family and its reflected orbit family. -/
theorem mem_reflectionCopyUnion_iff_orbitFamilyUnion_or_reflectionOrbitFamilyUnion
    (base : Fin 56 → V) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyUnion h base k ↔
      y ∈ h.orbitFamilyUnion base ∨
        y ∈ h.reflectionOrbitFamilyUnion base k := by
  rw [h.mem_reflectionCopyUnion_iff_or base k y,
    h.mem_orbitFamilyUnion base y,
    h.mem_reflectionOrbitFamilyUnion_iff base k y]

/-- The reflection-copy residual is exactly the complement of both the original
selected orbit family and its reflected orbit family. -/
theorem mem_reflectionCopyResidual_iff_not_orbitFamilyUnion_and_not_reflectionOrbitFamilyUnion
    (base : Fin 56 → V) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyResidual h base k ↔
      y ∉ h.orbitFamilyUnion base ∧
        y ∉ h.reflectionOrbitFamilyUnion base k := by
  rw [reflectionCopyResidual, Finset.mem_compl,
    h.mem_reflectionCopyUnion_iff_orbitFamilyUnion_or_reflectionOrbitFamilyUnion
      base k y]
  exact not_or

end D19ActsOnMoore57

namespace OrbitBaseSelectionInput

variable {h : D19ActsOnMoore57 V Γ}

/-- The reflected copy of the selected orbit-family union attached to an input. -/
noncomputable def reflectionOrbitFamilyUnion
    (input : OrbitBaseSelectionInput h) (k : ZMod 19) : Finset V :=
  h.reflectionOrbitFamilyUnion input.base k

/-- Membership in the reflected orbit-family union attached to an input. -/
theorem mem_reflectionOrbitFamilyUnion_iff
    (input : OrbitBaseSelectionInput h) (k : ZMod 19) (y : V) :
    y ∈ input.reflectionOrbitFamilyUnion k ↔
      ∃ q : Fin 56, ∃ i : ZMod 19,
        h.rotation i (h.smul (DihedralGroup.sr k) (input.base q)) = y := by
  simpa [reflectionOrbitFamilyUnion] using
    h.mem_reflectionOrbitFamilyUnion_iff input.base k y

/-- Input-specialized form: the reflection-copy union is the union of the
selected orbit-family union and its reflected orbit-family union. -/
theorem mem_reflectionCopyUnion_iff_orbitFamilyUnion_or_reflectionOrbitFamilyUnion
    (input : OrbitBaseSelectionInput h) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyUnion h input.base k ↔
      y ∈ input.orbitFamilyUnion ∨
        y ∈ input.reflectionOrbitFamilyUnion k := by
  simpa [OrbitBaseSelectionInput.orbitFamilyUnion,
    OrbitBaseSelectionInput.reflectionOrbitFamilyUnion] using
    h.mem_reflectionCopyUnion_iff_orbitFamilyUnion_or_reflectionOrbitFamilyUnion
      input.base k y

/-- Input-specialized form: the reflection-copy residual is exactly the
complement of both the selected orbit-family union and its reflected copy. -/
theorem mem_reflectionCopyResidual_iff_not_orbitFamilyUnion_and_not_reflectionOrbitFamilyUnion
    (input : OrbitBaseSelectionInput h) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyResidual h input.base k ↔
      y ∉ input.orbitFamilyUnion ∧
        y ∉ input.reflectionOrbitFamilyUnion k := by
  simpa [OrbitBaseSelectionInput.orbitFamilyUnion,
    OrbitBaseSelectionInput.reflectionOrbitFamilyUnion] using
    h.mem_reflectionCopyResidual_iff_not_orbitFamilyUnion_and_not_reflectionOrbitFamilyUnion
      input.base k y

end OrbitBaseSelectionInput

end Moore57
