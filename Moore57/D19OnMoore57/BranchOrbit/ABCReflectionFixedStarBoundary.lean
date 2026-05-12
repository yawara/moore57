import Moore57.D19OnMoore57.BranchOrbit.Midpoint

/-!
# Reflection fixed-star boundary

This file packages the common fixed-star input used by the reflection-labeled
branch argument.  The boundary records that every reflection fixed induced
graph has a `K_{1,55}`-style center, and that the rotation-fixed center is not
that star center.  It also isolates the extra midpoint identification needed
to turn the same fixed-star input into the middle fixed-neighbor count.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The subtype of vertices fixed by the reflection `sr k`. -/
abbrev reflectionFixedVertex
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) : Type u :=
  {x : V // h.smul (DihedralGroup.sr k) x = x}

/-- The rotation-fixed center, viewed as a fixed vertex of the reflection
`sr k`. -/
def reflectionRotationFixedCenterVertex
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    reflectionFixedVertex h k :=
  ⟨h.rotationFixedCenter, h.reflection_smul_rotationFixedCenter k⟩

/-- A vertex is the center of the reflection fixed star when it has fixed
degree `55` and every other fixed vertex has fixed degree at most `1`. -/
def IsReflectionFixedStarCenter
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19)
    (c : reflectionFixedVertex h k) : Prop :=
  (h.fixedInducedGraph (DihedralGroup.sr k)).degree c = 55 ∧
    ∀ x : reflectionFixedVertex h k,
      x ≠ c → (h.fixedInducedGraph (DihedralGroup.sr k)).degree x ≤ 1

/-- Boundary form of the fixed-star input for reflections.  For each
reflection, a fixed-star center exists, and the rotation-fixed center is not
such a center. -/
structure ReflectionFixedStarBoundary
    (h : D19ActsOnMoore57 V Γ) : Prop where
  exists_center :
    ∀ k : ZMod 19,
      ∃ c : reflectionFixedVertex h k, IsReflectionFixedStarCenter h k c
  rotationFixedCenter_not_center :
    ∀ k : ZMod 19,
      ¬ IsReflectionFixedStarCenter h k
        (reflectionRotationFixedCenterVertex h k)

namespace ReflectionFixedStarBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The fixed-star boundary implies the fixed-center leaf boundary already
used by the reflection-labeled branch argument. -/
def toReflectionFixedCenterLeafBoundary
    (boundary : ReflectionFixedStarBoundary h) :
    ReflectionFixedCenterLeafBoundary h where
  degree_le_one := by
    intro k
    rcases boundary.exists_center k with ⟨c, hc⟩
    exact hc.2 (reflectionRotationFixedCenterVertex h k) (by
      intro hcenter
      exact boundary.rotationFixedCenter_not_center k (by
        simpa [hcenter] using hc))

end ReflectionFixedStarBoundary

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The middle A-branch vertex fixed by the midpoint reflection, viewed in the
corresponding reflection fixed subtype. -/
def midpointMiddleFixedVertex
    (labeling : BranchOrbitABCReflectionLabeling h) (m : ZMod 19) :
    reflectionFixedVertex h (labeling.midpointReflectionIndex m) :=
  ⟨labeling.data.toAFiberCoordinates.a (0 + m), by
    have hraw :=
      (labeling.toAFiberMidpointReflectionEquivariance m).reflection_a
        (0 + m)
    have hidx : (2 : ZMod 19) * m - (0 + m) = 0 + m := by
      ring
    rw [hidx] at hraw
    exact hraw⟩

/-- The extra type-level input needed to derive the midpoint middle fixed
neighbor count from the abstract fixed-star boundary: each nonzero middle
A-branch vertex must be identified with the center of the corresponding
midpoint reflection fixed star. -/
structure ReflectionFixedStarMiddleBoundary
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  midpointMiddle_is_center :
    ∀ m : ZMod 19, ∀ _hm : m ≠ 0,
      IsReflectionFixedStarCenter h (labeling.midpointReflectionIndex m)
        (labeling.midpointMiddleFixedVertex m)

namespace ReflectionFixedStarMiddleBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The fixed-star middle identification gives the fixed-neighbor count needed
by the midpoint exception-set boundary. -/
def toMidpointMiddleFixedNeighborCardBoundary
    (middle : ReflectionFixedStarMiddleBoundary star labeling) :
    MidpointMiddleFixedNeighborCardBoundary labeling where
  fixed_middle_neighbor_card := by
    intro m hm
    have hdegree :
        (h.fixedInducedGraph
            (DihedralGroup.sr (labeling.midpointReflectionIndex m))).degree
          (labeling.midpointMiddleFixedVertex m) = 55 :=
      (middle.midpointMiddle_is_center m hm).1
    have hcard :=
      h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
        (DihedralGroup.sr (labeling.midpointReflectionIndex m))
        (labeling.midpointMiddleFixedVertex m)
    rw [hcard] at hdegree
    exact hdegree

end ReflectionFixedStarMiddleBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
