import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionEndpointPointwiseBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionIntersectionInvariantDecomp

/-!
# Two-point A-fixing reflection support

This file packages the finite-set consequences of the two-point
A-fixing-reflection support.  Once a moved reference coordinate `p` is chosen,
the support is exactly the pair `{p, A p}`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instSupportPairBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instSupportPairBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

namespace AFixingReflectionFixedNeighborCardBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- A support point is moved by the A-fixing coordinate reflection. -/
theorem aFiberReflectionCoordPerm_ne_of_mem
    (_supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport) :
    labeling.aFiberReflectionCoordPerm p ≠ p :=
  (labeling.mem_aFiberReflectionSupport p).1 hp

/-- If the A-fixing reflection support has cardinality two and contains `p`,
then it is exactly the pair formed by `p` and its A-fiber reflection mate. -/
theorem aFiberReflectionSupport_eq_pair_of_mem
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport) :
    labeling.aFiberReflectionSupport =
      ({p, labeling.aFiberReflectionCoordPerm p} : Finset
        labeling.data.toAFiberCoordinates.P) := by
  classical
  let q := labeling.aFiberReflectionCoordPerm p
  have hq : q ∈ labeling.aFiberReflectionSupport :=
    labeling.aFiberReflectionCoordPerm_mem_support_of_mem hp
  have hpq : p ≠ q := by
    exact (supportCard.aFiberReflectionCoordPerm_ne_of_mem hp).symm
  have hpair_subset :
      ({p, q} : Finset labeling.data.toAFiberCoordinates.P) ⊆
        labeling.aFiberReflectionSupport := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hp
    · exact hq
  have hpair_card :
      ({p, q} : Finset labeling.data.toAFiberCoordinates.P).card = 2 := by
    simp [hpq]
  have hpair_eq :
      ({p, q} : Finset labeling.data.toAFiberCoordinates.P) =
        labeling.aFiberReflectionSupport := by
    exact Finset.eq_of_subset_of_card_le hpair_subset (by
      rw [supportCard.aFiberReflectionSupport_card_two, hpair_card])
  simpa [q] using hpair_eq.symm

/-- Membership in a two-point A-fixing reflection support is membership in the
chosen point/reflection-mate pair. -/
theorem mem_aFiberReflectionSupport_iff_eq_or_eq_reflection_of_mem
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {p r : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport) :
    r ∈ labeling.aFiberReflectionSupport ↔
      r = p ∨ r = labeling.aFiberReflectionCoordPerm p := by
  classical
  rw [supportCard.aFiberReflectionSupport_eq_pair_of_mem hp]
  simp [eq_comm]

/-- The reflection mate of a chosen support point is the only other support
point. -/
theorem eq_reflection_of_mem_of_ne
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {p r : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport)
    (hr : r ∈ labeling.aFiberReflectionSupport)
    (hrp : r ≠ p) :
    r = labeling.aFiberReflectionCoordPerm p := by
  rcases
    (supportCard.mem_aFiberReflectionSupport_iff_eq_or_eq_reflection_of_mem hp).1
      hr with h | h
  · exact False.elim (hrp h)
  · exact h

end AFixingReflectionFixedNeighborCardBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
