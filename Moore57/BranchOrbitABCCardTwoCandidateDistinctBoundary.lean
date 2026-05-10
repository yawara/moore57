import Moore57.BranchOrbitABCCardTwoCandidateGeometryBoundary
import Moore57.AFiberFiberUnionCardinality

/-!
# Distinct card-two candidate vertices

The rotated candidate common-neighbor vertices land in their indexed A-fibers.
Thus candidates with distinct A-fiber indices are distinct vertices.
-/

namespace Moore57

noncomputable section

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates Γ}

/-- A rotated candidate vertex lies in the branch fiber indexed by its offset. -/
theorem rotatedCandidateVertex_mem_branchFiber
    (rot : AFiberRotationEquivariance h coords)
    (k : ZMod 19) (q : coords.P) :
    rotatedCandidateVertex rot k q ∈
      branchFiber Γ coords.u (coords.a (0 + k)) := by
  simpa [rotatedCandidateVertex] using
    coords.coord_mem (0 + k) (rot.coordPerm k 0 q)

/-- A rotated candidate vertex lies in the corresponding `AFiberCoordinates`
fiber. -/
theorem rotatedCandidateVertex_mem_fiber
    (rot : AFiberRotationEquivariance h coords)
    (k : ZMod 19) (q : coords.P) :
    rotatedCandidateVertex rot k q ∈ coords.fiber (0 + k) := by
  simpa [fiber] using
    rotatedCandidateVertex_mem_branchFiber (coords := coords) rot k q

/-- Rotated candidate vertices in distinct A-fibers are distinct, independently
of their base coordinates. -/
theorem rotatedCandidateVertex_ne_of_index_ne_of_coords
    (rot : AFiberRotationEquivariance h coords)
    {k l : ZMod 19} (hkl : k ≠ l) (q r : coords.P) :
    rotatedCandidateVertex rot k q ≠ rotatedCandidateVertex rot l r := by
  intro hxy
  have hx :
      rotatedCandidateVertex rot k q ∈
        branchFiber Γ coords.u (coords.a (0 + k)) :=
    rotatedCandidateVertex_mem_branchFiber (coords := coords) rot k q
  have hy :
      rotatedCandidateVertex rot l r ∈
        branchFiber Γ coords.u (coords.a (0 + l)) :=
    rotatedCandidateVertex_mem_branchFiber (coords := coords) rot l r
  have hidx : (0 + k : ZMod 19) ≠ 0 + l := by
    simpa using hkl
  have hdisj :
      Disjoint (branchFiber Γ coords.u (coords.a (0 + k)))
        (branchFiber Γ coords.u (coords.a (0 + l))) :=
    h.isMoore.branchFiber_disjoint_of_ne
      (coords.hub (0 + k)) (coords.hub (0 + l)) (coords.a_ne hidx)
  exact (Finset.disjoint_left.mp hdisj) hx (by simpa [hxy] using hy)

/-- Same-coordinate spelling of
`rotatedCandidateVertex_ne_of_index_ne_of_coords`. -/
theorem rotatedCandidateVertex_ne_of_index_ne
    (rot : AFiberRotationEquivariance h coords)
    {k l : ZMod 19} (hkl : k ≠ l) (q : coords.P) :
    rotatedCandidateVertex rot k q ≠ rotatedCandidateVertex rot l q :=
  rotatedCandidateVertex_ne_of_index_ne_of_coords rot hkl q q

end AFiberCoordinates

end

end Moore57
