import Moore57.D19OnMoore57.AFiber.MatchingRotationTransportBoundary
import Moore57.D19OnMoore57.AFiber.RotationCoordPermBoundary

/-!
# Candidate adjacency geometry for the card-two branch

This file proves the coordinate-adjacency pieces behind the natural-language
card-two construction.  If the base endpoint `p` matches to the rotated target
`q` at an offset, then the corresponding target vertex is adjacent to the base
endpoint.  Rotating the same matching equation gives the analogous adjacency
from a rotated endpoint.
-/

namespace Moore57

noncomputable section

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates Γ}

/-- The coordinate vertex in the `j`-th A-fiber obtained by rotating a base
coordinate `p`. -/
def rotatedEndpointVertex
    (rot : AFiberRotationEquivariance h coords)
    (j : ZMod 19) (p : coords.P) : V :=
  ((coords.coord (0 + j) (rot.coordPerm j 0 p) :
    {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + j))}) : V)

/-- The candidate common-neighbor vertex in the `k`-th A-fiber obtained by
rotating a base coordinate `q`. -/
def rotatedCandidateVertex
    (rot : AFiberRotationEquivariance h coords)
    (k : ZMod 19) (q : coords.P) : V :=
  ((coords.coord (0 + k) (rot.coordPerm k 0 q) :
    {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + k))}) : V)

/-- A base endpoint matching equation gives adjacency to the corresponding
rotated candidate vertex. -/
theorem base_adj_rotatedCandidateVertex_of_endpoint_matching
    (hΓ : IsMoore57 Γ)
    (rot : AFiberRotationEquivariance h coords)
    {k : ZMod 19} (hk : k ≠ 0)
    (p q : coords.P)
    (hm :
      matchingEquiv hΓ coords 0 (0 + k)
          (index_ne_add_of_ne_zero hk) p =
        rot.coordPerm k 0 q) :
    Γ.Adj
      (((coords.coord 0 p :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
      (rotatedCandidateVertex rot k q) := by
  simpa [rotatedCandidateVertex] using
    (adj_iff_matchingEquiv_eq hΓ coords
      (index_ne_add_of_ne_zero hk) p (rot.coordPerm k 0 q)).2 hm

/-- Rotating an endpoint matching equation by `j` gives adjacency from the
rotated source endpoint to the corresponding rotated target vertex.  This is
the formal coordinate heart of the second common-neighbor adjacency. -/
theorem rotatedEndpoint_adj_rotatedCandidateVertex_of_difference_matching
    (hΓ : IsMoore57 Γ)
    (rot : AFiberRotationEquivariance h coords)
    {j k : ZMod 19} (hkj : k - j ≠ 0)
    (p q : coords.P)
    (hm :
      matchingEquiv hΓ coords 0 (0 + (k - j))
          (index_ne_add_of_ne_zero hkj) p =
        rot.coordPerm (k - j) 0 q) :
    Γ.Adj
      (rotatedEndpointVertex rot j p)
      (rotatedCandidateVertex rot k q) := by
  have htransport :
      matchingEquiv hΓ coords (0 + j) ((0 + (k - j)) + j)
          (by
            intro hidx
            exact (index_ne_add_of_ne_zero hkj)
              (add_right_cancel hidx)) (rot.coordPerm j 0 p) =
        rot.coordPerm j (0 + (k - j)) (rot.coordPerm (k - j) 0 q) :=
    matchingEquiv_rotationCoordPerm_eq_rotationCoordPerm_of_endpoint_matching
      hΓ rot hkj p (rot.coordPerm (k - j) 0 q) hm
  have htarget :
      rot.coordPerm j (0 + (k - j)) (rot.coordPerm (k - j) 0 q) =
        rot.coordPerm k 0 q := by
    have hcomp :=
      AFiberRotationEquivariance.coordPerm_comp_apply
        (rot := rot) (d := k - j) (e := j) (i := 0) (p := q)
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hcomp
  have hidx : ((0 + (k - j)) + j : ZMod 19) = 0 + k := by
    ring_nf
  rw [htarget] at htransport
  have hadj :
      Γ.Adj
        (((coords.coord (0 + j) (rot.coordPerm j 0 p) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + j))}) : V))
        (((coords.coord ((0 + (k - j)) + j) (rot.coordPerm k 0 q) :
          {x : V // x ∈
            branchFiber Γ coords.u (coords.a ((0 + (k - j)) + j))}) : V)) :=
    (adj_iff_matchingEquiv_eq hΓ coords
      (by
        intro h
        exact (index_ne_add_of_ne_zero hkj) (add_right_cancel h))
      (rot.coordPerm j 0 p) (rot.coordPerm k 0 q)).2 htransport
  rw [hidx] at hadj
  simpa [rotatedEndpointVertex, rotatedCandidateVertex] using hadj

end AFiberCoordinates

end

end Moore57
