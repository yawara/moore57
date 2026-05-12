import Moore57.D19OnMoore57.BranchOrbit.ABCSupportPairEndpointMatchingBoundary
import Moore57.D19OnMoore57.AFiber.MatchingRotationTransportBoundary
import Moore57.D19OnMoore57.AFiber.RotationCoordPermBoundary

/-!
# Candidate adjacency from endpoint matching equations

This file records the small coordinate step used by the card-two
common-neighbor construction.  A matching target of the form
`matchingEquiv 0 d p = rot d 0 q` names a concrete rotated candidate vertex.
The rotation-transport API then gives the same candidate as an adjacent target
from any rotated source fiber whose index differs by `d`.
-/

namespace Moore57

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates Γ}

/-- A matching equation whose target is a rotated base coordinate gives the
concrete adjacency from the base source to the candidate vertex in fiber `k`. -/
theorem adj_base_candidate_of_matching_target
    (hΓ : IsMoore57 Γ)
    (rot : AFiberRotationEquivariance h coords)
    {k : ZMod 19} (h0k : 0 ≠ k)
    (p q : coords.P)
    (hm :
      matchingEquiv hΓ coords 0 k h0k p =
        rot.coordPerm k 0 q) :
    Γ.Adj
      (((coords.coord 0 p :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
      (((coords.coord k (rot.coordPerm k 0 q) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a k)}) : V)) := by
  exact
    (adj_iff_matchingEquiv_eq hΓ coords h0k p
      (rot.coordPerm k 0 q)).2 hm

/-- Transport an endpoint matching equation from fibers `0,d` to fibers
`j,j+d`, and rewrite the transported target as the single candidate obtained by
rotating the base coordinate by `d + j`. -/
theorem rotated_endpoint_matching_target_eq_candidate
    (hΓ : IsMoore57 Γ)
    (rot : AFiberRotationEquivariance h coords)
    {d j : ZMod 19} (hd : d ≠ 0)
    (p q : coords.P)
    (hm :
      matchingEquiv hΓ coords 0 (0 + d)
          (index_ne_add_of_ne_zero hd) p =
        rot.coordPerm d 0 q) :
    matchingEquiv hΓ coords (0 + j) ((0 + d) + j)
        (by
          intro hidx
          exact (index_ne_add_of_ne_zero hd) (add_right_cancel hidx))
        (rot.coordPerm j 0 p) =
      rot.coordPerm (d + j) 0 q := by
  have htransport :
      matchingEquiv hΓ coords (0 + j) ((0 + d) + j)
          (by
            intro hidx
            exact (index_ne_add_of_ne_zero hd) (add_right_cancel hidx))
          (rot.coordPerm j 0 p) =
        rot.coordPerm j (0 + d) (rot.coordPerm d 0 q) :=
    matchingEquiv_rotationCoordPerm_eq_rotationCoordPerm_of_endpoint_matching
      (hΓ := hΓ) (rot := rot) (d := d) (k := j) hd p
      (rot.coordPerm d 0 q) hm
  have hcandidate :
      rot.coordPerm j (0 + d) (rot.coordPerm d 0 q) =
        rot.coordPerm (d + j) 0 q := by
    simpa using rot.coordPerm_comp_apply d j 0 q
  exact htransport.trans hcandidate

/-- The transported endpoint matching equation is exactly the concrete
adjacency from the rotated source in fiber `j` to the candidate in fiber
`d + j`. -/
theorem adj_rotated_source_candidate_of_endpoint_matching
    (hΓ : IsMoore57 Γ)
    (rot : AFiberRotationEquivariance h coords)
    {d j : ZMod 19} (hd : d ≠ 0)
    (p q : coords.P)
    (hm :
      matchingEquiv hΓ coords 0 (0 + d)
          (index_ne_add_of_ne_zero hd) p =
        rot.coordPerm d 0 q) :
    Γ.Adj
      (((coords.coord (0 + j) (rot.coordPerm j 0 p) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + j))}) : V))
      (((coords.coord ((0 + d) + j) (rot.coordPerm (d + j) 0 q) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a ((0 + d) + j))}) :
        V)) := by
  exact
    (adj_iff_matchingEquiv_eq hΓ coords
      (by
        intro hidx
        exact (index_ne_add_of_ne_zero hd) (add_right_cancel hidx))
      (rot.coordPerm j 0 p) (rot.coordPerm (d + j) 0 q)).2
      (rotated_endpoint_matching_target_eq_candidate
        (hΓ := hΓ) (rot := rot) (d := d) (j := j) hd p q hm)

/-- Difference-equation spelling of the transported adjacency: if the
candidate fiber is `k = j + d`, the endpoint equation with offset `d` gives
adjacency from the source in fiber `j` to that candidate. -/
theorem adj_source_candidate_of_endpoint_matching_difference
    (hΓ : IsMoore57 Γ)
    (rot : AFiberRotationEquivariance h coords)
    {j k d : ZMod 19} (hd : d ≠ 0) (hk : k = j + d)
    (p q : coords.P)
    (hm :
      matchingEquiv hΓ coords 0 (0 + d)
          (index_ne_add_of_ne_zero hd) p =
        rot.coordPerm d 0 q) :
    Γ.Adj
      (((coords.coord j (rot.coordPerm j 0 p) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V))
      (((coords.coord k (rot.coordPerm k 0 q) :
        {x : V // x ∈ branchFiber Γ coords.u (coords.a k)}) : V)) := by
  subst k
  have hmatch :
      matchingEquiv hΓ coords j (j + d) (index_ne_add_of_ne_zero hd)
          (rot.coordPerm j 0 p) =
        rot.coordPerm (j + d) 0 q := by
    simpa [zero_add, add_comm, add_assoc, add_left_comm] using
      rotated_endpoint_matching_target_eq_candidate
        (hΓ := hΓ) (rot := rot) (d := d) (j := j) hd p q hm
  exact
    (adj_iff_matchingEquiv_eq hΓ coords (index_ne_add_of_ne_zero hd)
      (rot.coordPerm j 0 p) (rot.coordPerm (j + d) 0 q)).2 hmatch

/-- Pack the two concrete adjacencies for a candidate in fiber `k`: one from a
base-source matching equation and one from an endpoint equation whose offset
is the difference from source fiber `j` to candidate fiber `k`. -/
theorem candidate_commonNeighbor_adjacencies_of_matching_targets
    (hΓ : IsMoore57 Γ)
    (rot : AFiberRotationEquivariance h coords)
    {j k d : ZMod 19} (h0k : 0 ≠ k) (hd : d ≠ 0) (hk : k = j + d)
    (p0 pj q : coords.P)
    (hm0 :
      matchingEquiv hΓ coords 0 k h0k p0 =
        rot.coordPerm k 0 q)
    (hmj :
      matchingEquiv hΓ coords 0 (0 + d)
          (index_ne_add_of_ne_zero hd) pj =
        rot.coordPerm d 0 q) :
    Γ.Adj
        (((coords.coord 0 p0 :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
        (((coords.coord k (rot.coordPerm k 0 q) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a k)}) : V)) ∧
      Γ.Adj
        (((coords.coord j (rot.coordPerm j 0 pj) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a j)}) : V))
        (((coords.coord k (rot.coordPerm k 0 q) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a k)}) : V)) := by
  exact
    ⟨adj_base_candidate_of_matching_target
        (hΓ := hΓ) (rot := rot) h0k p0 q hm0,
      adj_source_candidate_of_endpoint_matching_difference
        (hΓ := hΓ) (rot := rot) hd hk pj q hmj⟩

end AFiberCoordinates

end Moore57
