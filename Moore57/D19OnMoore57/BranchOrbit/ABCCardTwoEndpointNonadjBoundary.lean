import Moore57.D19OnMoore57.BranchOrbit.ABCCardTwoCandidateGeometryBoundary
import Moore57.Moore57Graph.AFiber.FiberUnionCardinality

/-!
# Card-two rotated endpoint non-adjacency

This file isolates the small endpoint geometry used by the card-two
construction.  Rotated endpoints in a nonzero A-fiber are distinct from the
base endpoint by disjointness of branch fibers.  When the two endpoints share a
candidate neighbor, triangle-freeness makes them non-adjacent.
-/

namespace Moore57

noncomputable section

namespace AFiberCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates Γ}

/-- The endpoint vertex in the base A-fiber. -/
def baseEndpointVertex (coords : AFiberCoordinates Γ) (p : coords.P) : V :=
  ((coords.coord 0 p :
    {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V)

theorem baseEndpointVertex_mem_branchFiber
    (coords : AFiberCoordinates Γ) (p : coords.P) :
    baseEndpointVertex coords p ∈ branchFiber Γ coords.u (coords.a 0) := by
  simp [baseEndpointVertex]

theorem rotatedEndpointVertex_mem_branchFiber
    (rot : AFiberRotationEquivariance h coords)
    (j : ZMod 19) (p : coords.P) :
    rotatedEndpointVertex rot j p ∈
      branchFiber Γ coords.u (coords.a (0 + j)) := by
  simpa [rotatedEndpointVertex] using
    coords.coord_mem (0 + j) (rot.coordPerm j 0 p)

/-- The base endpoint and a nontrivially rotated endpoint lie in disjoint
A-fibers, hence are distinct. -/
theorem baseEndpointVertex_ne_rotatedEndpointVertex_of_ne_zero
    (hΓ : IsMoore57 Γ)
    (rot : AFiberRotationEquivariance h coords)
    {j : ZMod 19} (hj : j ≠ 0) (p : coords.P) :
    baseEndpointVertex coords p ≠ rotatedEndpointVertex rot j p := by
  intro hxy
  have hdisjoint :
      Disjoint
        (branchFiber Γ coords.u (coords.a 0))
        (branchFiber Γ coords.u (coords.a (0 + j))) :=
    hΓ.branchFiber_disjoint_of_ne
      (coords.hub 0) (coords.hub (0 + j))
      (coords.a_ne (index_ne_add_of_ne_zero hj))
  have hx :
      baseEndpointVertex coords p ∈
        branchFiber Γ coords.u (coords.a 0) :=
    baseEndpointVertex_mem_branchFiber coords p
  have hy :
      rotatedEndpointVertex rot j p ∈
        branchFiber Γ coords.u (coords.a (0 + j)) :=
    rotatedEndpointVertex_mem_branchFiber rot j p
  have hx_other :
      baseEndpointVertex coords p ∈
        branchFiber Γ coords.u (coords.a (0 + j)) := by
    simpa [hxy] using hy
  exact (Finset.disjoint_left.mp hdisjoint) hx hx_other

/-- If the base endpoint and a rotated endpoint share a candidate neighbor,
then they are not adjacent. -/
theorem baseEndpointVertex_not_adj_rotatedEndpointVertex_of_common_neighbor
    (hΓ : IsMoore57 Γ)
    (rot : AFiberRotationEquivariance h coords)
    (j : ZMod 19) (p : coords.P) {z : V}
    (hbase : Γ.Adj (baseEndpointVertex coords p) z)
    (hrot : Γ.Adj (rotatedEndpointVertex rot j p) z) :
    ¬ Γ.Adj (baseEndpointVertex coords p)
      (rotatedEndpointVertex rot j p) := by
  intro hendpoints
  exact hΓ.no_triangle hendpoints hrot hbase.symm

/-- Distinctness and non-adjacency for a nontrivially rotated endpoint pair
sharing a candidate neighbor. -/
theorem baseEndpointVertex_rotatedEndpointVertex_ne_and_not_adj_of_common_neighbor
    (hΓ : IsMoore57 Γ)
    (rot : AFiberRotationEquivariance h coords)
    {j : ZMod 19} (hj : j ≠ 0) (p : coords.P) {z : V}
    (hbase : Γ.Adj (baseEndpointVertex coords p) z)
    (hrot : Γ.Adj (rotatedEndpointVertex rot j p) z) :
    baseEndpointVertex coords p ≠ rotatedEndpointVertex rot j p ∧
      ¬ Γ.Adj (baseEndpointVertex coords p)
        (rotatedEndpointVertex rot j p) := by
  exact
    ⟨baseEndpointVertex_ne_rotatedEndpointVertex_of_ne_zero hΓ rot hj p,
      baseEndpointVertex_not_adj_rotatedEndpointVertex_of_common_neighbor
        hΓ rot j p hbase hrot⟩

/-- Candidate-geometry form: matching equations that give the same rotated
candidate neighbor for the base endpoint and the `j`-rotated endpoint force
that endpoint pair to be distinct and non-adjacent. -/
theorem baseEndpointVertex_rotatedEndpointVertex_ne_and_not_adj_of_matching_candidate
    (hΓ : IsMoore57 Γ)
    (rot : AFiberRotationEquivariance h coords)
    {j k : ZMod 19} (hj : j ≠ 0) (hk : k ≠ 0) (hkj : k - j ≠ 0)
    (p q : coords.P)
    (hmBase :
      matchingEquiv hΓ coords 0 (0 + k)
          (index_ne_add_of_ne_zero hk) p =
        rot.coordPerm k 0 q)
    (hmRot :
      matchingEquiv hΓ coords 0 (0 + (k - j))
          (index_ne_add_of_ne_zero hkj) p =
        rot.coordPerm (k - j) 0 q) :
    baseEndpointVertex coords p ≠ rotatedEndpointVertex rot j p ∧
      ¬ Γ.Adj (baseEndpointVertex coords p)
        (rotatedEndpointVertex rot j p) := by
  let z := rotatedCandidateVertex rot k q
  have hbase : Γ.Adj (baseEndpointVertex coords p) z := by
    simpa [baseEndpointVertex, z] using
      base_adj_rotatedCandidateVertex_of_endpoint_matching
        (hΓ := hΓ) (rot := rot) hk p q hmBase
  have hrot : Γ.Adj (rotatedEndpointVertex rot j p) z := by
    simpa [z] using
      rotatedEndpoint_adj_rotatedCandidateVertex_of_difference_matching
        (hΓ := hΓ) (rot := rot) hkj p q hmRot
  exact
    baseEndpointVertex_rotatedEndpointVertex_ne_and_not_adj_of_common_neighbor
      hΓ rot hj p hbase hrot

end AFiberCoordinates

end

end Moore57
