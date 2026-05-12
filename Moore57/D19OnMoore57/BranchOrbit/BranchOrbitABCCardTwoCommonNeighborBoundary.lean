import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionAllSupportBoundary

/-!
# Card-two endpoint obstruction via two common neighbors

The natural-language `e = 2` exclusion says that if every A-fixing support
point satisfies the endpoint adjacency, then a suitable non-adjacent endpoint
pair has multiple common neighbors, contradicting `μ = 1`.

This file records the formal graph-theoretic part of that argument.  The
coordinate construction of the two common neighbors is kept as the remaining
geometric input.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace IsMoore57

omit [DecidableEq V] in
/-- A Moore graph has at most one common neighbor for any non-adjacent pair. -/
theorem eq_of_commonNeighbor_of_commonNeighbor_of_not_adj
    (hΓ : IsMoore57 Γ) {x y z w : V}
    (hxy : x ≠ y) (hnadj : ¬ Γ.Adj x y)
    (hzx : Γ.Adj x z) (hyz : Γ.Adj y z)
    (hwx : Γ.Adj x w) (hyw : Γ.Adj y w) :
    z = w := by
  have hz_mem : z ∈ Γ.commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨hzx, hyz⟩
  have hw_mem : w ∈ Γ.commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨hwx, hyw⟩
  have hcard : Fintype.card (Γ.commonNeighbors x y) = 1 :=
    hΓ.of_not_adj hxy hnadj
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨c, hc_unique⟩
  have hcz : (c : V) = z :=
    (congrArg Subtype.val (hc_unique ⟨z, hz_mem⟩)).symm
  have hcw : (c : V) = w :=
    (congrArg Subtype.val (hc_unique ⟨w, hw_mem⟩)).symm
  exact hcz.symm.trans hcw

omit [DecidableEq V] in
/-- Contradiction form: a non-adjacent pair cannot have two distinct common
neighbors. -/
theorem no_two_commonNeighbors_of_not_adj
    (hΓ : IsMoore57 Γ) {x y z w : V}
    (hxy : x ≠ y) (hnadj : ¬ Γ.Adj x y)
    (hzw : z ≠ w)
    (hzx : Γ.Adj x z) (hyz : Γ.Adj y z)
    (hwx : Γ.Adj x w) (hyw : Γ.Adj y w) : False :=
  hzw
    (hΓ.eq_of_commonNeighbor_of_commonNeighbor_of_not_adj
      hxy hnadj hzx hyz hwx hyw)

/-- If two vertices have a common neighbor in a Moore graph, then they are
not adjacent.  This is the `λ = 0` endpoint core used by the common-neighbor
argument. -/
theorem not_adj_of_commonNeighbor
    (hΓ : IsMoore57 Γ) {x y z : V}
    (hzx : Γ.Adj x z) (hyz : Γ.Adj y z) :
    ¬ Γ.Adj x y := by
  intro hxy
  exact hΓ.no_triangle hxy hyz hzx.symm

/-- Two common neighbors of the same distinct endpoint pair coincide.  The
non-adjacency of the endpoint pair is derived from `λ = 0`; uniqueness then
uses `μ = 1`. -/
theorem eq_of_commonNeighbor_of_commonNeighbor
    (hΓ : IsMoore57 Γ) {x y z w : V}
    (hxy : x ≠ y)
    (hzx : Γ.Adj x z) (hyz : Γ.Adj y z)
    (hwx : Γ.Adj x w) (hyw : Γ.Adj y w) :
    z = w :=
  hΓ.eq_of_commonNeighbor_of_commonNeighbor_of_not_adj hxy
    (hΓ.not_adj_of_commonNeighbor hzx hyz) hzx hyz hwx hyw

/-- Contradiction form for two distinct common neighbors of a distinct
endpoint pair, with endpoint non-adjacency inferred from the first common
neighbor. -/
theorem no_two_commonNeighbors
    (hΓ : IsMoore57 Γ) {x y z w : V}
    (hxy : x ≠ y) (hzw : z ≠ w)
    (hzx : Γ.Adj x z) (hyz : Γ.Adj y z)
    (hwx : Γ.Adj x w) (hyw : Γ.Adj y w) : False :=
  hzw (hΓ.eq_of_commonNeighbor_of_commonNeighbor hxy hzx hyz hwx hyw)

/-- Two common neighbors of the same distinct endpoint pair cannot be adjacent:
they are equal by `μ = 1`, so an edge between them would be a loop. -/
theorem not_adj_between_commonNeighbors
    (hΓ : IsMoore57 Γ) {x y z w : V}
    (hxy : x ≠ y)
    (hzx : Γ.Adj x z) (hyz : Γ.Adj y z)
    (hwx : Γ.Adj x w) (hyw : Γ.Adj y w) :
    ¬ Γ.Adj z w := by
  intro hzw
  have h_eq : z = w :=
    hΓ.eq_of_commonNeighbor_of_commonNeighbor hxy hzx hyz hwx hyw
  subst h_eq
  exact SimpleGraph.irrefl Γ hzw

end IsMoore57

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Boundary form of the geometric `e = 2` contradiction: if all A-fixing
support points satisfy the endpoint adjacency for a nonzero offset, then one
can exhibit a non-adjacent pair with two distinct common neighbors. -/
structure MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  two_commonNeighbors_of_all_endpoint_adj :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      (∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (((labeling.data.toAFiberCoordinates.coord 0 p :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a 0)}) : V))
            (((labeling.data.toAFiberCoordinates.coord
                (0 + (midpointOf d + midpointOf d))
                (labeling.midpointReflectionCoordPerm (midpointOf d) p) :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a
                    (0 + (midpointOf d + midpointOf d)))}) : V))) →
        ∃ x y z w : V,
          x ≠ y ∧
          ¬ Γ.Adj x y ∧
          z ≠ w ∧
          Γ.Adj x z ∧ Γ.Adj y z ∧
          Γ.Adj x w ∧ Γ.Adj y w

namespace MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The two-common-neighbor construction gives the existing no-all-endpoint
adjacency boundary by the Moore `μ = 1` condition. -/
def toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    (boundary :
      MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary
        labeling) :
    MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling where
  not_all_support_endpoint_adj := by
    intro d hd hall
    rcases boundary.two_commonNeighbors_of_all_endpoint_adj d hd hall with
      ⟨x, y, z, w, hxy, hnadj, hzw, hxz, hyz, hxw, hyw⟩
    exact
      h.isMoore.no_two_commonNeighbors_of_not_adj
        hxy hnadj hzw hxz hyz hxw hyw

/-- Direct conversion to the existing no-card-two boundary. -/
def toMidpointExceptionAFixingSupportNoCardTwoBoundary
    (boundary :
      MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary
        labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardTwoBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    |>.toMidpointExceptionAFixingSupportNoCardTwoBoundary criterion

end MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
