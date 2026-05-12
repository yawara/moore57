import Moore57.D19OnMoore57.BranchOrbit.ABCEndpointCommonNeighborConcreteBoundary
import Moore57.D19OnMoore57.BranchOrbit.Matching

/-!
# Basic endpoint common-neighbor pair

This file names the natural endpoint pair used by the endpoint
common-neighbor argument.  The first endpoint is the endpoint already present
in the endpoint-adjacency hypothesis; the second is its A-fixing-reflection
image, written in coordinates in the `-d` endpoint fiber.

The remaining geometric input is only that this reflected endpoint is also
adjacent to the reference endpoint.  The swap, distinctness, and non-adjacency
parts of the concrete common-neighbor boundary are then formal.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The A-fixing reflection image of the endpoint used in endpoint adjacency,
written as the sign-swapped rotated endpoint in the `-d` A-fiber. -/
def endpointCommonNeighborAFixingReflectedEndpointVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) : V :=
  ((labeling.data.toAFiberCoordinates.coord (0 + (-d))
      (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p) :
    {x : V // x ∈
      branchFiber Γ labeling.data.toAFiberCoordinates.u
        (labeling.data.toAFiberCoordinates.a (0 + (-d)))}) : V)

/-- The endpoint target in the endpoint-adjacency hypothesis is sent by the
A-fixing reflection to the explicitly named sign-swapped endpoint. -/
theorem aFixingReflection_endpointCommonNeighborReflectedEndpointVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) :
    h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
        (labeling.endpointCommonNeighborReflectedEndpointVertex d p) =
      labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p := by
  let coords := labeling.data.toAFiberCoordinates
  have hdd : midpointOf d + midpointOf d = d := midpointOf_add_self d
  have hendpoint :
      labeling.endpointCommonNeighborReflectedEndpointVertex d p =
        (((coords.coord (0 + d)
            (labeling.data.toAFiberRotationEquivariance.coordPerm d 0
              (labeling.aFiberReflectionCoordPerm p)) :
          {x : V // x ∈ branchFiber Γ coords.u (coords.a (0 + d))}) : V)) := by
    have hidx : (0 + (midpointOf d + midpointOf d) : ZMod 19) = 0 + d := by
      simp [hdd]
    have hperm :
        labeling.midpointReflectionCoordPerm (midpointOf d) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p) := by
      simpa [hdd] using
        labeling.midpointReflectionCoordPerm_eq_rotationCoordPerm_aFiberReflectionCoordPerm
          (midpointOf d) p
    rw [endpointCommonNeighborReflectedEndpointVertex, hperm, hidx]
  rw [hendpoint]
  simpa [endpointCommonNeighborAFixingReflectedEndpointVertex, coords] using
    labeling.aFiberReflection_rotationCoordPerm_aFiberReflectionCoordPerm_vertex_eq
      d p

/-- Reflecting the sign-swapped endpoint returns the original endpoint. -/
theorem aFixingReflection_endpointCommonNeighborAFixingReflectedEndpointVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) :
    h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
        (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p) =
      labeling.endpointCommonNeighborReflectedEndpointVertex d p := by
  rw [← labeling.aFixingReflection_endpointCommonNeighborReflectedEndpointVertex d p]
  exact h.reflection_smul_reflection_smul labeling.aFixingReflectionIndex
    (labeling.endpointCommonNeighborReflectedEndpointVertex d p)

/-- The two endpoint targets in the natural A-fixing-reflected pair are
distinct for nonzero `d`, since they lie over the distinct A-branches `d` and
`-d`. -/
theorem endpointCommonNeighbor_reflected_endpoints_ne
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    labeling.endpointCommonNeighborReflectedEndpointVertex d p ≠
      labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p := by
  intro heq
  let coords := labeling.data.toAFiberCoordinates
  have hdd : midpointOf d + midpointOf d = d := midpointOf_add_self d
  have hidx : (0 + d : ZMod 19) ≠ 0 + (-d) := by
    simpa using ne_neg_self_zmod19 hd
  have hxmem :
      labeling.endpointCommonNeighborReflectedEndpointVertex d p ∈
        branchFiber Γ coords.u (coords.a (0 + d)) := by
    simpa [endpointCommonNeighborReflectedEndpointVertex, coords, hdd] using
      coords.coord_mem (0 + (midpointOf d + midpointOf d))
        (labeling.midpointReflectionCoordPerm (midpointOf d) p)
  have hybranch :
      Γ.Adj (coords.a (0 + (-d)))
        (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p) := by
    have hymem :
        labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p ∈
          branchFiber Γ coords.u (coords.a (0 + (-d))) := by
      simpa [endpointCommonNeighborAFixingReflectedEndpointVertex, coords] using
        coords.coord_mem (0 + (-d))
          (labeling.data.toAFiberRotationEquivariance.coordPerm (-d) 0 p)
    exact (mem_branchFiber.mp hymem).2
  have hnot :
      ¬ Γ.Adj
        (labeling.endpointCommonNeighborReflectedEndpointVertex d p)
        (coords.a (0 + (-d))) :=
    h.isMoore.not_adj_other_branch_of_mem_branchFiber
      (coords.hub (0 + d)) (coords.hub (0 + (-d)))
      (coords.a_ne hidx) hxmem
  exact hnot (by simpa [heq] using hybranch.symm)

/-- If both endpoint targets are adjacent to the same reference endpoint, then
the endpoint targets themselves are non-adjacent, by triangle-freeness. -/
theorem endpointCommonNeighbor_reflected_endpoints_not_adj_of_commonNeighbor
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P)
    (hadj :
      Γ.Adj
        (labeling.endpointCommonNeighborReferenceVertex p)
        (labeling.endpointCommonNeighborReflectedEndpointVertex d p))
    (hreflectedAdj :
      Γ.Adj
        (labeling.endpointCommonNeighborReferenceVertex p)
        (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p)) :
    ¬ Γ.Adj
      (labeling.endpointCommonNeighborReflectedEndpointVertex d p)
      (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p) := by
  intro hxy
  exact h.isMoore.no_triangle hxy hreflectedAdj.symm hadj

/-- Minimal remaining endpoint input after naming the natural swapped pair:
the A-fixing-reflected endpoint is also adjacent to the reference endpoint. -/
structure MidpointExceptionEndpointAdjCommonNeighborBasicBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFixing_reflected_endpoint_adj_reference_of_endpoint_adj :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (labeling.endpointCommonNeighborReferenceVertex p)
            (labeling.endpointCommonNeighborReflectedEndpointVertex d p) →
          Γ.Adj
            (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p)
            (labeling.endpointCommonNeighborReferenceVertex p)

namespace MidpointExceptionEndpointAdjCommonNeighborBasicBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The basic reflected-endpoint adjacency boundary supplies the concrete
swapped non-adjacent pair expected by the existing common-neighbor boundary. -/
def toMidpointExceptionEndpointAdjCommonNeighborFixedBoundary
    (boundary :
      MidpointExceptionEndpointAdjCommonNeighborBasicBoundary labeling) :
    MidpointExceptionEndpointAdjCommonNeighborFixedBoundary labeling where
  swapped_not_adj_pair_commonNeighbor_of_endpoint_adj := by
    intro d hd p hp hadj
    let x := labeling.endpointCommonNeighborReflectedEndpointVertex d p
    let y := labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p
    have hyz : Γ.Adj y (labeling.endpointCommonNeighborReferenceVertex p) :=
      boundary.aFixing_reflected_endpoint_adj_reference_of_endpoint_adj
        d hd p hp hadj
    refine ⟨x, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [x, y] using
        labeling.aFixingReflection_endpointCommonNeighborReflectedEndpointVertex
          d p
    · simpa [x, y] using
        labeling.aFixingReflection_endpointCommonNeighborAFixingReflectedEndpointVertex
          d p
    · simpa [x, y] using
        labeling.endpointCommonNeighbor_reflected_endpoints_ne d hd p
    · simpa [x, y] using
        labeling.endpointCommonNeighbor_reflected_endpoints_not_adj_of_commonNeighbor
          d p hadj hyz.symm
    · simpa [x] using hadj.symm
    · simpa [y] using hyz

/-- Direct connector to the existing endpoint fixedness boundary. -/
def toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    (boundary :
      MidpointExceptionEndpointAdjCommonNeighborBasicBoundary labeling) :
    MidpointExceptionEndpointAdjForcesAFixingFixedBoundary labeling :=
  boundary.toMidpointExceptionEndpointAdjCommonNeighborFixedBoundary
    |>.toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary

/-- Direct connector to pointwise endpoint non-adjacency on the A-fixing
moving support. -/
def toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
    (boundary :
      MidpointExceptionEndpointAdjCommonNeighborBasicBoundary labeling) :
    MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling :=
  boundary.toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    |>.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

end MidpointExceptionEndpointAdjCommonNeighborBasicBoundary

namespace MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Pointwise endpoint non-adjacency gives the basic common-neighbor boundary
vacuously: the endpoint-adjacency premise is already impossible on the
A-fixing moving support. -/
def toMidpointExceptionEndpointAdjCommonNeighborBasicBoundary
    (boundary :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    MidpointExceptionEndpointAdjCommonNeighborBasicBoundary labeling where
  aFixing_reflected_endpoint_adj_reference_of_endpoint_adj := by
    intro d hd p hp hadj
    exact False.elim
      (boundary.endpoint_nonadj_of_mem_support d hd p hp
        (by
          simpa [endpointCommonNeighborReferenceVertex,
            endpointCommonNeighborReflectedEndpointVertex] using hadj))

end MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
