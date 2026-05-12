import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCMidpointExceptionSetBoundary

/-!
# Reference matching solutions fixed by the A-fixing reflection

This file isolates the geometric input needed by
`ReferenceRotationEquationAFixingFixedBoundary`: a solution of the reference
matching equation is fixed as an underlying reference-fiber vertex by the
A-fixing reflection.  The conversion to the existing coordinate-permutation
boundary is formal.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- A coordinate is fixed by the A-fixing reflection permutation exactly when
its reference-fiber vertex is fixed by the underlying A-fixing reflection. -/
theorem aFiberReflectionCoordPerm_fixed_iff_vertex_fixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (p : labeling.data.toAFiberCoordinates.P) :
    labeling.aFiberReflectionCoordPerm p = p ↔
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((labeling.data.toAFiberCoordinates.coord 0 p :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a 0)}) : V)) =
        (((labeling.data.toAFiberCoordinates.coord 0 p :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a 0)}) : V)) := by
  simpa using labeling.aFiberReflectionCoordPerm_eq_iff p p

/-- Symmetric spelling of
`aFiberReflectionCoordPerm_fixed_iff_vertex_fixed`. -/
theorem aFiberReflection_vertex_fixed_iff_coordPerm_fixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (p : labeling.data.toAFiberCoordinates.P) :
    h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (((labeling.data.toAFiberCoordinates.coord 0 p :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a 0)}) : V)) =
        (((labeling.data.toAFiberCoordinates.coord 0 p :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a 0)}) : V)) ↔
      labeling.aFiberReflectionCoordPerm p = p := by
  exact (labeling.aFiberReflectionCoordPerm_fixed_iff_vertex_fixed p).symm

/-- Geometric boundary form: every solution of the reference matching equation
has its source reference-fiber vertex fixed by the A-fixing reflection. -/
structure ReferenceRotationMatchingSolutionVertexFixedBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  reference_solution_vertex_fixed :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p →
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (((labeling.data.toAFiberCoordinates.coord 0 p :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a 0)}) : V)) =
          (((labeling.data.toAFiberCoordinates.coord 0 p :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a 0)}) : V))

/-- Constructor from the geometric vertex-fixed boundary to the existing
coordinate-permutation fixedness boundary. -/
noncomputable def referenceRotationEquationAFixingFixedBoundary_of_vertexFixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (fixed : ReferenceRotationMatchingSolutionVertexFixedBoundary labeling) :
    ReferenceRotationEquationAFixingFixedBoundary labeling where
  reference_solution_fixed := by
    intro d hd p hmatch
    exact
      (labeling.aFiberReflectionCoordPerm_fixed_iff_vertex_fixed p).2
        (fixed.reference_solution_vertex_fixed d hd p hmatch)

namespace ReferenceRotationMatchingSolutionVertexFixedBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Method form of
`referenceRotationEquationAFixingFixedBoundary_of_vertexFixed`. -/
noncomputable def toReferenceRotationEquationAFixingFixedBoundary
    (fixed : ReferenceRotationMatchingSolutionVertexFixedBoundary labeling) :
    ReferenceRotationEquationAFixingFixedBoundary labeling :=
  referenceRotationEquationAFixingFixedBoundary_of_vertexFixed labeling fixed

end ReferenceRotationMatchingSolutionVertexFixedBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
