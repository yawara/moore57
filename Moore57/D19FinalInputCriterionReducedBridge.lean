import Moore57.D19FinalInputCriterionBoundary

/-!
# Reduced bridge from final input criteria

This file records the existing forgetful path from the low-level final input
criterion boundary to the reduced D19 contradiction interfaces.
-/

namespace Moore57

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19FinalInputCriterionBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the low-level criterion-boundary presentation down to the geometric
input boundary. -/
noncomputable def toD19GeometricInputs
    (data : D19FinalInputCriterionBoundaryInputs.{u, uP} h) :
    D19GeometricInputs h :=
  data.toD19FinalInputs.toD19GeometricInputs

/-- Forget the low-level criterion-boundary presentation down to the reduced
hypotheses used by the contradiction pipeline. -/
noncomputable def toD19ReducedHypotheses
    (data : D19FinalInputCriterionBoundaryInputs.{u, uP} h) :
    D19ReducedHypotheses h :=
  data.toD19GeometricInputs.toD19ReducedHypotheses

/-- Forget the low-level criterion-boundary presentation down to the split
orbit-contribution interface. -/
noncomputable def toD19OrbitContributionData
    (data : D19FinalInputCriterionBoundaryInputs.{u, uP} h) :
    D19OrbitContributionData h :=
  data.toD19ReducedHypotheses.toD19OrbitContributionData

/-- Forget the low-level criterion-boundary presentation down to the generated
orbit concrete interface. -/
noncomputable def toD19ActionOrbitConcreteData
    (data : D19FinalInputCriterionBoundaryInputs.{u, uP} h) :
    D19ActionOrbitConcreteData h :=
  data.toD19OrbitContributionData.toActionOrbitConcreteData

end D19FinalInputCriterionBoundaryInputs

end Moore57
