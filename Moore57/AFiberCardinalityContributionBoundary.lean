import Moore57.AdjacentMovedCanonicalAFiberCriterionBoundary

/-!
# A-fiber cardinality boundary and contribution data

This file records the `Nonempty`-level bridge between the final
A-fiber-cardinality boundary package and the existing fixed/A-fiber
contribution data.  The fixed side is canonical: it is supplied by the
existing zero-contribution theorem through the A-fiber-only contribution
record.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace AFiberCardinality38Boundary

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {indices : Finset (ZMod 19)}

/-- Convert the direct A-fiber-cardinality boundary to the split fixed/A-fiber
contribution data.  The fixed side is discharged by the existing zero theorem
inside `AFiberOnlyContribution38Data.toFixedAFiberContribution38Data`. -/
noncomputable def toFixedAFiberContribution38Data
    (boundary : AFiberCardinality38Boundary h coords indices)
    (input : OrbitBaseSelectionInput h) (k : ZMod 19) :
    FixedAFiberContribution38Data h input k
      (coords.fiberUnion indices) :=
  (boundary.toAFiberOnlyContribution38Data input k).toFixedAFiberContribution38Data

/-- The direct A-fiber-cardinality boundary is equivalent, at the `Nonempty`
level, to the existing split fixed/A-fiber contribution data for the same
selected A-fiber union. -/
theorem nonempty_iff_fixedAFiberContribution38Data
    (input : OrbitBaseSelectionInput h) (k : ZMod 19) :
    Nonempty (AFiberCardinality38Boundary h coords indices) ↔
      Nonempty
        (FixedAFiberContribution38Data h input k
          (coords.fiberUnion indices)) := by
  constructor
  · rintro ⟨boundary⟩
    exact ⟨boundary.toFixedAFiberContribution38Data input k⟩
  · rintro ⟨data⟩
    exact ⟨data.toAFiberCardinality38Boundary⟩

end AFiberCardinality38Boundary

namespace AFiberOnlyContribution38Data

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {indices : Finset (ZMod 19)}

/-- Symmetric spelling of
`AFiberCardinality38Boundary.nonempty_iff_aFiberOnlyContribution38Data`. -/
theorem nonempty_iff_aFiberCardinality38Boundary :
    Nonempty
        (AFiberOnlyContribution38Data h input k
          (coords.fiberUnion indices)) ↔
      Nonempty (AFiberCardinality38Boundary h coords indices) :=
  (AFiberCardinality38Boundary.nonempty_iff_aFiberOnlyContribution38Data
    (h := h) (coords := coords) (indices := indices) input k).symm

end AFiberOnlyContribution38Data

namespace FixedAFiberContribution38Data

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {indices : Finset (ZMod 19)}

/-- Symmetric spelling of the fixed/A-fiber contribution-data bridge. -/
theorem nonempty_iff_aFiberCardinality38Boundary :
    Nonempty
        (FixedAFiberContribution38Data h input k
          (coords.fiberUnion indices)) ↔
      Nonempty (AFiberCardinality38Boundary h coords indices) :=
  (AFiberCardinality38Boundary.nonempty_iff_fixedAFiberContribution38Data
    (h := h) (coords := coords) (indices := indices) input k).symm

end FixedAFiberContribution38Data

namespace AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- A concrete canonical A-fiber criterion determines the corresponding
A-fiber-cardinality boundary package. -/
theorem toAFiberCardinality38Boundary_nonempty
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
      h input) :
    Nonempty (AFiberCardinality38Boundary h w.coords w.indices) :=
  ⟨w.toAFiberCardinality38Boundary⟩

end AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

namespace AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Inclusion-form canonical A-fiber criteria determine the corresponding
A-fiber-cardinality boundary package through the existing canonical
conversion. -/
theorem toAFiberCardinality38Boundary_nonempty
    (w :
      AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness.{u, uP}
        h input) :
    Nonempty (AFiberCardinality38Boundary h w.coords w.indices) :=
  ⟨w.toAFiberCardinality38Boundary⟩

end AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness

end Moore57
