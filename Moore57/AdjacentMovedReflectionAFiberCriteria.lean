import Moore57.AdjacentMovedReflectionAvoidanceSplit
import Moore57.Moore57Graph.AFiber.CoordinateConstruction

/-!
# A-fiber criteria for the avoidance split witness

This file refines the `aPart : Finset V` field in
`AdjacentMovedReflectionAvoidanceSplit38Witness`: instead of taking it as an
arbitrary finset, the new data package makes it the union of selected
`AFiberCoordinates` branch fibers.  The package also records the intended
fixed/moved split and converts back to the existing witness.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace AFiberCoordinates

/-- The branch fiber over the A-side branch with index `i`. -/
abbrev fiber (A : AFiberCoordinates Γ) (i : ZMod 19) : Finset V :=
  branchFiber Γ A.u (A.a i)

/-- The union of a selected family of A-side branch fibers. -/
noncomputable def fiberUnion (A : AFiberCoordinates Γ)
    (indices : Finset (ZMod 19)) : Finset V :=
  indices.biUnion fun i => A.fiber i

/-- The union of all A-side branch fibers in the coordinate system. -/
noncomputable abbrev allFibers (A : AFiberCoordinates Γ) : Finset V :=
  A.fiberUnion Finset.univ

@[simp] theorem mem_fiber (A : AFiberCoordinates Γ) (i : ZMod 19) (x : V) :
    x ∈ A.fiber i ↔ x ∈ branchFiber Γ A.u (A.a i) :=
  Iff.rfl

theorem mem_fiberUnion_iff (A : AFiberCoordinates Γ)
    (indices : Finset (ZMod 19)) (x : V) :
    x ∈ A.fiberUnion indices ↔
      ∃ i : ZMod 19, i ∈ indices ∧ x ∈ branchFiber Γ A.u (A.a i) := by
  classical
  simp [fiberUnion, fiber]

theorem mem_allFibers_iff (A : AFiberCoordinates Γ) (x : V) :
    x ∈ A.allFibers ↔
      ∃ i : ZMod 19, x ∈ branchFiber Γ A.u (A.a i) := by
  classical
  simp [allFibers, mem_fiberUnion_iff]

/-- A coordinate representative lies in the corresponding selected A-fiber
union. -/
theorem coord_mem_fiberUnion (A : AFiberCoordinates Γ)
    {indices : Finset (ZMod 19)} {i : ZMod 19} (hi : i ∈ indices)
    (p : A.P) :
    ((A.coord i p : {x : V // x ∈ branchFiber Γ A.u (A.a i)}) : V) ∈
      A.fiberUnion indices := by
  classical
  exact (A.mem_fiberUnion_iff indices _).mpr
    ⟨i, hi, A.coord_mem i p⟩

end AFiberCoordinates

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- A finset whose vertices are fixed by `rotation 1` is disjoint from a
finset whose vertices are all moved by `rotation 1`. -/
theorem disjoint_of_rotation_one_fixed_moved
    {fixed moved : Finset V}
    (hfixed : ∀ ⦃y : V⦄, y ∈ fixed → h.rotation 1 y = y)
    (hmoved : ∀ ⦃y : V⦄, y ∈ moved → h.rotation 1 y ≠ y) :
    Disjoint fixed moved := by
  rw [Finset.disjoint_left]
  intro y hyfixed hymoved
  exact hmoved hymoved (hfixed hyfixed)

end D19ActsOnMoore57

/-- The A-fiber side of a reflection residual, represented semantically as a
union of fibers from an `AFiberCoordinates` structure.  The `moved` field is
the intended "non-fixed side" condition for the split. -/
structure ReflectionResidualAFiberSide
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h)
    (k : ZMod 19) where
  /-- A coordinate system for the A-side fibers. -/
  coords : AFiberCoordinates.{u, uP} Γ
  /-- The A-side fiber indices used in the residual. -/
  indices : Finset (ZMod 19)
  /-- The selected A-fiber union is contained in the canonical residual. -/
  subset_residual :
    coords.fiberUnion indices ≤ reflectionCopyResidual h input.base k
  /-- The selected A-fiber union is on the non-fixed side of the split. -/
  moved :
    ∀ ⦃y : V⦄, y ∈ coords.fiberUnion indices → h.rotation 1 y ≠ y

namespace ReflectionResidualAFiberSide

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}
variable {k : ZMod 19}

/-- The actual finset supplied as `aPart` to the older witness. -/
noncomputable abbrev aPart
    (side : ReflectionResidualAFiberSide h input k) : Finset V :=
  side.coords.fiberUnion side.indices

theorem aPart_subset_residual
    (side : ReflectionResidualAFiberSide h input k) :
    side.aPart ≤ reflectionCopyResidual h input.base k :=
  side.subset_residual

theorem mem_aPart_iff (side : ReflectionResidualAFiberSide h input k)
    (y : V) :
    y ∈ side.aPart ↔
      ∃ i : ZMod 19, i ∈ side.indices ∧
        y ∈ branchFiber Γ side.coords.u (side.coords.a i) :=
  side.coords.mem_fiberUnion_iff side.indices y

theorem moved_of_mem_aPart
    (side : ReflectionResidualAFiberSide h input k)
    {y : V} (hy : y ∈ side.aPart) :
    h.rotation 1 y ≠ y :=
  side.moved hy

end ReflectionResidualAFiberSide

/-- Avoidance split data whose A-side residual part is built from
`AFiberCoordinates`, rather than supplied as an arbitrary finset. -/
structure AdjacentMovedReflectionAFiberSplit38Data
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion
  fixedPart : Finset V
  /-- The fixed side really consists of vertices fixed by the basic rotation. -/
  fixedPart_fixed :
    ∀ ⦃y : V⦄, y ∈ fixedPart → h.rotation 1 y = y
  /-- The A-fiber side of the residual. -/
  aSide : ReflectionResidualAFiberSide.{u, uP} h input k
  residual_eq :
    reflectionCopyResidual h input.base k = fixedPart ∪ aSide.aPart
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      (fixedPart.filter fun y => Γ.Adj y (h.rotation d y)).card +
          (aSide.aPart.filter fun y => Γ.Adj y (h.rotation d y)).card =
        38

namespace AdjacentMovedReflectionAFiberSplit38Data

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- The A-fiber finset underlying the split. -/
noncomputable abbrev aPart
    (data : AdjacentMovedReflectionAFiberSplit38Data h input) : Finset V :=
  data.aSide.aPart

/-- The semantic fixed/moved side conditions imply the disjointness required by
the older split witness. -/
theorem parts_disjoint
    (data : AdjacentMovedReflectionAFiberSplit38Data h input) :
    Disjoint data.fixedPart data.aPart :=
  h.disjoint_of_rotation_one_fixed_moved data.fixedPart_fixed data.aSide.moved

/-- Convert the A-fiber split criterion to the existing avoidance split
witness. -/
noncomputable def toAvoidanceSplit38Witness
    (data : AdjacentMovedReflectionAFiberSplit38Data h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input where
  k := data.k
  reflection_not_mem_orbitFamilyUnion :=
    data.reflection_not_mem_orbitFamilyUnion
  fixedPart := data.fixedPart
  aPart := data.aPart
  parts_disjoint := data.parts_disjoint
  residual_eq := data.residual_eq
  residual_contribution := data.residual_contribution

end AdjacentMovedReflectionAFiberSplit38Data

namespace AdjacentMovedReflectionAvoidanceSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from an A-fiber residual split to the existing
avoidance split witness. -/
noncomputable def of_aFiberSplit
    (data : AdjacentMovedReflectionAFiberSplit38Data h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  data.toAvoidanceSplit38Witness

/-- A predicate-like package saying that an existing avoidance split witness
already has its `aPart` coming from selected A-fibers and respects the
fixed/non-fixed split. -/
structure AFiberCriteria
    (w : AdjacentMovedReflectionAvoidanceSplit38Witness h input) where
  coords : AFiberCoordinates.{u, uP} Γ
  indices : Finset (ZMod 19)
  aPart_eq : w.aPart = coords.fiberUnion indices
  fixedPart_fixed :
    ∀ ⦃y : V⦄, y ∈ w.fixedPart → h.rotation 1 y = y
  aPart_moved :
    ∀ ⦃y : V⦄, y ∈ coords.fiberUnion indices → h.rotation 1 y ≠ y

namespace AFiberCriteria

variable {w : AdjacentMovedReflectionAvoidanceSplit38Witness h input}

theorem mem_aPart_iff (c : AFiberCriteria w) (y : V) :
    y ∈ w.aPart ↔
      ∃ i : ZMod 19, i ∈ c.indices ∧
        y ∈ branchFiber Γ c.coords.u (c.coords.a i) := by
  rw [c.aPart_eq]
  exact c.coords.mem_fiberUnion_iff c.indices y

end AFiberCriteria

end AdjacentMovedReflectionAvoidanceSplit38Witness

end Moore57
