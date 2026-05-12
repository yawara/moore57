import Moore57.D19OnMoore57.AdjacentMoved.Reflection
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionFixedPart
import Moore57.D19OnMoore57.Rotation.OneMovingResidualProperties
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

/-!
# Canonical fixed side with an A-fiber residual side

This file combines the two refinements of
`AdjacentMovedReflectionAvoidanceSplit38Witness`: the fixed side is the
canonical `rotationOneFixedResidualPart`, and the A-side is supplied by a
`ReflectionResidualAFiberSide`.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Avoidance split data with the canonical rotation-fixed residual side and
an A-fiber moved side. -/
structure AdjacentMovedReflectionFixedAFiberCriteria38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion
  aSide : ReflectionResidualAFiberSide.{u, uP} h input k
  residual_eq :
    reflectionCopyResidual h input.base k =
      rotationOneFixedResidualPart h input k ∪ aSide.aPart
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((rotationOneFixedResidualPart h input k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card +
        ((aSide.aPart).filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        38

namespace AdjacentMovedReflectionFixedAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- The canonical fixed side consists of vertices fixed by `h.rotation 1`. -/
theorem fixedPart_fixed
    (w : AdjacentMovedReflectionFixedAFiberCriteria38Witness h input)
    {y : V} (hy : y ∈ rotationOneFixedResidualPart h input w.k) :
    h.rotation 1 y = y := by
  exact mem_fixedVertexSet.mp (mem_rotationOneFixedResidualPart_iff.mp hy).1

/-- The canonical fixed side is disjoint from the A-fiber moved side. -/
theorem parts_disjoint
    (w : AdjacentMovedReflectionFixedAFiberCriteria38Witness h input) :
    Disjoint (rotationOneFixedResidualPart h input w.k) w.aSide.aPart :=
  h.disjoint_of_rotation_one_fixed_moved
    (by
      intro y hy
      exact w.fixedPart_fixed hy)
    w.aSide.moved

/-- The recorded A-fiber side is exactly the canonical moving complement of
the fixed residual side. -/
theorem aPart_eq_rotationOneMovingResidualPart
    (w : AdjacentMovedReflectionFixedAFiberCriteria38Witness h input) :
    w.aSide.aPart = rotationOneMovingResidualPart h input w.k := by
  classical
  ext y
  constructor
  · intro hy
    rw [mem_rotationOneMovingResidualPart_iff]
    refine ⟨w.aSide.aPart_subset_residual hy, ?_⟩
    intro hfixed
    exact w.aSide.moved hy (mem_fixedVertexSet.mp hfixed)
  · intro hy
    have hmem := mem_rotationOneMovingResidualPart_iff.mp hy
    have hyUnion :
        y ∈ rotationOneFixedResidualPart h input w.k ∪ w.aSide.aPart := by
      rw [← w.residual_eq]
      exact hmem.1
    rcases Finset.mem_union.mp hyUnion with hyFixed | hyA
    · exact False.elim (hmem.2 (mem_rotationOneFixedResidualPart_iff.mp hyFixed).1)
    · exact hyA

/-- Convert the combined fixed/A-fiber criterion to the existing avoidance
split witness. -/
noncomputable def toAvoidanceSplit38Witness
    (w : AdjacentMovedReflectionFixedAFiberCriteria38Witness h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input where
  k := w.k
  reflection_not_mem_orbitFamilyUnion :=
    w.reflection_not_mem_orbitFamilyUnion
  fixedPart := rotationOneFixedResidualPart h input w.k
  aPart := w.aSide.aPart
  parts_disjoint := w.parts_disjoint
  residual_eq := w.residual_eq
  residual_contribution := w.residual_contribution

end AdjacentMovedReflectionFixedAFiberCriteria38Witness

namespace AdjacentMovedReflectionAvoidanceSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the combined canonical fixed/A-fiber criterion. -/
noncomputable def of_fixedAFiberCriteria
    (w : AdjacentMovedReflectionFixedAFiberCriteria38Witness h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  w.toAvoidanceSplit38Witness

end AdjacentMovedReflectionAvoidanceSplit38Witness

end Moore57

/-!
# Canonical A-fiber side for the rotation-fixed residual split

This file packages the strongest canonical version of the split criterion:
the fixed side is `rotationOneFixedResidualPart`, and the moving side is
identified with a selected A-fiber union.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Canonical fixed/A-fiber criterion for the reflection residual.

The field `moving_eq_aFiber` is the canonical identification of the moving
residual complement with the chosen A-fiber union.  From this equality we
derive the `ReflectionResidualAFiberSide` residual containment, moved-side
condition, and residual split equation. -/
structure AdjacentMovedReflectionCanonicalAFiberCriteria38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion
  coords : AFiberCoordinates.{u, uP} Γ
  indices : Finset (ZMod 19)
  moving_eq_aFiber :
    rotationOneMovingResidualPart h input k = coords.fiberUnion indices
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((rotationOneFixedResidualPart h input k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card +
        ((coords.fiberUnion indices).filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        38

namespace AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- The selected A-fiber union is contained in the reflection-copy residual,
because it is the canonical moving residual part. -/
theorem subset_residual
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    w.coords.fiberUnion w.indices ≤ reflectionCopyResidual h input.base w.k := by
  intro y hy
  have hyMoving : y ∈ rotationOneMovingResidualPart h input w.k := by
    simpa [w.moving_eq_aFiber] using hy
  exact (mem_rotationOneMovingResidualPart_iff.mp hyMoving).1

/-- The selected A-fiber union lies on the moved side of `rotation 1`, again
because it is the canonical moving residual part. -/
theorem aFiber_moved
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    ∀ ⦃y : V⦄, y ∈ w.coords.fiberUnion w.indices →
      h.rotation 1 y ≠ y := by
  intro y hy hyFixed
  have hyMoving : y ∈ rotationOneMovingResidualPart h input w.k := by
    simpa [w.moving_eq_aFiber] using hy
  exact (mem_rotationOneMovingResidualPart_iff.mp hyMoving).2
    (mem_fixedVertexSet.mpr hyFixed)

/-- Build the `ReflectionResidualAFiberSide` required by the existing
fixed/A-fiber criterion. -/
noncomputable def toReflectionResidualAFiberSide
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    ReflectionResidualAFiberSide.{u, uP} h input w.k where
  coords := w.coords
  indices := w.indices
  subset_residual := w.subset_residual
  moved := w.aFiber_moved

/-- The reflection-copy residual is the canonical fixed side together with the
chosen A-fiber union. -/
theorem residual_eq
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    reflectionCopyResidual h input.base w.k =
      rotationOneFixedResidualPart h input w.k ∪
        w.coords.fiberUnion w.indices := by
  rw [reflectionCopyResidual_eq_rotationOneFixed_union_moving h input w.k,
    w.moving_eq_aFiber]

/-- Convert the canonical A-fiber criterion to the existing fixed/A-fiber
criterion. -/
noncomputable def toFixedAFiberCriteria38Witness
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    AdjacentMovedReflectionFixedAFiberCriteria38Witness h input where
  k := w.k
  reflection_not_mem_orbitFamilyUnion :=
    w.reflection_not_mem_orbitFamilyUnion
  aSide := w.toReflectionResidualAFiberSide
  residual_eq := w.residual_eq
  residual_contribution := w.residual_contribution

/-- Convert the canonical A-fiber criterion directly to the existing avoidance
split witness. -/
noncomputable def toAvoidanceSplit38Witness
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  w.toFixedAFiberCriteria38Witness.toAvoidanceSplit38Witness

end AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

namespace AdjacentMovedReflectionFixedAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the canonical A-fiber criterion. -/
noncomputable def of_canonicalAFiberCriteria
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    AdjacentMovedReflectionFixedAFiberCriteria38Witness h input :=
  w.toFixedAFiberCriteria38Witness

end AdjacentMovedReflectionFixedAFiberCriteria38Witness

namespace AdjacentMovedReflectionAvoidanceSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the canonical A-fiber criterion to the existing
avoidance split witness. -/
noncomputable def of_canonicalAFiberCriteria
    (w : AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  w.toAvoidanceSplit38Witness

end AdjacentMovedReflectionAvoidanceSplit38Witness

end Moore57

/-!
# Inclusion form of the canonical A-fiber criterion

This file replaces the direct equality between the canonical moving residual
part and the selected A-fiber union by the two inclusions that imply it.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Canonical A-fiber criterion stated by mutual containment instead of a
direct equality of finsets. -/
structure AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
    (h : D19ActsOnMoore57 V Γ) (input : OrbitBaseSelectionInput h) where
  k : ZMod 19
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (input.base r) ∉ input.orbitFamilyUnion
  coords : AFiberCoordinates.{u, uP} Γ
  indices : Finset (ZMod 19)
  moving_subset_aFiber :
    rotationOneMovingResidualPart h input k ⊆ coords.fiberUnion indices
  aFiber_subset_moving :
    coords.fiberUnion indices ⊆ rotationOneMovingResidualPart h input k
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((rotationOneFixedResidualPart h input k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card +
        ((coords.fiberUnion indices).filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        38

namespace AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- The two inclusion hypotheses recover the canonical moving/A-fiber
equality expected by the existing criterion. -/
theorem moving_eq_aFiber
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    rotationOneMovingResidualPart h input w.k =
      w.coords.fiberUnion w.indices :=
  Finset.Subset.antisymm w.moving_subset_aFiber w.aFiber_subset_moving

/-- Membership form of the canonical moving/A-fiber identification. -/
theorem mem_moving_iff_mem_aFiber
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) (y : V) :
    y ∈ rotationOneMovingResidualPart h input w.k ↔
      y ∈ w.coords.fiberUnion w.indices := by
  constructor
  · intro hy
    exact w.moving_subset_aFiber hy
  · intro hy
    exact w.aFiber_subset_moving hy

/-- Symmetric membership form, useful when the A-fiber side is the starting
point. -/
theorem mem_aFiber_iff_mem_moving
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) (y : V) :
    y ∈ w.coords.fiberUnion w.indices ↔
      y ∈ rotationOneMovingResidualPart h input w.k :=
  (w.mem_moving_iff_mem_aFiber y).symm

/-- Convert the inclusion-form criterion to the existing equality-form
canonical A-fiber criterion. -/
noncomputable def toCanonicalAFiberCriteria38Witness
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input where
  k := w.k
  reflection_not_mem_orbitFamilyUnion :=
    w.reflection_not_mem_orbitFamilyUnion
  coords := w.coords
  indices := w.indices
  moving_eq_aFiber := w.moving_eq_aFiber
  residual_contribution := w.residual_contribution

/-- Convert the inclusion-form criterion directly to the existing fixed/A-fiber
criterion. -/
noncomputable def toFixedAFiberCriteria38Witness
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    AdjacentMovedReflectionFixedAFiberCriteria38Witness h input :=
  w.toCanonicalAFiberCriteria38Witness.toFixedAFiberCriteria38Witness

/-- Convert the inclusion-form criterion directly to the existing avoidance
split witness. -/
noncomputable def toAvoidanceSplit38Witness
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  w.toCanonicalAFiberCriteria38Witness.toAvoidanceSplit38Witness

end AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness

namespace AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the inclusion-form canonical A-fiber criterion. -/
noncomputable def of_inclusionCriteria
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    AdjacentMovedReflectionCanonicalAFiberCriteria38Witness h input :=
  w.toCanonicalAFiberCriteria38Witness

end AdjacentMovedReflectionCanonicalAFiberCriteria38Witness

namespace AdjacentMovedReflectionFixedAFiberCriteria38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the inclusion-form canonical A-fiber criterion. -/
noncomputable def of_canonicalAFiberInclusionCriteria
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    AdjacentMovedReflectionFixedAFiberCriteria38Witness h input :=
  w.toFixedAFiberCriteria38Witness

end AdjacentMovedReflectionFixedAFiberCriteria38Witness

namespace AdjacentMovedReflectionAvoidanceSplit38Witness

variable {h : D19ActsOnMoore57 V Γ}
variable {input : OrbitBaseSelectionInput h}

/-- Constructor wrapper from the inclusion-form canonical A-fiber criterion to
the existing avoidance split witness. -/
noncomputable def of_canonicalAFiberInclusionCriteria
    (w : AdjacentMovedReflectionCanonicalAFiberInclusionCriteria38Witness
      h input) :
    AdjacentMovedReflectionAvoidanceSplit38Witness h input :=
  w.toAvoidanceSplit38Witness

end AdjacentMovedReflectionAvoidanceSplit38Witness

end Moore57

