import Moore57.FixedUpperBoundCriteria
import Moore57.FixedUpperBoundEnumeration
import Moore57.RotationFixedUniqueCriteria
import Moore57.RotationFixedUpperBoundFromData

/-!
# Rotation-one fixed-bound boundary wrappers

This file keeps the final-boundary assumption
`fixedVertexCount (h.rotation 1) ≤ 19` as a small record, and provides
lossless conversions from the stronger fixed-point criteria already used
elsewhere: unique fixed point, finite enumeration, and subset finset data.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final-boundary package for the rotation-one fixed-count upper bound. -/
structure RotationOneFixedBoundBoundaryInput
    (h : D19ActsOnMoore57 V Γ) where
  /-- The final-boundary fixed-count assumption for rotation by `1`. -/
  rotationOneFixedCount_le_nineteen :
    fixedVertexCount (h.rotation 1) ≤ 19

namespace RotationOneFixedBoundBoundaryInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Turn the boundary package into the coarse upper-bound input for all
nontrivial rotations. -/
def toRotationFixedUpperBoundInput
    (data : RotationOneFixedBoundBoundaryInput h) :
    RotationFixedUpperBoundInput h :=
  RotationFixedUpperBoundInput.of_rotation_one_le_nineteen
    data.rotationOneFixedCount_le_nineteen

/-- Turn the boundary package into the canonical finite enumeration of the
rotation-one fixed vertices. -/
noncomputable def toRotationOneFixedEnumeration
    (data : RotationOneFixedBoundBoundaryInput h) :
    RotationOneFixedEnumeration h :=
  RotationOneFixedEnumeration.of_fixedVertexCount_le_nineteen
    data.rotationOneFixedCount_le_nineteen

/-- Read the boundary package back from the coarse upper-bound input. -/
def ofRotationFixedUpperBoundInput
    (input : RotationFixedUpperBoundInput h) :
    RotationOneFixedBoundBoundaryInput h where
  rotationOneFixedCount_le_nineteen := input.fixed_le_nineteen 1 (by decide)

/-- Build the boundary package from a generic rotation-one fixed-bound
witness. -/
def ofRotationOneFixedBoundWitness
    (w : RotationOneFixedBoundWitness h) :
    RotationOneFixedBoundBoundaryInput h where
  rotationOneFixedCount_le_nineteen :=
    w.fixedVertexCount_rotation_one_le_nineteen

/-- Build the boundary package from an explicit finite enumeration. -/
def ofRotationOneFixedEnumeration
    (e : RotationOneFixedEnumeration h) :
    RotationOneFixedBoundBoundaryInput h :=
  ofRotationOneFixedBoundWitness e.toRotationOneFixedBoundWitness

/-- Build the boundary package from a finite set covering all rotation-one
fixed vertices. -/
def of_subset_finset
    (s : Finset V)
    (hsub : ∀ ⦃v : V⦄, v ∈ fixedVertexSet (h.rotation 1) → v ∈ s)
    (hcard : s.card ≤ 19) :
    RotationOneFixedBoundBoundaryInput h :=
  ofRotationOneFixedBoundWitness
    (RotationOneFixedBoundWitness.of_subset_finset (h := h) s hsub hcard)

/-- Build the boundary package from an equivalence with a finite set of size
at most nineteen. -/
def of_equiv_finset
    (s : Finset V)
    (e : fixedVertexSet (h.rotation 1) ≃ s)
    (hcard : s.card ≤ 19) :
    RotationOneFixedBoundBoundaryInput h :=
  ofRotationOneFixedBoundWitness
    (RotationOneFixedBoundWitness.of_equiv_finset (h := h) s e hcard)

/-- Build the boundary package when the rotation-one fixed set is a
subsingleton. -/
def of_fixedVertexSet_subsingleton
    (hss : (fixedVertexSet (h.rotation 1)).Subsingleton) :
    RotationOneFixedBoundBoundaryInput h :=
  ofRotationOneFixedBoundWitness
    (RotationOneFixedBoundWitness.of_rotation_one_fixedVertexSet_subsingleton
      (h := h) hss)

/-- Build the boundary package from a singleton description of the
rotation-one fixed set. -/
def of_fixedVertexSet_eq_singleton
    {v0 : V}
    (hset : fixedVertexSet (h.rotation 1) = ({v0} : Set V)) :
    RotationOneFixedBoundBoundaryInput h :=
  ofRotationOneFixedBoundWitness
    (RotationOneFixedBoundWitness.of_rotation_one_fixedVertexSet_eq_singleton
      (h := h) hset)

/-- Build the boundary package from a unique fixed point for rotation by `1`. -/
def of_existsUnique_rotation_one_fixed
    (hunique : ∃! v : V, h.rotation 1 v = v) :
    RotationOneFixedBoundBoundaryInput h :=
  ofRotationOneFixedBoundWitness
    (RotationOneFixedBoundWitness.of_existsUnique_rotation_one_fixed
      (h := h) hunique)

/-- The boundary package is exactly the rotation-one fixed-count bound. -/
theorem nonempty_iff_rotationOneFixedCount_le_nineteen :
    Nonempty (RotationOneFixedBoundBoundaryInput h) ↔
      fixedVertexCount (h.rotation 1) ≤ 19 := by
  constructor
  · rintro ⟨data⟩
    exact data.rotationOneFixedCount_le_nineteen
  · intro hcount
    exact ⟨{ rotationOneFixedCount_le_nineteen := hcount }⟩

/-- The boundary package is equivalent, at the `Nonempty` level, to the coarse
upper-bound input for all nontrivial rotations. -/
theorem nonempty_iff_rotationFixedUpperBoundInput :
    Nonempty (RotationOneFixedBoundBoundaryInput h) ↔
      Nonempty (RotationFixedUpperBoundInput h) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toRotationFixedUpperBoundInput⟩
  · rintro ⟨input⟩
    exact ⟨ofRotationFixedUpperBoundInput input⟩

/-- The boundary package is equivalent, at the `Nonempty` level, to having a
finite rotation-one fixed enumeration. -/
theorem nonempty_iff_rotationOneFixedEnumeration :
    Nonempty (RotationOneFixedBoundBoundaryInput h) ↔
      Nonempty (RotationOneFixedEnumeration h) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toRotationOneFixedEnumeration⟩
  · rintro ⟨e⟩
    exact ⟨ofRotationOneFixedEnumeration e⟩

end RotationOneFixedBoundBoundaryInput

/-- A wrapper theorem exposing the final-boundary fixed-count conclusion from
a unique rotation-one fixed point. -/
theorem rotationOneFixedCount_le_nineteen_of_existsUnique_rotation_one_fixed
    (h : D19ActsOnMoore57 V Γ)
    (hunique : ∃! v : V, h.rotation 1 v = v) :
    fixedVertexCount (h.rotation 1) ≤ 19 :=
  (RotationOneFixedBoundBoundaryInput.of_existsUnique_rotation_one_fixed
    (h := h) hunique).rotationOneFixedCount_le_nineteen

/-- A wrapper theorem exposing the final-boundary fixed-count conclusion from
an explicit finite enumeration. -/
theorem rotationOneFixedCount_le_nineteen_of_enumeration
    {h : D19ActsOnMoore57 V Γ}
    (e : RotationOneFixedEnumeration h) :
    fixedVertexCount (h.rotation 1) ≤ 19 :=
  (RotationOneFixedBoundBoundaryInput.ofRotationOneFixedEnumeration e)
    |>.rotationOneFixedCount_le_nineteen

/-- A wrapper theorem exposing the final-boundary fixed-count conclusion from
a finite set covering all rotation-one fixed vertices. -/
theorem rotationOneFixedCount_le_nineteen_of_subset_finset
    (h : D19ActsOnMoore57 V Γ)
    (s : Finset V)
    (hsub : ∀ ⦃v : V⦄, v ∈ fixedVertexSet (h.rotation 1) → v ∈ s)
    (hcard : s.card ≤ 19) :
    fixedVertexCount (h.rotation 1) ≤ 19 :=
  (RotationOneFixedBoundBoundaryInput.of_subset_finset
    (h := h) s hsub hcard).rotationOneFixedCount_le_nineteen

end D19ActsOnMoore57

end Moore57
