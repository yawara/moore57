import Moore57.D19OnMoore57.Fixed.FixedUpperBoundEnumeration

/-!
# Rotation fixed enumerations from cardinality bounds

This file packages cardinality bounds for the rotation-one fixed set as
`RotationOneFixedEnumeration` records, and then as `RotationFixedUpperBoundInput`
records.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace RotationOneFixedEnumeration

variable {h : D19ActsOnMoore57 V Γ}

/-- A cardinality bound for the rotation-one fixed subtype gives the canonical
enumeration by its `Set.toFinset`. -/
noncomputable def of_fixedVertexSet_card_le_nineteen
    (hcard : Fintype.card (fixedVertexSet (h.rotation 1)) ≤ 19) :
    RotationOneFixedEnumeration h where
  carrier := (fixedVertexSet (h.rotation 1)).toFinset
  covers := by
    intro v hv
    simpa using hv
  card_le_nineteen := by
    rw [Set.toFinset_card]
    exact hcard

/-- A fixed-count bound for rotation by `1` gives the canonical fixed
enumeration. -/
noncomputable def of_fixedVertexCount_le_nineteen
    (hcount : fixedVertexCount (h.rotation 1) ≤ 19) :
    RotationOneFixedEnumeration h :=
  of_fixedVertexSet_card_le_nineteen
    (h := h) (by simpa [fixedVertexCount_eq_card_fixedVertexSet] using hcount)

/-- Exact cardinality one is a convenient special case of the cardinality
bound constructor. -/
noncomputable def of_fixedVertexSet_card_eq_one
    (hcard : Fintype.card (fixedVertexSet (h.rotation 1)) = 1) :
    RotationOneFixedEnumeration h :=
  of_fixedVertexSet_card_le_nineteen (h := h) (by omega)

/-- Exact fixed count one is a convenient special case of the fixed-count bound
constructor. -/
noncomputable def of_fixedVertexCount_eq_one
    (hcount : fixedVertexCount (h.rotation 1) = 1) :
    RotationOneFixedEnumeration h :=
  of_fixedVertexCount_le_nineteen (h := h) (by omega)

end RotationOneFixedEnumeration

namespace RotationFixedUpperBoundInput

variable {h : D19ActsOnMoore57 V Γ}

/-- A cardinality bound for the rotation-one fixed subtype gives the coarse
upper-bound input. -/
noncomputable def of_fixedVertexSet_card_le_nineteen
    (hcard : Fintype.card (fixedVertexSet (h.rotation 1)) ≤ 19) :
    RotationFixedUpperBoundInput h :=
  (RotationOneFixedEnumeration.of_fixedVertexSet_card_le_nineteen
    (h := h) hcard).toRotationFixedUpperBoundInput

/-- A fixed-count bound for rotation by `1` gives the coarse upper-bound
input. -/
noncomputable def of_fixedVertexCount_le_nineteen
    (hcount : fixedVertexCount (h.rotation 1) ≤ 19) :
    RotationFixedUpperBoundInput h :=
  (RotationOneFixedEnumeration.of_fixedVertexCount_le_nineteen
    (h := h) hcount).toRotationFixedUpperBoundInput

/-- Exact cardinality one gives the coarse upper-bound input. -/
noncomputable def of_fixedVertexSet_card_eq_one
    (hcard : Fintype.card (fixedVertexSet (h.rotation 1)) = 1) :
    RotationFixedUpperBoundInput h :=
  (RotationOneFixedEnumeration.of_fixedVertexSet_card_eq_one
    (h := h) hcard).toRotationFixedUpperBoundInput

/-- Exact fixed count one gives the coarse upper-bound input. -/
noncomputable def of_fixedVertexCount_eq_one
    (hcount : fixedVertexCount (h.rotation 1) = 1) :
    RotationFixedUpperBoundInput h :=
  (RotationOneFixedEnumeration.of_fixedVertexCount_eq_one
    (h := h) hcount).toRotationFixedUpperBoundInput

end RotationFixedUpperBoundInput

end D19ActsOnMoore57

end Moore57
