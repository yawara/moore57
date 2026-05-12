import Moore57.D19OnMoore57.Rotation.FixedUpperBoundInputs
import Moore57.D19OnMoore57.Rotation.FixedCountUnique
import Moore57.D19OnMoore57.Fixed.UpperBoundEnumeration
import Moore57.D19OnMoore57.Rotation.FixedEnumerationFromCount

/-!
# Rotation fixed upper-bound inputs from fixed-point data

This file collects thin constructors for `RotationFixedUpperBoundInput` from
existing exact fixed-point, fixed-count, and fixed-set data.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace RotationFixedUpperBoundInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Exact fixed-point data for all nontrivial rotations gives the coarse
upper-bound input. -/
def of_rotationFixedData
    (hfixed : RotationFixedData h.rotation) :
    RotationFixedUpperBoundInput h where
  fixed_le_nineteen := by
    intro d hd
    rw [hfixed.rotation_fixed d hd]
    decide

/-- Exact fixed count `1` for every nontrivial rotation gives the coarse
upper-bound input. -/
def of_all_fixedVertexCount_eq_one
    (hcount : ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1) :
    RotationFixedUpperBoundInput h :=
  of_rotationFixedData (h := h) { rotation_fixed := hcount }

/-- The upper-bound input is equivalent to the rotation-one fixed-count bound. -/
theorem iff_fixedVertexCount_rotation_one_le_nineteen :
    RotationFixedUpperBoundInput h ↔
      fixedVertexCount (h.rotation 1) ≤ 19 := by
  constructor
  · intro hin
    exact hin.fixed_le_nineteen 1 (by decide)
  · intro hcount
    exact of_rotation_one_le_nineteen (h := h) hcount

/-- Alias for the canonical constructor from a rotation-one fixed-set
cardinality bound. -/
noncomputable def of_rotation_one_fixedVertexSet_card_le_nineteen
    (hcard : Fintype.card (fixedVertexSet (h.rotation 1)) ≤ 19) :
    RotationFixedUpperBoundInput h :=
  of_fixedVertexSet_card_le_nineteen (h := h) hcard

/-- Alias for the canonical constructor from an exact singleton cardinality of
the rotation-one fixed set. -/
noncomputable def of_rotation_one_fixedVertexSet_card_eq_one'
    (hcard : Fintype.card (fixedVertexSet (h.rotation 1)) = 1) :
    RotationFixedUpperBoundInput h :=
  of_fixedVertexSet_card_eq_one (h := h) hcard

/-- Alias for the canonical constructor from exact rotation-one fixed count
`1`. -/
noncomputable def of_rotation_one_fixedVertexCount_eq_one'
    (hcount : fixedVertexCount (h.rotation 1) = 1) :
    RotationFixedUpperBoundInput h :=
  of_fixedVertexCount_eq_one (h := h) hcount

/-- Alias for the singleton fixed-set constructor. -/
def of_fixedVertexSet_rotation_one_eq_singleton
    {v0 : V}
    (hset : fixedVertexSet (h.rotation 1) = ({v0} : Set V)) :
    RotationFixedUpperBoundInput h :=
  of_rotation_one_fixedVertexSet_eq_singleton (h := h) hset

/-- Alias for the unique fixed-point constructor. -/
def of_existsUnique_fixed_rotation_one
    (hunique : ∃! v : V, h.rotation 1 v = v) :
    RotationFixedUpperBoundInput h :=
  of_existsUnique_rotation_one_fixed (h := h) hunique

end RotationFixedUpperBoundInput

end D19ActsOnMoore57

end Moore57
