import Moore57.D19OnMoore57.Rotation.RotationFixedUniqueCriteria

/-!
# Unique fixed point from exact rotation fixed count

This file adds the reverse direction to `RotationFixedUniqueCriteria`: an exact
rotation-one fixed count of `1` produces a unique fixed point.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Cardinality one of the rotation-one fixed subtype gives a unique fixed
vertex for rotation by `1`. -/
theorem existsUnique_rotation_one_fixed_of_fixedVertexSet_card_eq_one
    (h : D19ActsOnMoore57 V Γ)
    (hcard : Fintype.card (fixedVertexSet (h.rotation 1)) = 1) :
    ∃! v : V, h.rotation 1 v = v := by
  classical
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨x, hx⟩
  refine ⟨(x : V), ?_, ?_⟩
  · change h.rotation 1 (x : V) = (x : V)
    exact x.2
  intro y hy
  exact congrArg Subtype.val (hx ⟨y, by simpa using hy⟩)

/-- Exact rotation-one fixed count `1` gives a unique fixed vertex for rotation
by `1`. -/
theorem existsUnique_rotation_one_fixed_of_fixedVertexCount_eq_one
    (h : D19ActsOnMoore57 V Γ)
    (hcount : fixedVertexCount (h.rotation 1) = 1) :
    ∃! v : V, h.rotation 1 v = v :=
  h.existsUnique_rotation_one_fixed_of_fixedVertexSet_card_eq_one
    (by simpa [fixedVertexCount_eq_card_fixedVertexSet] using hcount)

/-- Cardinality one of the rotation-one fixed subtype identifies the fixed set
with a singleton. -/
theorem exists_fixedVertexSet_rotation_one_eq_singleton_of_card_eq_one
    (h : D19ActsOnMoore57 V Γ)
    (hcard : Fintype.card (fixedVertexSet (h.rotation 1)) = 1) :
    ∃ v0 : V, fixedVertexSet (h.rotation 1) = ({v0} : Set V) :=
  h.exists_fixedVertexSet_rotation_one_eq_singleton_of_existsUnique
    (h.existsUnique_rotation_one_fixed_of_fixedVertexSet_card_eq_one hcard)

/-- Exact rotation-one fixed count `1` identifies the fixed set with a
singleton. -/
theorem exists_fixedVertexSet_rotation_one_eq_singleton_of_fixedVertexCount_eq_one
    (h : D19ActsOnMoore57 V Γ)
    (hcount : fixedVertexCount (h.rotation 1) = 1) :
    ∃ v0 : V, fixedVertexSet (h.rotation 1) = ({v0} : Set V) :=
  h.exists_fixedVertexSet_rotation_one_eq_singleton_of_card_eq_one
    (by simpa [fixedVertexCount_eq_card_fixedVertexSet] using hcount)

namespace RotationOneFixedBoundWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Cardinality one of the rotation-one fixed subtype gives the generic
fixed-bound witness via the unique fixed-point constructor. -/
def of_fixedVertexSet_card_eq_one
    (hcard : Fintype.card (fixedVertexSet (h.rotation 1)) = 1) :
    RotationOneFixedBoundWitness h :=
  of_existsUnique_rotation_one_fixed
    (h.existsUnique_rotation_one_fixed_of_fixedVertexSet_card_eq_one hcard)

/-- Exact rotation-one fixed count `1` gives the generic fixed-bound witness
via the unique fixed-point constructor. -/
def of_fixedVertexCount_eq_one
    (hcount : fixedVertexCount (h.rotation 1) = 1) :
    RotationOneFixedBoundWitness h :=
  of_existsUnique_rotation_one_fixed
    (h.existsUnique_rotation_one_fixed_of_fixedVertexCount_eq_one hcount)

end RotationOneFixedBoundWitness

namespace RotationFixedUpperBoundInput

/-- Cardinality one of the rotation-one fixed subtype builds the coarse
upper-bound input. -/
def of_rotation_one_fixedVertexSet_card_eq_one
    (h : D19ActsOnMoore57 V Γ)
    (hcard : Fintype.card (fixedVertexSet (h.rotation 1)) = 1) :
    RotationFixedUpperBoundInput h :=
  (RotationOneFixedBoundWitness.of_fixedVertexSet_card_eq_one
    (h := h) hcard).toRotationFixedUpperBoundInput

/-- Exact rotation-one fixed count `1` builds the coarse upper-bound input. -/
def of_rotation_one_fixedVertexCount_eq_one
    (h : D19ActsOnMoore57 V Γ)
    (hcount : fixedVertexCount (h.rotation 1) = 1) :
    RotationFixedUpperBoundInput h :=
  (RotationOneFixedBoundWitness.of_fixedVertexCount_eq_one
    (h := h) hcount).toRotationFixedUpperBoundInput

end RotationFixedUpperBoundInput

end D19ActsOnMoore57

end Moore57
