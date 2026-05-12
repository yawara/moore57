import Moore57.D19OnMoore57.Rotation.RotationOneFixedBoundBoundary

/-!
# Nonempty bridges for the rotation-one fixed-bound boundary

This file records `Nonempty`-level bridges from the final boundary package
`RotationOneFixedBoundBoundaryInput` back to the existing fixed-point criteria.
It avoids adding new fixed-bound assumptions by reusing the established
constructors and consequences of `fixedVertexCount (h.rotation 1) ≤ 19`.
-/

namespace Moore57

namespace D19ActsOnMoore57

universe u uι

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace RotationOneFixedBoundBoundaryInput

variable {h : D19ActsOnMoore57 V Γ}

/-- A boundary package gives a generic rotation-one fixed-bound witness. -/
theorem nonempty_to_rotationOneFixedBoundWitness :
    Nonempty (RotationOneFixedBoundBoundaryInput h) →
      Nonempty (RotationOneFixedBoundWitness.{u, uι} h) := by
  classical
  rintro ⟨data⟩
  let e := Fintype.equivFin (fixedVertexSet (h.rotation 1))
  have hcard : Fintype.card (fixedVertexSet (h.rotation 1)) ≤ 19 :=
    by simpa [fixedVertexCount_eq_card_fixedVertexSet] using
      data.rotationOneFixedCount_le_nineteen
  let f : fixedVertexSet (h.rotation 1) → Fin 19 :=
    fun x => ⟨(e x).val, lt_of_lt_of_le (e x).isLt hcard⟩
  refine ⟨{
    ι := ULift.{uι, 0} (Fin 19)
    fintype_ι := inferInstance
    card_le_nineteen := by simp
    fixedEmbedding := {
      toFun x := ULift.up (f x)
      inj' := by
        intro x y hxy
        have hf : f x = f y := congrArg ULift.down hxy
        apply e.injective
        ext
        simpa [f] using congrArg Fin.val hf
    }
  }⟩

/-- A generic rotation-one fixed-bound witness gives a boundary package. -/
theorem nonempty_of_rotationOneFixedBoundWitness :
    Nonempty (RotationOneFixedBoundWitness.{u, uι} h) →
      Nonempty (RotationOneFixedBoundBoundaryInput h) := by
  rintro ⟨w⟩
  exact ⟨ofRotationOneFixedBoundWitness w⟩

/-- The boundary package is equivalent, at the `Nonempty` level, to the
generic rotation-one fixed-bound witness. -/
theorem nonempty_iff_rotationOneFixedBoundWitness :
    Nonempty (RotationOneFixedBoundBoundaryInput h) ↔
      Nonempty (RotationOneFixedBoundWitness.{u, uι} h) := by
  constructor
  · exact nonempty_to_rotationOneFixedBoundWitness
  · exact nonempty_of_rotationOneFixedBoundWitness

/-- A cardinality bound on the rotation-one fixed set gives a boundary
package at the `Nonempty` level. -/
theorem nonempty_of_fixedVertexSet_card_le_nineteen
    (hcard : Fintype.card (fixedVertexSet (h.rotation 1)) ≤ 19) :
    Nonempty (RotationOneFixedBoundBoundaryInput h) := by
  exact ⟨{
    rotationOneFixedCount_le_nineteen := by
      simpa [fixedVertexCount_eq_card_fixedVertexSet] using hcard
  }⟩

/-- The boundary package is equivalent, at the `Nonempty` level, to the
cardinality bound on the rotation-one fixed set. -/
theorem nonempty_iff_fixedVertexSet_card_le_nineteen :
    Nonempty (RotationOneFixedBoundBoundaryInput h) ↔
      Fintype.card (fixedVertexSet (h.rotation 1)) ≤ 19 := by
  constructor
  · rintro ⟨data⟩
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using
      data.rotationOneFixedCount_le_nineteen
  · exact nonempty_of_fixedVertexSet_card_le_nineteen

/-- A boundary package forces the exact rotation-one fixed count. -/
theorem rotationOneFixedCount_eq_one_of_nonempty
    (hne : Nonempty (RotationOneFixedBoundBoundaryInput h)) :
    fixedVertexCount (h.rotation 1) = 1 := by
  rcases hne with ⟨data⟩
  exact data.toRotationFixedUpperBoundInput.rotation_one_fixed_count_eq_one

/-- Exact rotation-one fixed count gives a boundary package at the `Nonempty`
level. -/
theorem nonempty_of_fixedVertexCount_eq_one
    (hcount : fixedVertexCount (h.rotation 1) = 1) :
    Nonempty (RotationOneFixedBoundBoundaryInput h) := by
  exact ⟨{
    rotationOneFixedCount_le_nineteen := by
      rw [hcount]
      decide
  }⟩

/-- The boundary package is equivalent, at the `Nonempty` level, to exact
rotation-one fixed count `1`. -/
theorem nonempty_iff_fixedVertexCount_eq_one :
    Nonempty (RotationOneFixedBoundBoundaryInput h) ↔
      fixedVertexCount (h.rotation 1) = 1 := by
  constructor
  · exact rotationOneFixedCount_eq_one_of_nonempty
  · exact nonempty_of_fixedVertexCount_eq_one

/-- A boundary package forces cardinality one for the rotation-one fixed set. -/
theorem fixedVertexSet_card_eq_one_of_nonempty
    (hne : Nonempty (RotationOneFixedBoundBoundaryInput h)) :
    Fintype.card (fixedVertexSet (h.rotation 1)) = 1 := by
  simpa [fixedVertexCount_eq_card_fixedVertexSet] using
    rotationOneFixedCount_eq_one_of_nonempty (h := h) hne

/-- Cardinality one for the rotation-one fixed set gives a boundary package at
the `Nonempty` level. -/
theorem nonempty_of_fixedVertexSet_card_eq_one
    (hcard : Fintype.card (fixedVertexSet (h.rotation 1)) = 1) :
    Nonempty (RotationOneFixedBoundBoundaryInput h) := by
  exact nonempty_of_fixedVertexCount_eq_one (h := h)
    (by simpa [fixedVertexCount_eq_card_fixedVertexSet] using hcard)

/-- The boundary package is equivalent, at the `Nonempty` level, to
cardinality one of the rotation-one fixed set. -/
theorem nonempty_iff_fixedVertexSet_card_eq_one :
    Nonempty (RotationOneFixedBoundBoundaryInput h) ↔
      Fintype.card (fixedVertexSet (h.rotation 1)) = 1 := by
  constructor
  · exact fixedVertexSet_card_eq_one_of_nonempty
  · exact nonempty_of_fixedVertexSet_card_eq_one

/-- A boundary package gives a unique fixed point for rotation by `1`. -/
theorem existsUnique_rotation_one_fixed_of_nonempty
    (hne : Nonempty (RotationOneFixedBoundBoundaryInput h)) :
    ∃! v : V, h.rotation 1 v = v :=
  h.existsUnique_rotation_one_fixed_of_fixedVertexCount_eq_one
    (rotationOneFixedCount_eq_one_of_nonempty (h := h) hne)

/-- A unique fixed point for rotation by `1` gives a boundary package at the
`Nonempty` level. -/
theorem nonempty_of_existsUnique_rotation_one_fixed
    (hunique : ∃! v : V, h.rotation 1 v = v) :
    Nonempty (RotationOneFixedBoundBoundaryInput h) := by
  exact ⟨of_existsUnique_rotation_one_fixed hunique⟩

/-- The boundary package is equivalent, at the `Nonempty` level, to a unique
fixed point for rotation by `1`. -/
theorem nonempty_iff_existsUnique_rotation_one_fixed :
    Nonempty (RotationOneFixedBoundBoundaryInput h) ↔
      ∃! v : V, h.rotation 1 v = v := by
  constructor
  · exact existsUnique_rotation_one_fixed_of_nonempty
  · exact nonempty_of_existsUnique_rotation_one_fixed

/-- A boundary package identifies the rotation-one fixed set with a
singleton. -/
theorem exists_fixedVertexSet_rotation_one_eq_singleton_of_nonempty
    (hne : Nonempty (RotationOneFixedBoundBoundaryInput h)) :
    ∃ v0 : V, fixedVertexSet (h.rotation 1) = ({v0} : Set V) :=
  h.exists_fixedVertexSet_rotation_one_eq_singleton_of_fixedVertexCount_eq_one
    (rotationOneFixedCount_eq_one_of_nonempty (h := h) hne)

/-- A singleton rotation-one fixed set gives a boundary package at the
`Nonempty` level. -/
theorem nonempty_of_fixedVertexSet_eq_singleton
    {v0 : V}
    (hset : fixedVertexSet (h.rotation 1) = ({v0} : Set V)) :
    Nonempty (RotationOneFixedBoundBoundaryInput h) := by
  exact ⟨of_fixedVertexSet_eq_singleton hset⟩

/-- An existential singleton description of the rotation-one fixed set gives a
boundary package at the `Nonempty` level. -/
theorem nonempty_of_exists_fixedVertexSet_rotation_one_eq_singleton
    (hset : ∃ v0 : V, fixedVertexSet (h.rotation 1) = ({v0} : Set V)) :
    Nonempty (RotationOneFixedBoundBoundaryInput h) := by
  rcases hset with ⟨v0, hv0⟩
  exact nonempty_of_fixedVertexSet_eq_singleton (h := h) (v0 := v0) hv0

/-- The boundary package is equivalent, at the `Nonempty` level, to a
singleton description of the rotation-one fixed set. -/
theorem nonempty_iff_exists_fixedVertexSet_rotation_one_eq_singleton :
    Nonempty (RotationOneFixedBoundBoundaryInput h) ↔
      ∃ v0 : V, fixedVertexSet (h.rotation 1) = ({v0} : Set V) := by
  constructor
  · exact exists_fixedVertexSet_rotation_one_eq_singleton_of_nonempty
  · exact nonempty_of_exists_fixedVertexSet_rotation_one_eq_singleton

/-- A boundary package makes the rotation-one fixed set a subsingleton. -/
theorem fixedVertexSet_subsingleton_of_nonempty
    (hne : Nonempty (RotationOneFixedBoundBoundaryInput h)) :
    (fixedVertexSet (h.rotation 1)).Subsingleton := by
  rcases exists_fixedVertexSet_rotation_one_eq_singleton_of_nonempty
      (h := h) hne with
    ⟨v0, hset⟩
  rw [hset]
  exact Set.subsingleton_singleton

/-- A subsingleton rotation-one fixed set gives a boundary package at the
`Nonempty` level. -/
theorem nonempty_of_fixedVertexSet_subsingleton
    (hss : (fixedVertexSet (h.rotation 1)).Subsingleton) :
    Nonempty (RotationOneFixedBoundBoundaryInput h) := by
  exact ⟨of_fixedVertexSet_subsingleton hss⟩

/-- The boundary package is equivalent, at the `Nonempty` level, to the
rotation-one fixed set being a subsingleton. -/
theorem nonempty_iff_fixedVertexSet_subsingleton :
    Nonempty (RotationOneFixedBoundBoundaryInput h) ↔
      (fixedVertexSet (h.rotation 1)).Subsingleton := by
  constructor
  · exact fixedVertexSet_subsingleton_of_nonempty
  · exact nonempty_of_fixedVertexSet_subsingleton

end RotationOneFixedBoundBoundaryInput

namespace RotationOneFixedBoundWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Symmetric spelling of the boundary/witness `Nonempty` bridge from the
boundary namespace. -/
theorem nonempty_iff_boundaryInput :
    Nonempty (RotationOneFixedBoundWitness.{u, uι} h) ↔
      Nonempty (RotationOneFixedBoundBoundaryInput h) :=
  RotationOneFixedBoundBoundaryInput.nonempty_iff_rotationOneFixedBoundWitness.symm

end RotationOneFixedBoundWitness

end D19ActsOnMoore57

end Moore57
