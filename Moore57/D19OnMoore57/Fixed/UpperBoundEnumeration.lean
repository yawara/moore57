import Moore57.D19OnMoore57.Fixed.UpperBoundCriteria

/-!
# Enumeration criteria for the rotation fixed upper bound

This file adds convenient constructors for `RotationFixedUpperBoundInput` from
explicit finite containers of the rotation-one fixed vertices.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A finite vertex enumeration covering all rotation-one fixed vertices. -/
structure RotationOneFixedEnumeration (h : D19ActsOnMoore57 V Γ) where
  /-- A finite set containing every fixed vertex of `h.rotation 1`. -/
  carrier : Finset V
  /-- Every rotation-one fixed vertex appears in the finite set. -/
  covers : ∀ ⦃v : V⦄, v ∈ fixedVertexSet (h.rotation 1) → v ∈ carrier
  /-- The enumeration has at most nineteen distinct vertices. -/
  card_le_nineteen : carrier.card ≤ 19

namespace RotationOneFixedBoundWitness

variable {h : D19ActsOnMoore57 V Γ}

/-- Build a fixed-bound witness from a finite set containing every
rotation-one fixed vertex. -/
def of_subset_finset
    (s : Finset V)
    (hsub : ∀ ⦃v : V⦄, v ∈ fixedVertexSet (h.rotation 1) → v ∈ s)
    (hcard : s.card ≤ 19) :
    RotationOneFixedBoundWitness h where
  ι := s
  fintype_ι := inferInstance
  card_le_nineteen := by
    simpa using hcard
  fixedEmbedding := {
    toFun x := ⟨x.1, hsub x.2⟩
    inj' := by
      intro x y hxy
      ext
      exact congrArg (fun z : s => (z : V)) hxy
  }

/-- Build a fixed-bound witness from a finite set exactly equivalent to the
rotation-one fixed vertices. -/
def of_equiv_finset
    (s : Finset V)
    (e : fixedVertexSet (h.rotation 1) ≃ s)
    (hcard : s.card ≤ 19) :
    RotationOneFixedBoundWitness h where
  ι := s
  fintype_ι := inferInstance
  card_le_nineteen := by
    simpa using hcard
  fixedEmbedding := e.toEmbedding

end RotationOneFixedBoundWitness

namespace RotationOneFixedEnumeration

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert an explicit finite enumeration into the generic fixed-bound
witness. -/
def toRotationOneFixedBoundWitness
    (e : RotationOneFixedEnumeration h) :
    RotationOneFixedBoundWitness h :=
  RotationOneFixedBoundWitness.of_subset_finset
    e.carrier e.covers e.card_le_nineteen

/-- Convert an explicit finite enumeration into the upper-bound input used by
the D19 reduction. -/
def toRotationFixedUpperBoundInput
    (e : RotationOneFixedEnumeration h) :
    RotationFixedUpperBoundInput h :=
  e.toRotationOneFixedBoundWitness.toRotationFixedUpperBoundInput

end RotationOneFixedEnumeration

/-- If all rotation-one fixed vertices lie in a finite set of cardinality at
most nineteen, then the rotation-one fixed count is at most nineteen. -/
theorem fixedVertexCount_rotation_one_le_nineteen_of_subset_finset
    (h : D19ActsOnMoore57 V Γ)
    (s : Finset V)
    (hsub : ∀ ⦃v : V⦄, v ∈ fixedVertexSet (h.rotation 1) → v ∈ s)
    (hcard : s.card ≤ 19) :
    fixedVertexCount (h.rotation 1) ≤ 19 :=
  (RotationOneFixedBoundWitness.of_subset_finset
    (h := h) s hsub hcard).fixedVertexCount_rotation_one_le_nineteen

/-- If the rotation-one fixed vertices are equivalent to a finite set of
cardinality at most nineteen, then the rotation-one fixed count is at most
nineteen. -/
theorem fixedVertexCount_rotation_one_le_nineteen_of_equiv_finset
    (h : D19ActsOnMoore57 V Γ)
    (s : Finset V)
    (e : fixedVertexSet (h.rotation 1) ≃ s)
    (hcard : s.card ≤ 19) :
    fixedVertexCount (h.rotation 1) ≤ 19 :=
  (RotationOneFixedBoundWitness.of_equiv_finset
    (h := h) s e hcard).fixedVertexCount_rotation_one_le_nineteen

/-- If all rotation-one fixed vertices lie in a finite set of cardinality at
most nineteen, then build the coarse upper-bound input for all nontrivial
rotations. -/
def RotationFixedUpperBoundInput.of_rotation_one_subset_finset
    (h : D19ActsOnMoore57 V Γ)
    (s : Finset V)
    (hsub : ∀ ⦃v : V⦄, v ∈ fixedVertexSet (h.rotation 1) → v ∈ s)
    (hcard : s.card ≤ 19) :
    RotationFixedUpperBoundInput h :=
  (RotationOneFixedBoundWitness.of_subset_finset
    (h := h) s hsub hcard).toRotationFixedUpperBoundInput

/-- If the rotation-one fixed vertices are equivalent to a finite set of
cardinality at most nineteen, then build the coarse upper-bound input. -/
def RotationFixedUpperBoundInput.of_rotation_one_equiv_finset
    (h : D19ActsOnMoore57 V Γ)
    (s : Finset V)
    (e : fixedVertexSet (h.rotation 1) ≃ s)
    (hcard : s.card ≤ 19) :
    RotationFixedUpperBoundInput h :=
  (RotationOneFixedBoundWitness.of_equiv_finset
    (h := h) s e hcard).toRotationFixedUpperBoundInput

/-- Build the coarse upper-bound input from an explicit finite enumeration
record. -/
def RotationFixedUpperBoundInput.of_rotation_one_enumeration
    {h : D19ActsOnMoore57 V Γ}
    (e : RotationOneFixedEnumeration h) :
    RotationFixedUpperBoundInput h :=
  e.toRotationFixedUpperBoundInput

/-- Build the coarse upper-bound input from an equality identifying the
rotation-one fixed set's `toFinset` with a finite set of size at most nineteen. -/
def RotationFixedUpperBoundInput.of_rotation_one_toFinset_eq
    (h : D19ActsOnMoore57 V Γ)
    (s : Finset V)
    (hs : (fixedVertexSet (h.rotation 1)).toFinset = s)
    (hcard : s.card ≤ 19) :
    RotationFixedUpperBoundInput h :=
  RotationFixedUpperBoundInput.of_rotation_one_subset_finset h s
    (fun {v} hv => by
      rw [← hs]
      simp [hv])
    hcard

/-- A finite set witness can also be supplied as a finite subtype. -/
def RotationFixedUpperBoundInput.of_rotation_one_subset_set
    (h : D19ActsOnMoore57 V Γ)
    (S : Set V) [Fintype S]
    (hsub : fixedVertexSet (h.rotation 1) ⊆ S)
    (hcard : Fintype.card S ≤ 19) :
    RotationFixedUpperBoundInput h :=
  RotationFixedUpperBoundInput.of_rotation_one_le_nineteen (h := h) (by
    rw [fixedVertexCount_eq_card_fixedVertexSet]
    exact (Fintype.card_le_of_injective
      (fun x : fixedVertexSet (h.rotation 1) => (⟨x.1, hsub x.2⟩ : S))
      (by
        intro x y hxy
        ext
        exact congrArg (fun z : S => (z : V)) hxy)).trans hcard)

/-- A list containing every rotation-one fixed vertex and of length at most
nineteen gives the coarse upper-bound input. Duplicates are allowed. -/
def RotationFixedUpperBoundInput.of_rotation_one_subset_list
    (h : D19ActsOnMoore57 V Γ)
    (l : List V)
    (hsub : ∀ ⦃v : V⦄, v ∈ fixedVertexSet (h.rotation 1) → v ∈ l)
    (hlen : l.length ≤ 19) :
    RotationFixedUpperBoundInput h :=
  RotationFixedUpperBoundInput.of_rotation_one_subset_finset h l.toFinset
    (fun {v} hv => by
      simpa using hsub (v := v) hv)
    ((List.toFinset_card_le (l := l)).trans hlen)

/-- A list whose `toFinset` is exactly the rotation-one fixed set gives the
coarse upper-bound input when its length is at most nineteen. -/
def RotationFixedUpperBoundInput.of_rotation_one_list_toFinset_eq
    (h : D19ActsOnMoore57 V Γ)
    (l : List V)
    (hl : l.toFinset = (fixedVertexSet (h.rotation 1)).toFinset)
    (hlen : l.length ≤ 19) :
    RotationFixedUpperBoundInput h :=
  RotationFixedUpperBoundInput.of_rotation_one_subset_list h l
    (fun {v} hv => by
      have hvf : v ∈ (fixedVertexSet (h.rotation 1)).toFinset := by
        simpa using hv
      have hvl : v ∈ l.toFinset := by
        simpa [hl] using hvf
      simpa using hvl)
    hlen

end D19ActsOnMoore57

end Moore57
