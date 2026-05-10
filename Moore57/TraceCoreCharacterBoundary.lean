import Moore57.D19RepresentationCharacterFromData
import Moore57.TraceDataSplit
import Moore57.RotationFixedRegularity

/-!
# Boundary helpers for trace-core character data

This file makes the assumptions hidden in a
`traceCore : TraceCharacterCoreData Γ h.rotation h.a1` easy to expose at final
boundaries.  The API is intentionally thin: it gives named projections,
component constructors, and nonemptiness equivalences without changing the
underlying data.
-/

namespace Moore57

namespace TraceCharacterCoreData

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {rotation : ZMod 19 → Equiv.Perm V}
variable {a1 : ZMod 19 → ℕ}

/-- The explicit component package equivalent to `TraceCharacterCoreData`.

This is useful at final boundaries because it displays exactly what a
`traceCore` hypothesis contains: multiplicity arithmetic, `a1` compatibility,
and the nontrivial-rotation character identity. -/
structure Components
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (rotation : ZMod 19 → Equiv.Perm V)
    (a1 : ZMod 19 → ℕ) where
  /-- Representation-theoretic multiplicities and their arithmetic constraints. -/
  multiplicity : TraceMultiplicityData
  /-- `a1` compatibility for every nontrivial rotation. -/
  rotation_a1 :
    ∀ d : ZMod 19, d ≠ 0 → adjacentMovedCount Γ (rotation d) = a1 d
  /-- Character value for every nontrivial rotation. -/
  rotation_character :
    ∀ d : ZMod 19, d ≠ 0 →
      Matrix.trace (E7Matrix Γ * permMatrix (rotation d)) =
        (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
          (multiplicity.gamma : ℚ)

/-- Constructor wrapper from the visible components of trace-core character
data. -/
def ofComponents
    (multiplicity : TraceMultiplicityData)
    (rotation_a1 :
      ∀ d : ZMod 19, d ≠ 0 → adjacentMovedCount Γ (rotation d) = a1 d)
    (rotation_character :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (rotation d)) =
          (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
            (multiplicity.gamma : ℚ)) :
    TraceCharacterCoreData Γ rotation a1 where
  toTraceMultiplicityData := multiplicity
  rotation_a1 := rotation_a1
  rotation_character := rotation_character

/-- Extract the visible component package from trace-core character data. -/
def toComponents
    (core : TraceCharacterCoreData Γ rotation a1) :
    Components Γ rotation a1 :=
  { multiplicity := core.toTraceMultiplicityData
    rotation_a1 := core.rotation_a1
    rotation_character := core.rotation_character }

@[simp] theorem ofComponents_toTraceMultiplicityData
    (multiplicity : TraceMultiplicityData)
    (rotation_a1 :
      ∀ d : ZMod 19, d ≠ 0 → adjacentMovedCount Γ (rotation d) = a1 d)
    (rotation_character :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (rotation d)) =
          (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
            (multiplicity.gamma : ℚ)) :
    (ofComponents (Γ := Γ) (rotation := rotation) (a1 := a1)
        multiplicity rotation_a1 rotation_character).toTraceMultiplicityData =
      multiplicity :=
  rfl

@[simp] theorem ofComponents_rotation_a1
    (multiplicity : TraceMultiplicityData)
    (rotation_a1 :
      ∀ d : ZMod 19, d ≠ 0 → adjacentMovedCount Γ (rotation d) = a1 d)
    (rotation_character :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (rotation d)) =
          (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
            (multiplicity.gamma : ℚ)) :
    (ofComponents (Γ := Γ) (rotation := rotation) (a1 := a1)
        multiplicity rotation_a1 rotation_character).rotation_a1 =
      rotation_a1 :=
  rfl

@[simp] theorem ofComponents_rotation_character
    (multiplicity : TraceMultiplicityData)
    (rotation_a1 :
      ∀ d : ZMod 19, d ≠ 0 → adjacentMovedCount Γ (rotation d) = a1 d)
    (rotation_character :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (rotation d)) =
          (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
            (multiplicity.gamma : ℚ)) :
    (ofComponents (Γ := Γ) (rotation := rotation) (a1 := a1)
        multiplicity rotation_a1 rotation_character).rotation_character =
      rotation_character :=
  rfl

@[simp] theorem toComponents_ofComponents
    (multiplicity : TraceMultiplicityData)
    (rotation_a1 :
      ∀ d : ZMod 19, d ≠ 0 → adjacentMovedCount Γ (rotation d) = a1 d)
    (rotation_character :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (rotation d)) =
          (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
            (multiplicity.gamma : ℚ)) :
    (ofComponents (Γ := Γ) (rotation := rotation) (a1 := a1)
        multiplicity rotation_a1 rotation_character).toComponents =
      { multiplicity := multiplicity
        rotation_a1 := rotation_a1
        rotation_character := rotation_character } :=
  rfl

@[simp] theorem ofComponents_toComponents
    (core : TraceCharacterCoreData Γ rotation a1) :
    ofComponents (Γ := Γ) (rotation := rotation) (a1 := a1)
        core.toComponents.multiplicity core.toComponents.rotation_a1
        core.toComponents.rotation_character =
      core := by
  cases core
  rfl

/-- `TraceCharacterCoreData` is equivalent to its explicit component package. -/
def componentsEquiv :
    TraceCharacterCoreData Γ rotation a1 ≃ Components Γ rotation a1 where
  toFun := toComponents
  invFun := fun data =>
    ofComponents data.multiplicity data.rotation_a1 data.rotation_character
  left_inv := by
    intro core
    exact ofComponents_toComponents core
  right_inv := by
    rintro ⟨multiplicity, rotation_a1, rotation_character⟩
    rfl

/-- Nonemptiness of trace-core data is nonemptiness of the explicit component
package. -/
theorem nonempty_iff_components :
    Nonempty (TraceCharacterCoreData Γ rotation a1) ↔
      Nonempty (Components Γ rotation a1) := by
  constructor
  · rintro ⟨core⟩
    exact ⟨core.toComponents⟩
  · rintro ⟨data⟩
    exact ⟨ofComponents data.multiplicity data.rotation_a1 data.rotation_character⟩

/-- Existence form of `nonempty_iff_components`, spelling out all remaining
fields in a `traceCore` hypothesis. -/
theorem nonempty_iff_exists_components :
    Nonempty (TraceCharacterCoreData Γ rotation a1) ↔
      ∃ multiplicity : TraceMultiplicityData,
        (∀ d : ZMod 19, d ≠ 0 → adjacentMovedCount Γ (rotation d) = a1 d) ∧
          (∀ d : ZMod 19, d ≠ 0 →
            Matrix.trace (E7Matrix Γ * permMatrix (rotation d)) =
              (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
                (multiplicity.gamma : ℚ)) := by
  constructor
  · rintro ⟨core⟩
    exact ⟨core.toTraceMultiplicityData, core.rotation_a1, core.rotation_character⟩
  · rintro ⟨multiplicity, rotation_a1, rotation_character⟩
    exact ⟨ofComponents multiplicity rotation_a1 rotation_character⟩

/-- Named projection for the adjacent-moved compatibility field. -/
theorem rotation_a1_eq
    (core : TraceCharacterCoreData Γ rotation a1)
    (d : ZMod 19) (hd : d ≠ 0) :
    adjacentMovedCount Γ (rotation d) = a1 d :=
  core.rotation_a1 d hd

/-- Named projection for the nontrivial-rotation character identity. -/
theorem rotation_character_eq
    (core : TraceCharacterCoreData Γ rotation a1)
    (d : ZMod 19) (hd : d ≠ 0) :
    Matrix.trace (E7Matrix Γ * permMatrix (rotation d)) =
      (core.alpha : ℚ) + (core.beta : ℚ) - (core.gamma : ℚ) :=
  core.rotation_character d hd

/-- Named projection for the reflection-character arithmetic constraint. -/
theorem reflection_eq (core : TraceCharacterCoreData Γ rotation a1) :
    (core.alpha : ℤ) - (core.beta : ℤ) = 33 :=
  core.reflection

/-- Named projection for the total dimension arithmetic constraint. -/
theorem dimension_eq (core : TraceCharacterCoreData Γ rotation a1) :
    core.alpha + core.beta + 18 * core.gamma = 1729 :=
  core.dimension

/-- Named projection for the trivial `-8`-eigenspace bound. -/
theorem minus8_trivial_bound (core : TraceCharacterCoreData Γ rotation a1) :
    core.alpha ≤ 113 :=
  core.minus8_trivial_nonneg

/-- Named projection for the sign `-8`-eigenspace bound. -/
theorem minus8_sign_bound (core : TraceCharacterCoreData Γ rotation a1) :
    core.beta ≤ 58 :=
  core.minus8_sign_nonneg

end TraceCharacterCoreData

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The final-boundary component package for
`TraceCharacterCoreData Γ h.rotation h.a1`.

For a `D19ActsOnMoore57` witness, the `a1` compatibility is supplied by `h`,
so the remaining visible assumptions are exactly multiplicity arithmetic and
the nontrivial-rotation character identity. -/
structure TraceCoreCharacterBoundary (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and their arithmetic constraints. -/
  multiplicity : TraceMultiplicityData
  /-- Character value for every nontrivial rotation of the D19 action. -/
  rotation_character :
    ∀ d : ZMod 19, d ≠ 0 →
      Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
        (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
          (multiplicity.gamma : ℚ)

namespace TraceCoreCharacterBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The ambient `D19ActsOnMoore57` witness supplies the split rotation fixed
data needed by `TraceCharacterCoreData.toTraceRepresentationData`. -/
def rotationFixedData (h : D19ActsOnMoore57 V Γ) :
    RotationFixedData h.rotation where
  rotation_fixed := by
    intro d hd
    exact h.rotation_fixed_card_eq_one hd

/-- Build trace-core data from the final-boundary components. -/
noncomputable def toTraceCharacterCoreData
    (data : TraceCoreCharacterBoundary h) :
    TraceCharacterCoreData Γ h.rotation h.a1 :=
  TraceCharacterCoreData.ofComponents data.multiplicity
    h.rotation_a1_def_of_ne_zero data.rotation_character

/-- Extract the final-boundary components from trace-core data. -/
def ofTraceCharacterCoreData
    (core : TraceCharacterCoreData Γ h.rotation h.a1) :
    TraceCoreCharacterBoundary h :=
  { multiplicity := core.toTraceMultiplicityData
    rotation_character := core.rotation_character }

@[simp] theorem toTraceCharacterCoreData_toTraceMultiplicityData
    (data : TraceCoreCharacterBoundary h) :
    data.toTraceCharacterCoreData.toTraceMultiplicityData = data.multiplicity :=
  rfl

@[simp] theorem toTraceCharacterCoreData_rotation_character
    (data : TraceCoreCharacterBoundary h) :
    data.toTraceCharacterCoreData.rotation_character = data.rotation_character :=
  rfl

@[simp] theorem ofTraceCharacterCoreData_toTraceCharacterCoreData
    (data : TraceCoreCharacterBoundary h) :
    ofTraceCharacterCoreData data.toTraceCharacterCoreData = data := by
  cases data
  rfl

@[simp] theorem toTraceCharacterCoreData_ofTraceCharacterCoreData
    (core : TraceCharacterCoreData Γ h.rotation h.a1) :
    toTraceCharacterCoreData (ofTraceCharacterCoreData core) = core := by
  exact
    D19RepresentationCharacterInput.toTraceCharacterCoreData_ofTraceCharacterCoreData
      core

/-- At a `D19ActsOnMoore57` final boundary, trace-core data is equivalent to
multiplicity arithmetic plus the nontrivial-rotation character identity. -/
noncomputable def equivTraceCharacterCoreData
    (h : D19ActsOnMoore57 V Γ) :
    TraceCoreCharacterBoundary h ≃ TraceCharacterCoreData Γ h.rotation h.a1 where
  toFun := toTraceCharacterCoreData
  invFun := ofTraceCharacterCoreData
  left_inv := by
    intro data
    exact ofTraceCharacterCoreData_toTraceCharacterCoreData data
  right_inv := by
    intro core
    exact toTraceCharacterCoreData_ofTraceCharacterCoreData core

/-- Nonemptiness form of `equivTraceCharacterCoreData`. -/
theorem nonempty_iff_traceCharacterCoreData
    (h : D19ActsOnMoore57 V Γ) :
    Nonempty (TraceCoreCharacterBoundary h) ↔
      Nonempty (TraceCharacterCoreData Γ h.rotation h.a1) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toTraceCharacterCoreData⟩
  · rintro ⟨core⟩
    exact ⟨ofTraceCharacterCoreData core⟩

/-- Existence form that makes the final `traceCore` assumption explicit. -/
theorem traceCharacterCoreData_nonempty_iff_exists_boundary
    (h : D19ActsOnMoore57 V Γ) :
    Nonempty (TraceCharacterCoreData Γ h.rotation h.a1) ↔
      ∃ multiplicity : TraceMultiplicityData,
        ∀ d : ZMod 19, d ≠ 0 →
          Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
            (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
              (multiplicity.gamma : ℚ) := by
  constructor
  · rintro ⟨core⟩
    exact ⟨core.toTraceMultiplicityData, core.rotation_character⟩
  · rintro ⟨multiplicity, rotation_character⟩
    exact ⟨toTraceCharacterCoreData
      { multiplicity := multiplicity
        rotation_character := rotation_character }⟩

/-- Combine the final trace-core boundary with the raw action's rotation
fixed-count theorem to obtain the arithmetic trace-representation data. -/
noncomputable def toTraceRepresentationData
    (data : TraceCoreCharacterBoundary h) :
    TraceRepresentationData h.a1 :=
  data.toTraceCharacterCoreData.toTraceRepresentationData
    (rotationFixedData h) h.isMoore

/-- A trace-core boundary exists only if the corresponding trace-representation
data exists; the rotation fixed-count field is supplied by the raw action. -/
theorem nonempty_traceRepresentationData
    (data : TraceCoreCharacterBoundary h) :
    Nonempty (TraceRepresentationData h.a1) :=
  ⟨data.toTraceRepresentationData⟩

end TraceCoreCharacterBoundary

end D19ActsOnMoore57

end Moore57
