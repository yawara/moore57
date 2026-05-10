import Moore57.D19RepresentationCharacterBoundary
import Moore57.TraceCoreRepresentationBoundary

/-!
# Boundary bridges for D19 representation-character data

This file isolates the remaining representation-theoretic boundary once a
`D19ActsOnMoore57` witness has supplied the concrete rotation action and the
`a1` compatibility.  The remaining data is exactly multiplicity arithmetic
plus the nontrivial-rotation character identity.
-/

namespace Moore57

namespace TraceMultiplicityData

/-- Build multiplicity data from its visible arithmetic components. -/
def ofComponents
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    TraceMultiplicityData where
  alpha := alpha
  beta := beta
  gamma := gamma
  reflection := reflection
  dimension := dimension
  minus8_trivial_nonneg := minus8_trivial_nonneg
  minus8_sign_nonneg := minus8_sign_nonneg

@[simp] theorem ofComponents_alpha
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    (ofComponents alpha beta gamma reflection dimension
      minus8_trivial_nonneg minus8_sign_nonneg).alpha = alpha :=
  rfl

@[simp] theorem ofComponents_beta
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    (ofComponents alpha beta gamma reflection dimension
      minus8_trivial_nonneg minus8_sign_nonneg).beta = beta :=
  rfl

@[simp] theorem ofComponents_gamma
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    (ofComponents alpha beta gamma reflection dimension
      minus8_trivial_nonneg minus8_sign_nonneg).gamma = gamma :=
  rfl

@[simp] theorem ofComponents_to_components (multiplicity : TraceMultiplicityData) :
    ofComponents multiplicity.alpha multiplicity.beta multiplicity.gamma
        multiplicity.reflection multiplicity.dimension
        multiplicity.minus8_trivial_nonneg
        multiplicity.minus8_sign_nonneg =
      multiplicity := by
  cases multiplicity
  rfl

/-- The multiplicity boundary with every field exposed. -/
def ComponentsBoundary : Prop :=
  ∃ alpha beta gamma : ℕ,
    ((alpha : ℤ) - (beta : ℤ) = 33) ∧
      (alpha + beta + 18 * gamma = 1729) ∧
        alpha ≤ 113 ∧ beta ≤ 58

/-- A `TraceMultiplicityData` record exists exactly when its exposed arithmetic
components exist. -/
theorem nonempty_iff_componentsBoundary :
    Nonempty TraceMultiplicityData ↔ ComponentsBoundary := by
  constructor
  · rintro ⟨multiplicity⟩
    exact
      ⟨multiplicity.alpha, multiplicity.beta, multiplicity.gamma,
        multiplicity.reflection, multiplicity.dimension,
        multiplicity.minus8_trivial_nonneg,
        multiplicity.minus8_sign_nonneg⟩
  · rintro ⟨alpha, beta, gamma, reflection, dimension,
        minus8_trivial_nonneg, minus8_sign_nonneg⟩
    exact
      ⟨ofComponents alpha beta gamma reflection dimension
        minus8_trivial_nonneg minus8_sign_nonneg⟩

end TraceMultiplicityData

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The remaining representation-character boundary after the action supplies
`rotation` and `a1`: multiplicity arithmetic plus the character value on every
nontrivial rotation. -/
def RepresentationCharacterComponentsBoundary
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  ∃ alpha beta gamma : ℕ,
    ((alpha : ℤ) - (beta : ℤ) = 33) ∧
      (alpha + beta + 18 * gamma = 1729) ∧
        alpha ≤ 113 ∧ beta ≤ 58 ∧
          ∀ d : ZMod 19, d ≠ 0 →
            Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
              (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)

/-- The action and Moore57 hypothesis determine the Higman trace expression in
terms of the fixed count and the action-defined `a1`.  What is not supplied by
`h` alone is the representation-character rewrite to `alpha + beta - gamma`. -/
theorem rotation_trace_eq_fixed_a1
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) :
    Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
      (8 * (fixedVertexCount (h.rotation d) : ℚ) + (h.a1 d : ℚ) - 65) / 15 := by
  rw [h.isMoore.higman_trace_formula (h.rotation d), h.rotation_a1_def d]

/-- The component boundary is the same as multiplicity data plus the
nontrivial-rotation character identity. -/
theorem representationCharacterComponentsBoundary_iff_exists_traceMultiplicityData
    (h : D19ActsOnMoore57 V Γ) :
    RepresentationCharacterComponentsBoundary h ↔
      ∃ multiplicity : TraceMultiplicityData,
        ∀ d : ZMod 19, d ≠ 0 →
          Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
            (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) -
              (multiplicity.gamma : ℚ) := by
  constructor
  · rintro ⟨alpha, beta, gamma, reflection, dimension,
        minus8_trivial_nonneg, minus8_sign_nonneg, rotation_character⟩
    refine
      ⟨TraceMultiplicityData.ofComponents alpha beta gamma reflection dimension
        minus8_trivial_nonneg minus8_sign_nonneg, ?_⟩
    intro d hd
    simpa [TraceMultiplicityData.ofComponents] using
      rotation_character d hd
  · rintro ⟨multiplicity, rotation_character⟩
    exact
      ⟨multiplicity.alpha, multiplicity.beta, multiplicity.gamma,
        multiplicity.reflection, multiplicity.dimension,
        multiplicity.minus8_trivial_nonneg,
        multiplicity.minus8_sign_nonneg, rotation_character⟩

namespace D19RepresentationCharacterInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Build the representation-character input directly from exposed
multiplicity components and the nontrivial-rotation character identity. -/
def ofComponents
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (rotation_character :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)) :
    D19RepresentationCharacterInput h where
  multiplicity :=
    TraceMultiplicityData.ofComponents alpha beta gamma reflection dimension
      minus8_trivial_nonneg minus8_sign_nonneg
  rotation_character := by
    intro d hd
    simpa [TraceMultiplicityData.ofComponents] using rotation_character d hd

@[simp] theorem ofComponents_multiplicity
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (rotation_character :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)) :
    (ofComponents (h := h) alpha beta gamma reflection dimension
        minus8_trivial_nonneg minus8_sign_nonneg
        rotation_character).multiplicity =
      TraceMultiplicityData.ofComponents alpha beta gamma reflection dimension
        minus8_trivial_nonneg minus8_sign_nonneg :=
  rfl

/-- A representation-character input exists exactly when the exposed component
boundary exists. -/
theorem nonempty_iff_componentsBoundary
    (h : D19ActsOnMoore57 V Γ) :
    Nonempty (D19RepresentationCharacterInput h) ↔
      RepresentationCharacterComponentsBoundary h :=
  (nonempty_iff_exists_traceMultiplicityData h).trans
    (representationCharacterComponentsBoundary_iff_exists_traceMultiplicityData h).symm

/-- Repackage a representation-character input as the component boundary
consumed by the branch-orbit no-go frontiers. -/
theorem representationCharacterComponentsBoundary
    (input : D19RepresentationCharacterInput h) :
    RepresentationCharacterComponentsBoundary h :=
  (nonempty_iff_componentsBoundary _).mp ⟨input⟩

/-- Repackage a representation-character input as the final trace-core
boundary.  The `rotation_a1` field is supplied by `h` when lowering further to
`TraceCharacterCoreData`. -/
def toTraceCoreCharacterBoundary
    (input : D19RepresentationCharacterInput h) :
    TraceCoreCharacterBoundary h :=
  TraceCoreCharacterBoundary.ofD19RepresentationCharacterInput input

/-- Forget the final trace-core boundary back to representation-character
input. -/
def ofTraceCoreCharacterBoundary
    (data : TraceCoreCharacterBoundary h) :
    D19RepresentationCharacterInput h :=
  data.toD19RepresentationCharacterInput

@[simp] theorem toTraceCoreCharacterBoundary_multiplicity
    (input : D19RepresentationCharacterInput h) :
    input.toTraceCoreCharacterBoundary.multiplicity = input.multiplicity :=
  rfl

@[simp] theorem ofTraceCoreCharacterBoundary_multiplicity
    (data : TraceCoreCharacterBoundary h) :
    (ofTraceCoreCharacterBoundary data).multiplicity = data.multiplicity :=
  rfl

@[simp] theorem ofTraceCoreCharacterBoundary_toTraceCoreCharacterBoundary
    (input : D19RepresentationCharacterInput h) :
    ofTraceCoreCharacterBoundary input.toTraceCoreCharacterBoundary = input :=
  TraceCoreCharacterBoundary.toD19RepresentationCharacterInput_ofD19RepresentationCharacterInput
    input

@[simp] theorem toTraceCoreCharacterBoundary_ofTraceCoreCharacterBoundary
    (data : TraceCoreCharacterBoundary h) :
    (ofTraceCoreCharacterBoundary data).toTraceCoreCharacterBoundary = data :=
  TraceCoreCharacterBoundary.ofD19RepresentationCharacterInput_toD19RepresentationCharacterInput
    data

/-- The final trace-core boundary and representation-character input are
equivalent once `h` supplies `rotation_a1`. -/
def traceCoreCharacterBoundaryEquiv
    (h : D19ActsOnMoore57 V Γ) :
    D19RepresentationCharacterInput h ≃ TraceCoreCharacterBoundary h where
  toFun := toTraceCoreCharacterBoundary
  invFun := ofTraceCoreCharacterBoundary
  left_inv := by
    intro input
    exact ofTraceCoreCharacterBoundary_toTraceCoreCharacterBoundary input
  right_inv := by
    intro data
    exact toTraceCoreCharacterBoundary_ofTraceCoreCharacterBoundary data

/-- Nonemptiness form of `traceCoreCharacterBoundaryEquiv`. -/
theorem nonempty_iff_traceCoreCharacterBoundary
    (h : D19ActsOnMoore57 V Γ) :
    Nonempty (D19RepresentationCharacterInput h) ↔
      Nonempty (TraceCoreCharacterBoundary h) :=
  (TraceCoreCharacterBoundary.nonempty_iff_d19RepresentationCharacterInput h).symm

end D19RepresentationCharacterInput

namespace TraceCoreCharacterBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Build the final trace-core boundary directly from the exposed
representation-character components. -/
def ofComponents
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (rotation_character :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)) :
    TraceCoreCharacterBoundary h where
  multiplicity :=
    TraceMultiplicityData.ofComponents alpha beta gamma reflection dimension
      minus8_trivial_nonneg minus8_sign_nonneg
  rotation_character := by
    intro d hd
    simpa [TraceMultiplicityData.ofComponents] using rotation_character d hd

@[simp] theorem ofComponents_multiplicity
    (alpha beta gamma : ℕ)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58)
    (rotation_character :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)) :
    (ofComponents (h := h) alpha beta gamma reflection dimension
        minus8_trivial_nonneg minus8_sign_nonneg
        rotation_character).multiplicity =
      TraceMultiplicityData.ofComponents alpha beta gamma reflection dimension
        minus8_trivial_nonneg minus8_sign_nonneg :=
  rfl

/-- The final trace-core boundary exists exactly when the exposed component
boundary exists. -/
theorem nonempty_iff_componentsBoundary
    (h : D19ActsOnMoore57 V Γ) :
    Nonempty (TraceCoreCharacterBoundary h) ↔
      RepresentationCharacterComponentsBoundary h :=
  (nonempty_iff_d19RepresentationCharacterInput h).trans
    (D19RepresentationCharacterInput.nonempty_iff_componentsBoundary h)

/-- Repackage a trace-core character boundary as the component boundary
consumed by the branch-orbit no-go frontiers. -/
theorem representationCharacterComponentsBoundary
    (data : TraceCoreCharacterBoundary h) :
    RepresentationCharacterComponentsBoundary h :=
  (nonempty_iff_componentsBoundary _).mp ⟨data⟩

end TraceCoreCharacterBoundary

namespace RepresentationCharacterComponentsBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Reify the exposed component boundary as the final trace-core boundary.

This is noncomputable only because the component boundary is Prop-valued and
there may be many equivalent multiplicity witnesses. -/
noncomputable def toTraceCoreCharacterBoundary
    (hcomp : RepresentationCharacterComponentsBoundary h) :
    TraceCoreCharacterBoundary h :=
  Classical.choice
    ((TraceCoreCharacterBoundary.nonempty_iff_componentsBoundary h).mpr hcomp)

/-- Lower the exposed component boundary to the arithmetic trace representation
data used by the older trace consumers.  The raw action supplies the separated
rotation fixed-count field. -/
noncomputable def toTraceRepresentationData
    (hcomp : RepresentationCharacterComponentsBoundary h) :
    TraceRepresentationData h.a1 :=
  hcomp.toTraceCoreCharacterBoundary.toTraceRepresentationData

/-- Nonemptiness wrapper for the component-boundary-to-trace-data bridge. -/
theorem nonempty_traceRepresentationData
    (hcomp : RepresentationCharacterComponentsBoundary h) :
    Nonempty (TraceRepresentationData h.a1) :=
  ⟨hcomp.toTraceRepresentationData⟩

end RepresentationCharacterComponentsBoundary

end D19ActsOnMoore57

end Moore57
