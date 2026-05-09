import Moore57.TraceCoreBridge

/-!
# Packaging helpers for D19 trace multiplicity data

This file keeps small representation-theory input records separate from the
larger `TraceCharacterData` bundle, specialized to the rotation action coming
from `D19ActsOnMoore57`.
-/

namespace Moore57

namespace TraceMultiplicityData

/-- The reflection-character constraint as a named projection theorem. -/
theorem reflection_eq (h : TraceMultiplicityData) :
    (h.alpha : ℤ) - (h.beta : ℤ) = 33 :=
  h.reflection

/-- The dimension constraint as a named projection theorem. -/
theorem dimension_eq (h : TraceMultiplicityData) :
    h.alpha + h.beta + 18 * h.gamma = 1729 :=
  h.dimension

/-- The `-8` trivial-isotypic nonnegativity constraint as a named projection theorem. -/
theorem minus8_trivial_bound (h : TraceMultiplicityData) :
    h.alpha ≤ 113 :=
  h.minus8_trivial_nonneg

/-- The `-8` sign-isotypic nonnegativity constraint as a named projection theorem. -/
theorem minus8_sign_bound (h : TraceMultiplicityData) :
    h.beta ≤ 58 :=
  h.minus8_sign_nonneg

end TraceMultiplicityData

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The reduced trace input for the rotation action attached to a
`D19ActsOnMoore57` witness.

It separates multiplicity arithmetic, nontrivial-rotation character values, and
fixed-point data while staying specialized to `h.rotation` and `h.a1`. -/
structure D19TraceInput (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and their arithmetic constraints. -/
  multiplicity : TraceMultiplicityData
  /-- The character value for every nontrivial rotation. -/
  rotation_character :
    ∀ d : ZMod 19, d ≠ 0 →
      Matrix.trace (E7Matrix Γ * permMatrix (h.rotation d)) =
        (multiplicity.alpha : ℚ) + (multiplicity.beta : ℚ) - (multiplicity.gamma : ℚ)
  /-- Fixed-point data for every nontrivial rotation. -/
  fixed : RotationFixedData h.rotation

namespace D19TraceInput

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the reduced D19 trace input into the arithmetic trace data currently
used by the contradiction argument. -/
noncomputable def toTraceRepresentationData (hin : D19TraceInput h) :
    TraceRepresentationData h.a1 :=
  h.toTraceRepresentationData hin.multiplicity hin.rotation_character hin.fixed

/-- The converted trace representation keeps the packaged `alpha`. -/
@[simp] theorem toTraceRepresentationData_alpha (hin : D19TraceInput h) :
    hin.toTraceRepresentationData.alpha = hin.multiplicity.alpha :=
  rfl

/-- The converted trace representation keeps the packaged `beta`. -/
@[simp] theorem toTraceRepresentationData_beta (hin : D19TraceInput h) :
    hin.toTraceRepresentationData.beta = hin.multiplicity.beta :=
  rfl

/-- The converted trace representation keeps the packaged `gamma`. -/
@[simp] theorem toTraceRepresentationData_gamma (hin : D19TraceInput h) :
    hin.toTraceRepresentationData.gamma = hin.multiplicity.gamma :=
  rfl

/-- The converted trace representation keeps the packaged reflection constraint. -/
@[simp] theorem toTraceRepresentationData_reflection (hin : D19TraceInput h) :
    hin.toTraceRepresentationData.reflection = hin.multiplicity.reflection :=
  rfl

/-- The converted trace representation keeps the packaged dimension constraint. -/
@[simp] theorem toTraceRepresentationData_dimension (hin : D19TraceInput h) :
    hin.toTraceRepresentationData.dimension = hin.multiplicity.dimension :=
  rfl

/-- The converted trace representation keeps the packaged trivial bound. -/
@[simp] theorem toTraceRepresentationData_minus8_trivial_nonneg (hin : D19TraceInput h) :
    hin.toTraceRepresentationData.minus8_trivial_nonneg = hin.multiplicity.minus8_trivial_nonneg :=
  rfl

/-- The converted trace representation keeps the packaged sign bound. -/
@[simp] theorem toTraceRepresentationData_minus8_sign_nonneg (hin : D19TraceInput h) :
    hin.toTraceRepresentationData.minus8_sign_nonneg = hin.multiplicity.minus8_sign_nonneg :=
  rfl

end D19TraceInput

end Moore57
