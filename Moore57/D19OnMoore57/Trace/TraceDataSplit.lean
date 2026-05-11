import Moore57.D19Contradiction

/-!
# Split trace data assumptions

This file separates the fixed-point input for nontrivial rotations from the
representation-theoretic trace data used to build `TraceRepresentationData`.
-/

namespace Moore57

/-- Fixed-point data for nontrivial rotations. -/
structure RotationFixedData
    {V : Type*} [Fintype V] [DecidableEq V]
    (rotation : ZMod 19 → Equiv.Perm V) where
  /-- Every nontrivial rotation has exactly one fixed vertex. -/
  rotation_fixed :
    ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (rotation d) = 1

/-- The representation-theoretic multiplicities and their arithmetic constraints. -/
structure TraceMultiplicityData where
  /-- Multiplicity of the trivial rational representation. -/
  alpha : ℕ
  /-- Multiplicity of the sign representation. -/
  beta : ℕ
  /-- Multiplicity of the 18-dimensional rational irreducible representation. -/
  gamma : ℕ
  /-- Reflection character value: `alpha - beta = 33`. -/
  reflection : (alpha : ℤ) - (beta : ℤ) = 33
  /-- Dimension of the 7-eigenspace representation. -/
  dimension : alpha + beta + 18 * gamma = 1729
  /-- Nonnegativity of the trivial multiplicity contribution in the `-8`-eigenspace. -/
  minus8_trivial_nonneg : alpha ≤ 113
  /-- Nonnegativity of the sign multiplicity contribution in the `-8`-eigenspace. -/
  minus8_sign_nonneg : beta ≤ 58

/-- Character data without the fixed-point assumption for rotations. -/
structure TraceCharacterCoreData
    {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (rotation : ZMod 19 → Equiv.Perm V)
    (a1 : ZMod 19 → ℕ) extends TraceMultiplicityData where
  /-- `a1 d` is the adjacent-moved vertex count for `rotation d`. -/
  rotation_a1 :
    ∀ d : ZMod 19, d ≠ 0 → adjacentMovedCount Γ (rotation d) = a1 d
  /-- The representation-theoretic character value for nontrivial rotations. -/
  rotation_character :
    ∀ d : ZMod 19, d ≠ 0 →
      Matrix.trace (E7Matrix Γ * permMatrix (rotation d)) =
        (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)

namespace TraceCharacterCoreData

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    {rotation : ZMod 19 → Equiv.Perm V}
    {a1 : ZMod 19 → ℕ}

/-- Combine core character data with the separated fixed-point data to obtain
the arithmetic trace representation data. -/
def toTraceRepresentationData
    (h : TraceCharacterCoreData Γ rotation a1)
    (hfixed : RotationFixedData rotation)
    (hΓ : IsMoore57 Γ) :
    TraceRepresentationData a1 where
  alpha := h.alpha
  beta := h.beta
  gamma := h.gamma
  reflection := h.reflection
  dimension := h.dimension
  minus8_trivial_nonneg := h.minus8_trivial_nonneg
  minus8_sign_nonneg := h.minus8_sign_nonneg
  rotation_trace := by
    intro d hd
    exact rotation_trace_eq_of_higman_character hΓ (rotation d)
      (hfixed.rotation_fixed d hd) (h.rotation_a1 d hd) (h.rotation_character d hd)

end TraceCharacterCoreData

namespace TraceCharacterData

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    {rotation : ZMod 19 → Equiv.Perm V}
    {a1 : ZMod 19 → ℕ}

/-- Extract the fixed-point part of the bundled trace character data. -/
def toRotationFixedData (h : TraceCharacterData Γ rotation a1) :
    RotationFixedData rotation where
  rotation_fixed := h.rotation_fixed

/-- Extract the multiplicity arithmetic part of the bundled trace character data. -/
def toTraceMultiplicityData (h : TraceCharacterData Γ rotation a1) :
    TraceMultiplicityData where
  alpha := h.alpha
  beta := h.beta
  gamma := h.gamma
  reflection := h.reflection
  dimension := h.dimension
  minus8_trivial_nonneg := h.minus8_trivial_nonneg
  minus8_sign_nonneg := h.minus8_sign_nonneg

/-- Drop the fixed-point field from the bundled trace character data. -/
def toTraceCharacterCoreData (h : TraceCharacterData Γ rotation a1) :
    TraceCharacterCoreData Γ rotation a1 where
  toTraceMultiplicityData := h.toTraceMultiplicityData
  rotation_a1 := h.rotation_a1
  rotation_character := h.rotation_character

/-- The existing bundled trace character data factors through the split records. -/
def toTraceRepresentationData_split
    (h : TraceCharacterData Γ rotation a1) (hΓ : IsMoore57 Γ) :
    TraceRepresentationData a1 :=
  h.toTraceCharacterCoreData.toTraceRepresentationData h.toRotationFixedData hΓ

end TraceCharacterData

end Moore57
