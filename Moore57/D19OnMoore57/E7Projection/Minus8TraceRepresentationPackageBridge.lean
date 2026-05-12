import Moore57.D19OnMoore57.E7Projection.ProjectionA1CharacterBoundary
import Moore57.D19OnMoore57.E7Projection.Minus8CharacterBoundaryPackages

/-!
# Package bridge from trace-representation data

This file connects the older `TraceRepresentationData h.a1` arithmetic surface
to the newer Type-valued E7/minus-8 character boundary package.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

namespace E7Minus8CharacterReflectionCountBoundary

variable (h : D19ActsOnMoore57 V Γ)

/-- Build the direct E7/minus-8 character package from the older
`TraceRepresentationData h.a1` arithmetic data, a minus-8 value-boundary, and
the standard count inputs at the reflection representative `sr 0`. -/
def ofTraceRepresentationData
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (reflection_fixed_count :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr 0)) = 56)
    (reflection_adjacent_moved :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr 0)) = 112) :
    E7Minus8CharacterReflectionCountBoundary h where
  alpha := data.alpha
  beta := data.beta
  gamma := data.gamma
  A := A
  B := B
  C := C
  e7Class :=
    E7ProjectionCharacterClassBoundary.ofTraceRepresentationDataAndReflectionCounts
      h data rotation_fixed reflection_fixed_count reflection_adjacent_moved
  minus8Values := minus8Values
  dt := 0
  reflection_fixed_count := reflection_fixed_count
  reflection_adjacent_moved := reflection_adjacent_moved
  rotation_fixed_count := rotation_fixed

/-- Fixed-star form of `ofTraceRepresentationData`: the `sr 0` fixed-star
boundary supplies both standard reflection count inputs. -/
def ofTraceRepresentationDataAndReflectionStar
    (data : TraceRepresentationData h.a1)
    (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    (rotation_fixed :
      ∀ d : ZMod 19, d ≠ 0 → fixedVertexCount (h.rotation d) = 1)
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr 0))) :
    E7Minus8CharacterReflectionCountBoundary h :=
  ofTraceRepresentationData h data A B C minus8Values rotation_fixed
    hStar.fixedVertexCount_eq_56
    (hStar.adjacentMovedCount_eq_112 h.isMoore)

end E7Minus8CharacterReflectionCountBoundary

end D19ActsOnMoore57

end

end Moore57
