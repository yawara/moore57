import Moore57.D19OnMoore57.E7Projection.Minus8K155NoGoConnectors
import Moore57.D19OnMoore57.E7Projection.Minus8PaperFixedStarNoGoConnectors
import Moore57.D19OnMoore57.E7Projection.Minus8RawReflectionStarConnectors
import Moore57.D19OnMoore57.E7Projection.Minus8TraceBoundaryBridge
import Moore57.D19OnMoore57.E7Projection.ProjectionLinearCharacterConsequences
import Moore57.D19OnMoore57.LinearCharacter.Nonempty
import Moore57.D19OnMoore57.Reflection.LinearCharacterNonemptyBridge
import Moore57.D19OnMoore57.Reflection.LinearRawReflectionK155Bridge
import Moore57.D19OnMoore57.D19Core.Dihedral19CharacterValueReduction

/-!
# Inverse-pair trace boundary bridge for E7 and minus-8

This file packages concrete projection trace data where nontrivial rotation
obligations have been reduced to one representative from each inverse pair.
The trace data is first converted to mathlib character data for the concrete
projection representations, then expanded by D19 character conjugacy.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Trace-level E7 boundary data with rotations reduced to inverse pairs. -/
structure E7ProjectionInversePairTraceBoundary
    (h : D19ActsOnMoore57 V Γ) (alpha beta gamma : ℕ) where
  dimension : alpha + beta + 18 * gamma = 1729
  rotation_pair_trace :
    ∀ d : ZMod 19, d ≠ 0 →
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ) ∨
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r (-d)))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)
  reflection_zero_trace :
    Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
      (alpha : ℚ) - (beta : ℚ)

/-- Trace-level minus-8 boundary data with rotations reduced to inverse pairs. -/
structure Minus8ProjectionInversePairTraceBoundary
    (h : D19ActsOnMoore57 V Γ) (A B C : ℕ) where
  one_trace :
    Matrix.trace (permMatrix (h.smulEquiv (1 : DihedralGroup 19))) - 1 -
        Matrix.trace (E7Matrix Γ *
          permMatrix (h.smulEquiv (1 : DihedralGroup 19))) =
      (A : ℚ) + (B : ℚ) + 18 * (C : ℚ)
  rotation_pair_trace :
    ∀ d : ZMod 19, d ≠ 0 →
      Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.r d))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (A : ℚ) + (B : ℚ) - (C : ℚ) ∨
        Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.r (-d)))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (DihedralGroup.r (-d)))) =
          (A : ℚ) + (B : ℚ) - (C : ℚ)
  reflection_zero_trace :
    Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.sr 0))) - 1 -
        Matrix.trace (E7Matrix Γ *
          permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
      (A : ℚ) - (B : ℚ)

namespace E7ProjectionInversePairTraceBoundary

/-- Convert inverse-pair E7 trace data to inverse-pair character data. -/
def toCharacterClassInversePairBoundary
    {h : D19ActsOnMoore57 V Γ} {alpha beta gamma : ℕ}
    (boundary : E7ProjectionInversePairTraceBoundary h alpha beta gamma) :
    D19CharacterClassInversePairBoundary
      h.e7ProjectionRepresentation alpha beta gamma where
  dimension := boundary.dimension
  rotation_pair := {
    pair_value := by
      intro d hd
      rcases boundary.rotation_pair_trace d hd with htrace | htrace
      · left
        rw [h.e7ProjectionRepresentation_character_eq_matrix_trace]
        exact htrace
      · right
        rw [h.e7ProjectionRepresentation_character_eq_matrix_trace]
        exact htrace
  }
  reflection_zero := by
    rw [h.e7ProjectionRepresentation_character_eq_matrix_trace]
    exact boundary.reflection_zero_trace

/-- Expand inverse-pair E7 trace data to the existing class-boundary API. -/
def toCharacterClassBoundary
    {h : D19ActsOnMoore57 V Γ} {alpha beta gamma : ℕ}
    (boundary : E7ProjectionInversePairTraceBoundary h alpha beta gamma) :
    D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma :=
  boundary.toCharacterClassInversePairBoundary.toClassBoundary

end E7ProjectionInversePairTraceBoundary

namespace Minus8ProjectionInversePairTraceBoundary

/-- Convert inverse-pair minus-8 trace data to inverse-pair character data. -/
def toCharacterValueInversePairBoundary
    {h : D19ActsOnMoore57 V Γ} {A B C : ℕ}
    (boundary : Minus8ProjectionInversePairTraceBoundary h A B C) :
    D19CharacterValueInversePairBoundary
      h.minus8ProjectionRepresentation A B C where
  one_value := by
    rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
    exact boundary.one_trace
  rotation_pair := {
    pair_value := by
      intro d hd
      rcases boundary.rotation_pair_trace d hd with htrace | htrace
      · left
        rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
        exact htrace
      · right
        rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
        exact htrace
  }
  reflection_zero := by
    rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
    exact boundary.reflection_zero_trace

/-- Expand inverse-pair minus-8 trace data to the existing value-boundary API. -/
def toCharacterValueBoundary
    {h : D19ActsOnMoore57 V Γ} {A B C : ℕ}
    (boundary : Minus8ProjectionInversePairTraceBoundary h A B C) :
    D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C :=
  boundary.toCharacterValueInversePairBoundary.toValueBoundary

end Minus8ProjectionInversePairTraceBoundary

namespace D19CharacterClassBoundary

/-- Build the E7 class boundary from explicit inverse-pair projection traces. -/
def ofE7ProjectionInversePairTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (rotation_pair_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
            (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ) ∨
          Matrix.trace (E7Matrix Γ *
              permMatrix (h.smulEquiv (DihedralGroup.r (-d)))) =
            (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (reflection_zero_trace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (alpha : ℚ) - (beta : ℚ)) :
    D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma :=
  (E7ProjectionInversePairTraceBoundary.toCharacterClassBoundary
    ({ dimension := dimension
       rotation_pair_trace := rotation_pair_trace
       reflection_zero_trace := reflection_zero_trace } :
      E7ProjectionInversePairTraceBoundary h alpha beta gamma))

end D19CharacterClassBoundary

namespace D19CharacterValueBoundary

/-- Build the minus-8 value boundary from explicit inverse-pair projection traces. -/
def ofMinus8ProjectionInversePairTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (A B C : ℕ)
    (one_trace :
      Matrix.trace (permMatrix (h.smulEquiv (1 : DihedralGroup 19))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (1 : DihedralGroup 19))) =
        (A : ℚ) + (B : ℚ) + 18 * (C : ℚ))
    (rotation_pair_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.r d))) - 1 -
            Matrix.trace (E7Matrix Γ *
              permMatrix (h.smulEquiv (DihedralGroup.r d))) =
            (A : ℚ) + (B : ℚ) - (C : ℚ) ∨
          Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.r (-d)))) - 1 -
            Matrix.trace (E7Matrix Γ *
              permMatrix (h.smulEquiv (DihedralGroup.r (-d)))) =
            (A : ℚ) + (B : ℚ) - (C : ℚ))
    (reflection_zero_trace :
      Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.sr 0))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (A : ℚ) - (B : ℚ)) :
    D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C :=
  (Minus8ProjectionInversePairTraceBoundary.toCharacterValueBoundary
    ({ one_trace := one_trace
       rotation_pair_trace := rotation_pair_trace
       reflection_zero_trace := reflection_zero_trace } :
      Minus8ProjectionInversePairTraceBoundary h A B C))

end D19CharacterValueBoundary

end Moore57

/-!
# Linear-character consequences of inverse-pair trace boundaries

This file packages the inverse-pair projection trace boundaries into the
linear-character input and component-boundary consequences already available
for the concrete `E7` and `(-8)` projection character boundaries.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19LinearCharacterInput

/-- Inverse-pair projection trace boundaries for the concrete `E7` and `(-8)`
representations produce a linear-character input once the standard fixed-count
facts are supplied. -/
theorem nonempty_ofE7AndMinus8InversePairTraceBoundaries
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    Nonempty (D19LinearCharacterInput h) :=
  nonempty_ofE7AndMinus8CharacterBoundaries h
    alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hreflection_a0 hreflection_a1 hrotation_a0

end D19LinearCharacterInput

/-- Component-boundary consequence of inverse-pair trace boundaries for the
concrete `E7` and `(-8)` projection representations. -/
theorem representationCharacterComponentsBoundary_of_E7AndMinus8InversePairTraceBoundaries
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    RepresentationCharacterComponentsBoundary h :=
  representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundaries h
    alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hreflection_a0 hreflection_a1 hrotation_a0

end D19ActsOnMoore57

end Moore57

/-!
# Inverse-pair trace count raw-reflection fixed-star connectors

This file exposes the raw-reflection fixed-star and `K_{1,55}` wrappers directly
from inverse-pair trace boundaries plus the count-side inputs needed to build a
nonempty `D19LinearCharacterInput`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Inverse-pair E7/minus-8 trace boundaries plus the reflection and rotation
count inputs give the raw-reflection paper-shaped `56`-fixed-set star for any
reflection. -/
theorem involutionFixedSetStar56_of_E7AndMinus8InversePairTraceBoundariesAndReflectionCounts_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_nonempty_linearCharacterInput_raw_reflection
    (D19LinearCharacterInput.nonempty_ofE7AndMinus8InversePairTraceBoundaries
      h alpha beta gamma A B C e7Trace minus8Trace
      hreflection_a0 hreflection_a1 hrotation_a0)
    k

/-- Inverse-pair E7/minus-8 trace boundaries plus the reflection and rotation
count inputs give a nonempty explicit `K_{1,55}` witness for any reflection via
the raw-reflection bridge. -/
theorem nonempty_involutionK155_of_E7AndMinus8InversePairTraceBoundariesAndReflectionCounts_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_nonempty_linearCharacterInput_raw_reflection
    (D19LinearCharacterInput.nonempty_ofE7AndMinus8InversePairTraceBoundaries
      h alpha beta gamma A B C e7Trace minus8Trace
      hreflection_a0 hreflection_a1 hrotation_a0)
    k

end D19ActsOnMoore57

end

end Moore57

/-!
# Inverse-pair trace raw-reflection fixed-star connectors

This file composes the inverse-pair trace boundary bridge with the existing
raw-reflection fixed-star connectors.  It contains no new linear algebra or
graph theory: inverse-pair trace data is first expanded to the concrete
character-boundary API, and the existing paper-star/K155 raw-reflection
connectors supply the reflection-wise fixed-star outputs.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Inverse-pair E7/minus-8 trace boundaries plus one paper-shaped fixed-star
boundary give the raw-reflection paper-shaped `56`-fixed-set star for any
reflection. -/
theorem involutionFixedSetStar56_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56_raw_reflection
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar k

/-- Inverse-pair E7/minus-8 trace boundaries plus one paper-shaped fixed-star
boundary give a nonempty explicit `K_{1,55}` witness for any reflection via
the raw-reflection bridge. -/
theorem nonempty_involutionK155_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56_raw_reflection
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar k

/-- Inverse-pair E7/minus-8 trace boundaries plus one explicit `K_{1,55}`
witness give the raw-reflection paper-shaped `56`-fixed-set star for any
reflection. -/
theorem involutionFixedSetStar56_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_E7AndMinus8CharacterBoundariesAndInvolutionK155_raw_reflection
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK k

/-- Inverse-pair E7/minus-8 trace boundaries plus one explicit `K_{1,55}`
witness give a nonempty explicit `K_{1,55}` witness for any reflection via the
raw-reflection bridge. -/
theorem nonempty_involutionK155_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155_raw_reflection
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt)))
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_E7AndMinus8CharacterBoundariesAndInvolutionK155_raw_reflection
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK k

end D19ActsOnMoore57

end

end Moore57

/-!
# Inverse-pair trace no-go connectors for E7 and minus-8

This file is a thin wrapper layer from inverse-pair projection trace data to
the existing fixed-star no-go surfaces.  The trace data is first expanded to
the concrete character-boundary API; no linear algebra or representation theory
is reproved here.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Fixed-star reference-matching no-go from inverse-pair projection trace
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar

/-- Fixed-star local-obstruction no-go from inverse-pair projection trace
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar

/-- Fixed-star witness no-go from inverse-pair projection trace boundaries and
an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarWitnessBoundary_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar

/-- Fixed-star coordinate-witness no-go from inverse-pair projection trace
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar

/-- Lean-aware fixed-star final no-go from inverse-pair projection trace
boundaries and an explicit paper-shaped `56`-vertex fixed-star witness. -/
theorem no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8InversePairTraceBoundariesAndPaperFixedStar56
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
            star labeling :=
  no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndPaperFixedStar56
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hStar

/-- Fixed-star reference-matching no-go from inverse-pair projection trace
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK

/-- Fixed-star local-obstruction no-go from inverse-pair projection trace
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK

/-- Fixed-star witness no-go from inverse-pair projection trace boundaries and
an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarWitnessBoundary_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary
            star labeling :=
  no_D19_fixedStarWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK

/-- Fixed-star coordinate-witness no-go from inverse-pair projection trace
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK

/-- Lean-aware fixed-star final no-go from inverse-pair projection trace
boundaries and an explicit `K_{1,55}` reflection fixed-star witness. -/
theorem no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8InversePairTraceBoundariesAndInvolutionK155
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma)
    (minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C)
    {dt : ZMod 19}
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr dt))) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
            star labeling :=
  no_D19_leanAwareFixedStarFinalBoundary_of_E7AndMinus8CharacterBoundariesAndInvolutionK155
    h alpha beta gamma A B C
    e7Trace.toCharacterClassBoundary
    minus8Trace.toCharacterValueBoundary
    hK

end

end Moore57

/-!
# Boundary packages for inverse-pair E7/minus-8 trace data

This file bundles the inverse-pair trace boundaries together with the
count-side reflection and rotation inputs used to build
`Nonempty (D19LinearCharacterInput h)`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- A compact package for the inverse-pair trace boundaries and the count-side
inputs needed by the linear-character bridge. -/
structure E7Minus8InversePairTraceReflectionCountBoundary
    (h : D19ActsOnMoore57 V Γ) where
  alpha : ℕ
  beta : ℕ
  gamma : ℕ
  A : ℕ
  B : ℕ
  C : ℕ
  e7Trace : E7ProjectionInversePairTraceBoundary h alpha beta gamma
  minus8Trace : Minus8ProjectionInversePairTraceBoundary h A B C
  dt : ZMod 19
  reflection_fixed_count :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56
  reflection_adjacent_moved :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112
  rotation_fixed_count :
    ∀ d : ZMod 19, d ≠ 0 →
      fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1

namespace E7Minus8InversePairTraceReflectionCountBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The packaged trace and count inputs produce a nonempty linear-character
input. -/
theorem nonempty_d19LinearCharacterInput
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    Nonempty (D19LinearCharacterInput h) :=
  D19LinearCharacterInput.nonempty_ofE7AndMinus8InversePairTraceBoundaries
    h boundary.alpha boundary.beta boundary.gamma boundary.A boundary.B boundary.C
    boundary.e7Trace boundary.minus8Trace
    boundary.reflection_fixed_count boundary.reflection_adjacent_moved
    boundary.rotation_fixed_count

/-- The packaged boundary gives the raw-reflection paper-shaped
`56`-fixed-set star for any reflection. -/
theorem involutionFixedSetStar56_raw_reflection
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h)
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  involutionFixedSetStar56_of_E7AndMinus8InversePairTraceBoundariesAndReflectionCounts_raw_reflection
    h boundary.alpha boundary.beta boundary.gamma boundary.A boundary.B boundary.C
    boundary.e7Trace boundary.minus8Trace
    boundary.reflection_fixed_count boundary.reflection_adjacent_moved
    boundary.rotation_fixed_count k

/-- The packaged boundary gives a nonempty explicit `K_{1,55}` witness for any
reflection. -/
theorem nonempty_involutionK155_raw_reflection
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h)
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  nonempty_involutionK155_of_E7AndMinus8InversePairTraceBoundariesAndReflectionCounts_raw_reflection
    h boundary.alpha boundary.beta boundary.gamma boundary.A boundary.B boundary.C
    boundary.e7Trace boundary.minus8Trace
    boundary.reflection_fixed_count boundary.reflection_adjacent_moved
    boundary.rotation_fixed_count k

/-- The packaged inverse-pair trace boundary gives reflection fixed count `56`
for any reflection. -/
theorem fixedVertexCount_reflection_eq_56_raw_reflection
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h)
    (k : ZMod 19) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
  fixedVertexCount_reflection_eq_56_of_nonempty_linearCharacterInput_raw_reflection
    boundary.nonempty_d19LinearCharacterInput k

/-- The packaged inverse-pair trace boundary gives reflection adjacent-moved
count `112` for any reflection. -/
theorem adjacentMovedCount_reflection_eq_112_raw_reflection
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h)
    (k : ZMod 19) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 112 :=
  adjacentMovedCount_reflection_eq_112_of_nonempty_linearCharacterInput_raw_reflection
    boundary.nonempty_d19LinearCharacterInput k

/-- The packaged inverse-pair trace boundary eliminates the regular-`10`
branch of the raw split, hence gives the fixed-center leaf boundary. -/
theorem reflectionFixedCenterLeafBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  reflectionFixedCenterLeafBoundary_of_nonempty_linearCharacterInput
    boundary.nonempty_d19LinearCharacterInput

/-- The packaged inverse-pair trace boundary supplies the representation
component boundary. -/
theorem representationCharacterComponentsBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    RepresentationCharacterComponentsBoundary h :=
  representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
    boundary.nonempty_d19LinearCharacterInput

/-- Current-final-gap no-go from the packaged nonempty linear-character input. -/
theorem no_currentFinalGapBoundary
    (boundary : E7Minus8InversePairTraceReflectionCountBoundary h) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  no_D19_currentFinalGapBoundary_of_nonempty_linearCharacterInput h
    boundary.nonempty_d19LinearCharacterInput

end E7Minus8InversePairTraceReflectionCountBoundary

end D19ActsOnMoore57

end

end Moore57

