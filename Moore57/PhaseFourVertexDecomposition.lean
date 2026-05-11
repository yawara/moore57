import Moore57.PhaseFourPrebuilt
import Moore57.PhaseOnePrebuilt
import Moore57.D19VertexPermutationRepresentation
import Moore57.D19BurnsideFixedCountConstraints
import Moore57.RotationFixedCountOneFrontier
import Moore57.D19RepresentationMathlibCharacterTools

/-!
# Phase 4.3 / 4.4: vertex permutation character and its D₁₉ linear-character form

Natural-language Section 4.3 records the rotation orbit decomposition of the
vertex space (`1^1, 19^55, 38^58`).  Section 4.4 turns this into the linear
character

  `π_V = 114·1 + 58·ε + 171·ρ`

of `DihedralGroup 19` on `V`.

This file packages the class values of the mathlib vertex permutation
representation and verifies the linear-character equality.  The class values
come from Phase 1 (`a_0(r^d)=1` for nontrivial rotations, `a_0(t)=56` for any
reflection) and the Burnside identity term `|V|=3250`.

The identity `114 + 58 + 18·171 = 3250` (dimension), `114 + 58 − 171 = 1`
(rotation), and `114 − 58 = 56` (reflection) pin down the linear character on
every class.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Phase 4.3 (identity character value): the vertex permutation character at
the identity is `|V| = 3250`. -/
theorem vertex_character_one_eq_3250 (h : D19ActsOnMoore57 V Γ) :
    (h.vertexPermutationRepresentation).character (1 : DihedralGroup 19) =
      (3250 : ℚ) := by
  rw [h.vertexPermutationRepresentation_character_eq_fixedVertexCount,
    h.fixedVertexCount_smulEquiv_one]
  norm_num

/-- Phase 4.3 (rotation character value): for every nontrivial rotation `r^d`,
the vertex permutation character equals `a_0(r^d) = 1`. -/
theorem vertex_character_rotation_ne
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} (hd : d ≠ 0) :
    (h.vertexPermutationRepresentation).character (DihedralGroup.r d) =
      (1 : ℚ) := by
  rw [h.vertexPermutationRepresentation_character_eq_fixedVertexCount,
    h.rotationFixedCountOne_smulEquiv d hd]
  norm_num

/-- Phase 4.3 (reflection character value): for every reflection `sr k`, the
vertex permutation character equals `a_0(t) = 56`. -/
theorem vertex_character_reflection
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    (h.vertexPermutationRepresentation).character (DihedralGroup.sr k) =
      (56 : ℚ) := by
  rw [h.vertexPermutationRepresentation_character_eq_fixedVertexCount,
    h.reflection_fixedVertexCount_eq_fiftySix k]
  norm_num

/-- Phase 4.4: the vertex permutation character agrees pointwise with the
linear D₁₉ rational character `114·1 + 58·ε + 171·ρ`.

This is the natural-language identity `π_V = 114·1 + 58·ε + 171·ρ` arising from
the vertex orbit decomposition `1^1, 19^55, 38^58`. -/
theorem vertex_character_eq_d19LinearCharacter_114_58_171
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) :
    (h.vertexPermutationRepresentation).character g =
      (d19LinearCharacter 114 58 171 g : ℚ) := by
  refine character_eq_d19Linear_of_values
    (h.vertexPermutationRepresentation).character 114 58 171
    ?_ ?_ ?_ g
  · -- identity: 3250 = 114 + 58 + 18·171
    rw [h.vertex_character_one_eq_3250]
    norm_num
  · -- nontrivial rotation: 1 = 114 + 58 − 171
    intro d hd
    rw [h.vertex_character_rotation_ne hd]
    norm_num
  · -- reflection: 56 = 114 − 58
    intro k
    rw [h.vertex_character_reflection k]
    norm_num

end D19ActsOnMoore57

end Moore57
