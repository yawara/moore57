import Moore57.D19OnMoore57.D19Core.BurnsideFixedCountConstraints
import Moore57.D19OnMoore57.D19Core.RepresentationMathlibCharacterTools
import Moore57.D19OnMoore57.Reflection.RawActionFixedStar

/-!
# Vertex permutation character decomposition

Section 4.3 / 4.4 of the natural-language proof records the rotation orbit
decomposition of the vertex space (`1^1, 19^55, 38^58`) and turns it into the
linear character

  `π_V = 114·1 + 58·ε + 171·ρ`

of `DihedralGroup 19` on `V`.

The class values of the vertex permutation character come from raw-action
fixed counts: `a₀(1) = |V| = 3250` (Burnside), `a₀(rᵈ) = 1` for nontrivial
rotations (`rotationFixedCountOne_smulEquiv`), and `a₀(t) = 56` for any
reflection (`fixedVertexCount_reflection_eq_56_of_raw_action`).

The identities `114 + 58 + 18·171 = 3250` (dimension), `114 + 58 − 171 = 1`
(rotation), and `114 − 58 = 56` (reflection) pin down the linear character on
every class.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Identity character value: the vertex permutation character at the identity
is `|V| = 3250`. -/
theorem vertex_character_one_eq_3250 (h : D19ActsOnMoore57 V Γ) :
    (h.vertexPermutationRepresentation).character (1 : DihedralGroup 19) =
      (3250 : ℚ) := by
  rw [h.vertexPermutationRepresentation_character_eq_fixedVertexCount,
    h.fixedVertexCount_smulEquiv_one]
  norm_num

/-- Rotation character value: for every nontrivial rotation `rᵈ`, the vertex
permutation character equals `a₀(rᵈ) = 1`. -/
theorem vertex_character_rotation_ne
    (h : D19ActsOnMoore57 V Γ) {d : ZMod 19} (hd : d ≠ 0) :
    (h.vertexPermutationRepresentation).character (DihedralGroup.r d) =
      (1 : ℚ) := by
  rw [h.vertexPermutationRepresentation_character_eq_fixedVertexCount,
    h.rotationFixedCountOne_smulEquiv d hd]
  norm_num

/-- Reflection character value: for every reflection `sr k`, the vertex
permutation character equals `a₀(t) = 56`. -/
theorem vertex_character_reflection
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    (h.vertexPermutationRepresentation).character (DihedralGroup.sr k) =
      (56 : ℚ) := by
  rw [h.vertexPermutationRepresentation_character_eq_fixedVertexCount,
    h.fixedVertexCount_reflection_eq_56_of_raw_action k]
  norm_num

/-- The vertex permutation character agrees pointwise with the linear D₁₉
rational character `114·1 + 58·ε + 171·ρ`.

This is the natural-language identity `π_V = 114·1 + 58·ε + 171·ρ` arising
from the vertex orbit decomposition `1^1, 19^55, 38^58`. -/
theorem vertex_character_eq_d19LinearCharacter_114_58_171
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) :
    (h.vertexPermutationRepresentation).character g =
      (d19LinearCharacter 114 58 171 g : ℚ) := by
  refine character_eq_d19Linear_of_values
    (h.vertexPermutationRepresentation).character 114 58 171
    ?_ ?_ ?_ g
  · rw [h.vertex_character_one_eq_3250]; norm_num
  · intro d hd
    rw [h.vertex_character_rotation_ne hd]; norm_num
  · intro k
    rw [h.vertex_character_reflection k]; norm_num

end D19ActsOnMoore57

end Moore57
