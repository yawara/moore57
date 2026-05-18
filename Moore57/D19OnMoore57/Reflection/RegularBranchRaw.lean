import Moore57.D19OnMoore57.Reflection.FixedCenterLocal
import Mathlib.Tactic

/-!
# Raw regular reflection branch facts

This file records the part of the regular fixed-induced branch that does not
use any character input.  A regular fixed-induced graph with strong
`(λ, μ) = (0, 1)` parameters has fixed count `d^2 + 1`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

set_option linter.flexible false in
/-- Raw strongly-regular parameter arithmetic for a regular fixed-induced
graph.  No representation or character input is used here. -/
theorem fixedInducedGraph_regular_fixedVertexCount_eq_degree_sq_add_one
    (g : DihedralGroup 19) (d : ℕ)
    (hreg :
      ∀ x : fixedVertexSet (h.smulEquiv g),
        (h.fixedInducedGraph g).degree x = d)
    (hpos : 0 < fixedVertexCount (h.smulEquiv g)) :
    fixedVertexCount (h.smulEquiv g) = d * d + 1 := by
  let Gfix := h.fixedInducedGraph g
  let n := fixedVertexCount (h.smulEquiv g)
  have hsrg : Gfix.IsSRGWith n d 0 1 :=
    h.fixedInducedGraph_isSRGWith_of_regular g d hreg
  have hparam := SimpleGraph.IsSRGWith.param_eq Gfix hsrg hpos
  simp at hparam
  rcases Fintype.card_pos_iff.mp (by
      simpa [n, fixedVertexCount_eq_card_fixedVertexSet] using hpos) with ⟨x⟩
  have hd_lt_n : d < n := by
    have hdegree_lt := Gfix.degree_lt_card_verts x
    rw [hreg x] at hdegree_lt
    simpa [Gfix, n, fixedVertexCount_eq_card_fixedVertexSet] using hdegree_lt
  by_cases hd0 : d = 0
  · subst d
    have hn_eq_one : n = 1 := by
      omega
    simp [n, hn_eq_one]
  · have hdpos : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd0)
    have hsub_pos : 1 ≤ n - d := by omega
    have hdle : d ≤ n := Nat.le_of_lt hd_lt_n
    have hparam_nat : d * (d - 1) = n - d - 1 := by
      simpa [Nat.sub_zero, Nat.mul_one] using hparam
    have hparam_int := congrArg (fun m : ℕ => (m : ℤ)) hparam_nat
    change ((d * (d - 1) : ℕ) : ℤ) = ((n - d - 1 : ℕ) : ℤ) at hparam_int
    rw [Nat.cast_mul, Nat.cast_sub hdpos, Nat.cast_sub hsub_pos,
      Nat.cast_sub hdle] at hparam_int
    norm_num at hparam_int
    have hn_int : (n : ℤ) = (d : ℤ) * (d : ℤ) + 1 := by
      nlinarith
    have hn_nat : n = d * d + 1 := by
      exact_mod_cast hn_int
    simpa [n] using hn_nat

/-- Reflection-specialized version: a regular fixed-induced graph for a
reflection has fixed count `d^2 + 1`, because the rotation-fixed center is
always fixed by the reflection. -/
theorem reflection_regular_fixedVertexCount_eq_degree_sq_add_one
    (k : ZMod 19) (d : ℕ)
    (hreg :
      ∀ x : fixedVertexSet (h.smulEquiv (DihedralGroup.sr k)),
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree x = d) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = d * d + 1 := by
  have hpos : 0 < fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) := by
    rw [fixedVertexCount_eq_card_fixedVertexSet]
    exact Fintype.card_pos_iff.mpr
      ⟨⟨h.rotationFixedCenter, by
        change h.smul (DihedralGroup.sr k) h.rotationFixedCenter =
          h.rotationFixedCenter
        exact h.reflection_smul_rotationFixedCenter k⟩⟩
  exact h.fixedInducedGraph_regular_fixedVertexCount_eq_degree_sq_add_one
    (DihedralGroup.sr k) d hreg hpos

end D19ActsOnMoore57

end

end Moore57
