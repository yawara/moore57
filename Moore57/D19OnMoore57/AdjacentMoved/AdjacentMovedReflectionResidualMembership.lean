import Moore57.D19OnMoore57.AdjacentMoved.AdjacentMovedReflectionComplementResidual

-- The theorem statements below expand through nested indexed finset unions
-- over `Fin 2 × Fin 56` and rotation orbit membership.
set_option maxRecDepth 10000

/-!
# Membership criteria for reflection-copy residuals

This file exposes the canonical complement residual as the vertices that lie in
neither the original selected rotation-orbit family nor its reflected copy.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- Membership in the reflection-copy union in indexed form. -/
theorem mem_reflectionCopyUnion_iff
    (base : Fin 56 → V) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyUnion h base k ↔
      ∃ side : Fin 2, ∃ q : Fin 56, ∃ i : ZMod 19,
        h.rotation i (reflectionCopyBase h base k (side, q)) = y := by
  classical
  constructor
  · intro hy
    change y ∈
      (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion
        (fun sideq =>
          h.rotationOrbitFinset (reflectionCopyBase h base k sideq)) at hy
    rcases Finset.mem_biUnion.mp hy with ⟨sideq, _hsideq, hyOrbit⟩
    rcases sideq with ⟨side, q⟩
    rcases (h.mem_rotationOrbitFinset
        (reflectionCopyBase h base k (side, q)) y).mp hyOrbit with ⟨i, hi⟩
    exact ⟨side, q, i, hi⟩
  · rintro ⟨side, q, i, hi⟩
    change y ∈
      (Finset.univ : Finset (Fin 2 × Fin 56)).biUnion
        (fun sideq =>
          h.rotationOrbitFinset (reflectionCopyBase h base k sideq))
    exact Finset.mem_biUnion.mpr
      ⟨(side, q), Finset.mem_univ _,
        (h.mem_rotationOrbitFinset
          (reflectionCopyBase h base k (side, q)) y).mpr ⟨i, hi⟩⟩

/-- Membership in the reflection-copy union, split into original and reflected
orbit families. -/
theorem mem_reflectionCopyUnion_iff_or
    (base : Fin 56 → V) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyUnion h base k ↔
      (∃ q : Fin 56, ∃ i : ZMod 19, h.rotation i (base q) = y) ∨
        ∃ q : Fin 56, ∃ i : ZMod 19,
          h.rotation i (h.smul (DihedralGroup.sr k) (base q)) = y := by
  classical
  constructor
  · intro hy
    rcases (h.mem_reflectionCopyUnion_iff base k y).mp hy with
      ⟨side, q, i, hi⟩
    fin_cases side
    · left
      exact ⟨q, i, by simpa [reflectionCopyBase] using hi⟩
    · right
      exact ⟨q, i, by simpa [reflectionCopyBase] using hi⟩
  · rintro (horig | href)
    · rcases horig with ⟨q, i, hi⟩
      exact (h.mem_reflectionCopyUnion_iff base k y).mpr
        ⟨0, q, i, by simpa [reflectionCopyBase] using hi⟩
    · rcases href with ⟨q, i, hi⟩
      exact (h.mem_reflectionCopyUnion_iff base k y).mpr
        ⟨1, q, i, by simpa [reflectionCopyBase] using hi⟩

/-- Membership in the canonical reflection-copy residual is exactly avoiding
both the original selected orbit family and its reflected copy. -/
theorem mem_reflectionCopyResidual_iff
    (base : Fin 56 → V) (k : ZMod 19) (y : V) :
    y ∈ reflectionCopyResidual h base k ↔
      ¬ ((∃ q : Fin 56, ∃ i : ZMod 19, h.rotation i (base q) = y) ∨
        ∃ q : Fin 56, ∃ i : ZMod 19,
          h.rotation i (h.smul (DihedralGroup.sr k) (base q)) = y) := by
  classical
  rw [reflectionCopyResidual, Finset.mem_compl,
    h.mem_reflectionCopyUnion_iff_or base k y]

/-- A residual vertex is not in the original selected orbit family. -/
theorem not_mem_original_orbitFamily_of_mem_reflectionCopyResidual
    (base : Fin 56 → V) (k : ZMod 19) {y : V}
    (hy : y ∈ reflectionCopyResidual h base k) :
    ¬ ∃ q : Fin 56, ∃ i : ZMod 19, h.rotation i (base q) = y := by
  intro horig
  exact (h.mem_reflectionCopyResidual_iff base k y).mp hy (Or.inl horig)

/-- A residual vertex is not in the reflected selected orbit family. -/
theorem not_mem_reflected_orbitFamily_of_mem_reflectionCopyResidual
    (base : Fin 56 → V) (k : ZMod 19) {y : V}
    (hy : y ∈ reflectionCopyResidual h base k) :
    ¬ ∃ q : Fin 56, ∃ i : ZMod 19,
      h.rotation i (h.smul (DihedralGroup.sr k) (base q)) = y := by
  intro href
  exact (h.mem_reflectionCopyResidual_iff base k y).mp hy (Or.inr href)

end D19ActsOnMoore57

end Moore57
