import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCReflectionLabeling

/-!
# Reflection fixed-center leaf boundary

This file isolates the fixed-star input used by the reflection-labeled branch
argument.  The natural-language proof obtains it from the fact that an
involution fixed set is a `K_{1,55}` star and that `rotationFixedCenter` is a
leaf of that star.  Downstream Lean only needs the induced fixed-graph degree
bound at `rotationFixedCenter`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Boundary form of the fixed-star leaf input for reflections: in every
reflection fixed induced graph, the rotation-fixed center has degree at most
one. -/
structure ReflectionFixedCenterLeafBoundary
    (h : D19ActsOnMoore57 V Γ) where
  degree_le_one :
    ∀ k : ZMod 19,
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
          ⟨h.rotationFixedCenter, by
            change h.smul (DihedralGroup.sr k) h.rotationFixedCenter =
              h.rotationFixedCenter
            exact h.reflection_smul_rotationFixedCenter k⟩ ≤ 1

namespace ReflectionFixedCenterLeafBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the fixed-star leaf boundary to the fixed-neighbor bound already
consumed by the reflection quotient-orbit argument. -/
theorem fixed_center_neighbors_card_le_one
    (boundary : ReflectionFixedCenterLeafBoundary h) :
    ∀ k : ZMod 19,
      ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
        h.smul (DihedralGroup.sr k) y = y).card ≤ 1 :=
  BranchOrbitABCReflectionLabeling.fixed_center_neighbors_card_le_one_of_forall_fixedInducedDegree_le_one
    (h := h) boundary.degree_le_one

/-- The fixed-star leaf boundary forces a nontrivial reflection action on the
three rotation-orbits of neighbors around `rotationFixedCenter`. -/
theorem exists_reflectionCenterNeighborOrbitIndex_ne
    (boundary : ReflectionFixedCenterLeafBoundary h)
    (base : Fin 3 → V)
    (base_adj : ∀ q : Fin 3, Γ.Adj h.rotationFixedCenter (base q))
    (base_pairwise_disjoint :
      ∀ q r : Fin 3, q ≠ r →
        Disjoint (h.rotationOrbitFinset (base q))
          (h.rotationOrbitFinset (base r)))
    (base_cover :
      Γ.neighborFinset h.rotationFixedCenter = h.orbitFamilyUnion base)
    (k : ZMod 19) :
    ∃ b : Fin 3,
      BranchOrbitABCReflectionLabeling.reflectionCenterNeighborOrbitIndex
        (h := h) base base_adj base_cover k b ≠ b :=
  BranchOrbitABCReflectionLabeling.exists_reflectionCenterNeighborOrbitIndex_ne_of_fixed_neighbors_card_le_one
    (h := h) base base_adj base_pairwise_disjoint base_cover k
    (boundary.fixed_center_neighbors_card_le_one k)

end ReflectionFixedCenterLeafBoundary

end

end Moore57
