import Moore57.D19OnMoore57.BranchOrbit.ABCReflectionFixedStarBoundary

/-!
# Reflection fixed-star boundary from action-level data

This file is a thin connector around the current fixed-induced-graph API.  It
does not assert the missing `K_{1,55}` theorem for reflection fixed sets.
Instead it packages the precise degree/count inputs that are enough to build
`ReflectionFixedStarBoundary`, and connects the action-level fixed-neighbor
count formulation to induced degrees via
`D19ActsOnMoore57.fixedInducedGraph_degree_eq_fixedNeighborFinset_card`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The ambient neighbors of `v` fixed by the reflection `sr k`. -/
def reflectionFixedNeighborFinset
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) (v : V) : Finset V :=
  (Γ.neighborFinset v).filter fun w => h.smul (DihedralGroup.sr k) w = w

/-- Degree-distribution input for the reflection fixed induced graphs.

For every reflection fixed induced graph, this records a vertex of degree `55`,
all other fixed vertices having degree at most `1`, and separately that the
rotation-fixed center has degree at most `1`. -/
structure ReflectionFixedInducedStarDegrees
    (h : D19ActsOnMoore57 V Γ) : Prop where
  exists_center_degree :
    ∀ k : ZMod 19,
      ∃ c : reflectionFixedVertex h k,
        (h.fixedInducedGraph (DihedralGroup.sr k)).degree c = 55 ∧
          ∀ x : reflectionFixedVertex h k,
            x ≠ c → (h.fixedInducedGraph (DihedralGroup.sr k)).degree x ≤ 1
  rotationFixedCenter_degree_le_one :
    ∀ k : ZMod 19,
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
          (reflectionRotationFixedCenterVertex h k) ≤ 1

namespace ReflectionFixedInducedStarDegrees

variable {h : D19ActsOnMoore57 V Γ}

/-- The degree-distribution boundary is exactly enough to recover the existing
`ReflectionFixedStarBoundary`. -/
def toReflectionFixedStarBoundary
    (input : ReflectionFixedInducedStarDegrees h) :
    ReflectionFixedStarBoundary h where
  exists_center := input.exists_center_degree
  rotationFixedCenter_not_center := by
    intro k hcenter
    have hle := input.rotationFixedCenter_degree_le_one k
    simp [hcenter.1] at hle

end ReflectionFixedInducedStarDegrees

/-- Action-level fixed-neighbor count input for the same reflection fixed-star
shape.  This is often closer to data produced directly from the group action. -/
structure ReflectionFixedNeighborStarCounts
    (h : D19ActsOnMoore57 V Γ) : Prop where
  exists_center_count :
    ∀ k : ZMod 19,
      ∃ c : reflectionFixedVertex h k,
        (reflectionFixedNeighborFinset h k (c : V)).card = 55 ∧
          ∀ x : reflectionFixedVertex h k,
            x ≠ c → (reflectionFixedNeighborFinset h k (x : V)).card ≤ 1
  rotationFixedCenter_count_le_one :
    ∀ k : ZMod 19,
      (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card ≤ 1

namespace ReflectionFixedNeighborStarCounts

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert reflection fixed-neighbor counts to induced fixed-graph degrees
using the existing degree/count bridge. -/
def toReflectionFixedInducedStarDegrees
    (input : ReflectionFixedNeighborStarCounts h) :
    ReflectionFixedInducedStarDegrees h where
  exists_center_degree := by
    intro k
    rcases input.exists_center_count k with ⟨c, hc_degree, hc_other⟩
    refine ⟨c, ?_, ?_⟩
    · have hdegree :=
        h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
          (DihedralGroup.sr k) c
      simpa [reflectionFixedNeighborFinset] using hdegree.trans hc_degree
    · intro x hx
      have hdegree :=
        h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
          (DihedralGroup.sr k) x
      rw [hdegree]
      simpa [reflectionFixedNeighborFinset] using hc_other x hx
  rotationFixedCenter_degree_le_one := by
    intro k
    have hdegree :=
      h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
        (DihedralGroup.sr k) (reflectionRotationFixedCenterVertex h k)
    rw [hdegree]
    simpa [reflectionFixedNeighborFinset, reflectionRotationFixedCenterVertex] using
      input.rotationFixedCenter_count_le_one k

/-- The action-level fixed-neighbor count input is enough to recover the
existing fixed-star boundary. -/
def toReflectionFixedStarBoundary
    (input : ReflectionFixedNeighborStarCounts h) :
    ReflectionFixedStarBoundary h :=
  input.toReflectionFixedInducedStarDegrees.toReflectionFixedStarBoundary

end ReflectionFixedNeighborStarCounts

/-- Convenience constructor from induced fixed-graph degree data. -/
def reflectionFixedStarBoundary_of_fixedInduced_degrees
    {h : D19ActsOnMoore57 V Γ}
    (input : ReflectionFixedInducedStarDegrees h) :
    ReflectionFixedStarBoundary h :=
  input.toReflectionFixedStarBoundary

/-- Convenience constructor from action-level reflection fixed-neighbor counts. -/
def reflectionFixedStarBoundary_of_reflectionFixedNeighbor_counts
    {h : D19ActsOnMoore57 V Γ}
    (input : ReflectionFixedNeighborStarCounts h) :
    ReflectionFixedStarBoundary h :=
  input.toReflectionFixedStarBoundary

end

end Moore57
