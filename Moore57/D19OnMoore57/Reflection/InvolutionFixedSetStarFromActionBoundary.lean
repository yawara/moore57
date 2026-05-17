import Moore57.D19OnMoore57.Reflection.InvolutionK155FromActionBoundary
import Moore57.D19OnMoore57.Involution.FixedStarPaperBoundary

/-!
# Reflection paper fixed-star from action-level data

This file isolates the route from a raw reflection in a `D19` action to the
paper-shaped fixed-star statement.  The reflection action supplies the
involutive graph automorphism fields automatically; the remaining inputs are
the fixed-point count and the fixed-star geometry.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- A reflection acts as an involution on vertices. -/
theorem reflection_smulEquiv_involutive
    (k : ZMod 19) :
    Function.Involutive (h.smulEquiv (DihedralGroup.sr k)) := by
  intro v
  change (h.smulEquiv (DihedralGroup.sr k) *
      h.smulEquiv (DihedralGroup.sr k)) v = v
  rw [← h.smulEquiv_mul, DihedralGroup.sr_mul_self, h.smulEquiv_one]
  rfl

/-- A reflection acts by graph automorphisms on the Moore graph. -/
theorem reflection_smulEquiv_automorphism
    (k : ZMod 19) :
    ∀ v w : V,
      Γ.Adj v w ↔
        Γ.Adj ((h.smulEquiv (DihedralGroup.sr k)) v)
          ((h.smulEquiv (DihedralGroup.sr k)) w) := by
  intro v w
  change Γ.Adj v w ↔
    Γ.Adj (h.smul (DihedralGroup.sr k) v)
      (h.smul (DihedralGroup.sr k) w)
  exact h.smul_adj (DihedralGroup.sr k) v w

/-- A reflection is non-trivial as a vertex permutation (faithfulness +
constructor distinctness `sr k ≠ r 0`). -/
theorem reflection_smulEquiv_ne_one
    (k : ZMod 19) :
    h.smulEquiv (DihedralGroup.sr k) ≠ 1 := by
  intro hone
  have hgroup : DihedralGroup.sr k = (1 : DihedralGroup 19) := by
    apply h.faithful (DihedralGroup.sr k) 1
    intro v
    have hv : h.smul (DihedralGroup.sr k) v = v := by
      have hv' : h.smulEquiv (DihedralGroup.sr k) v = (1 : Equiv.Perm V) v := by
        rw [hone]
      simpa using hv'
    rw [h.one_smul]
    exact hv
  rw [show (1 : DihedralGroup 19) = DihedralGroup.r 0 from rfl] at hgroup
  cases hgroup

/-- Direct constructor for the paper-shaped fixed-star statement for a raw
reflection: only the fixed count and star-center geometry remain as inputs. -/
theorem involutionFixedSetStar56_of_reflection_fixedVertexCount_and_fixedSetStarWithCenter
    (k : ZMod 19)
    (hfix : fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56)
    (hcenter :
      ∃ c : V, FixedSetStarWithCenter Γ (h.smulEquiv (DihedralGroup.sr k)) c) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) where
  involutive := h.reflection_smulEquiv_involutive k
  automorphism := h.reflection_smulEquiv_automorphism k
  fixed_card := by
    simpa using hfix
  exists_center := hcenter

/-- Per-reflection family form of
`involutionFixedSetStar56_of_reflection_fixedVertexCount_and_fixedSetStarWithCenter`. -/
theorem reflection_involutionFixedSetStar56_of_fixedVertexCount_and_fixedSetStarWithCenter
    (hfix : ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56)
    (hcenter : ∀ k : ZMod 19,
      ∃ c : V, FixedSetStarWithCenter Γ (h.smulEquiv (DihedralGroup.sr k)) c) :
    ∀ k : ZMod 19,
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  intro k
  exact h.involutionFixedSetStar56_of_reflection_fixedVertexCount_and_fixedSetStarWithCenter
    k (hfix k) (hcenter k)

/-- Existing constructive center-count data for a raw reflection gives the
paper-shaped fixed-star statement. -/
theorem involutionFixedSetStar56OfReflectionFixedNeighborCenterCount
    (k : ZMod 19)
    (c : reflectionFixedVertex h k)
    (hc :
      (reflectionFixedNeighborFinset h k (c : V)).card = 55)
    (hfix :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  (h.involutionK155OfReflectionFixedNeighborCenterCount k c hc hfix)
    |>.toInvolutionFixedSetStar56

/-- Prop-valued wrapper around
`involutionFixedSetStar56OfReflectionFixedNeighborCenterCount`. -/
theorem nonempty_involutionFixedSetStar56_of_reflectionFixedNeighbor_center_count
    (k : ZMod 19)
    (c : reflectionFixedVertex h k)
    (hc :
      (reflectionFixedNeighborFinset h k (c : V)).card = 55)
    (hfix :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    Nonempty (InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  ⟨h.involutionFixedSetStar56OfReflectionFixedNeighborCenterCount k c hc hfix⟩

end D19ActsOnMoore57

namespace ReflectionFixedNeighborStarCenterData

variable {h : D19ActsOnMoore57 V Γ}

/-- Construct paper-shaped fixed-star witnesses from constructive fixed-neighbor
center data and the reflection fixed-count `56`. -/
def toInvolutionFixedSetStar56
    (input : ReflectionFixedNeighborStarCenterData h)
    (hfix : ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    ∀ k : ZMod 19,
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  intro k
  exact h.involutionFixedSetStar56OfReflectionFixedNeighborCenterCount
    k (input.center k) (input.center_count k) (hfix k)

end ReflectionFixedNeighborStarCenterData

namespace ReflectionFixedInducedStarCenterData

variable {h : D19ActsOnMoore57 V Γ}

/-- Construct paper-shaped fixed-star witnesses from constructive induced-degree
center data and the reflection fixed-count `56`. -/
def toInvolutionFixedSetStar56
    (input : ReflectionFixedInducedStarCenterData h)
    (hfix : ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    ∀ k : ZMod 19,
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  input.toReflectionFixedNeighborStarCenterData.toInvolutionFixedSetStar56 hfix

end ReflectionFixedInducedStarCenterData

namespace ReflectionFixedNeighborStarCounts

variable {h : D19ActsOnMoore57 V Γ}

/-- Prop-valued fixed-neighbor star counts plus the reflection fixed-count `56`
give paper-shaped fixed-star witnesses. -/
theorem nonempty_involutionFixedSetStar56
    (input : ReflectionFixedNeighborStarCounts h)
    (hfix : ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    ∀ k : ZMod 19,
      Nonempty (InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k))) := by
  intro k
  rcases input.exists_center_count k with ⟨c, hc, _⟩
  exact h.nonempty_involutionFixedSetStar56_of_reflectionFixedNeighbor_center_count
    k c hc (hfix k)

end ReflectionFixedNeighborStarCounts

namespace ReflectionFixedInducedStarDegrees

variable {h : D19ActsOnMoore57 V Γ}

/-- Prop-valued induced fixed-graph star degrees plus the reflection fixed-count
`56` give paper-shaped fixed-star witnesses. -/
theorem nonempty_involutionFixedSetStar56
    (input : ReflectionFixedInducedStarDegrees h)
    (hfix : ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    ∀ k : ZMod 19,
      Nonempty (InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k))) := by
  intro k
  rcases input.exists_center_degree k with ⟨c, hc, _⟩
  have hdegree :=
    h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
      (DihedralGroup.sr k) c
  have hcount :
      (reflectionFixedNeighborFinset h k (c : V)).card = 55 := by
    simpa [reflectionFixedNeighborFinset] using hdegree.symm.trans hc
  exact h.nonempty_involutionFixedSetStar56_of_reflectionFixedNeighbor_center_count
    k c hcount (hfix k)

end ReflectionFixedInducedStarDegrees

namespace ReflectionFixedStarBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The older fixed-star boundary plus the reflection fixed-count `56` also
yields paper-shaped fixed-star witnesses. -/
theorem nonempty_involutionFixedSetStar56
    (boundary : ReflectionFixedStarBoundary h)
    (hfix : ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    ∀ k : ZMod 19,
      Nonempty (InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k))) := by
  intro k
  rcases boundary.exists_center k with ⟨c, hc⟩
  have hdegree :=
    h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
      (DihedralGroup.sr k) c
  have hcount :
      (reflectionFixedNeighborFinset h k (c : V)).card = 55 := by
    simpa [reflectionFixedNeighborFinset, IsReflectionFixedStarCenter] using
      hdegree.symm.trans hc.1
  exact h.nonempty_involutionFixedSetStar56_of_reflectionFixedNeighbor_center_count
    k c hcount (hfix k)

end ReflectionFixedStarBoundary

end

end Moore57
