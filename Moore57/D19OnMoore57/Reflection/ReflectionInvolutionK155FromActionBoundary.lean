import Moore57.D19OnMoore57.Reflection.ReflectionFixedStarFromActionBoundary
import Moore57.D19OnMoore57.Reflection.ReflectionFixedCenterLeafActionFrontier
import Moore57.D19OnMoore57.Involution.InvolutionFixedStarA1

/-!
# Reflection `K_{1,55}` from fixed-neighbor action data

This file isolates a useful intermediate step toward the raw reflection
`InvolutionK155` theorem.  If a reflection has a fixed vertex with exactly
`55` fixed neighbors, and the total reflection fixed-vertex count is `56`,
then those fixed vertices are exactly the center plus its fixed neighbors.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- A reflection fixed vertex with `55` fixed neighbors, together with the
total reflection fixed count `56`, determines the explicit `K_{1,55}` fixed
star for that reflection. -/
def involutionK155OfReflectionFixedNeighborCenterCount
    (k : ZMod 19)
    (c : reflectionFixedVertex h k)
    (hc :
      (reflectionFixedNeighborFinset h k (c : V)).card = 55)
    (hfix :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  classical
  let σ : Equiv.Perm V := h.smulEquiv (DihedralGroup.sr k)
  let leaves : Finset V := reflectionFixedNeighborFinset h k (c : V)
  have hc_fixed : σ (c : V) = (c : V) := by
    change h.smul (DihedralGroup.sr k) (c : V) = (c : V)
    exact c.property
  have hcenter_notMem : (c : V) ∉ leaves := by
    intro hmem
    have hAdj : Γ.Adj (c : V) (c : V) := by
      simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp hmem).1
    exact (Γ.loopless.irrefl (a := (c : V)) hAdj).elim
  have hinsert_subset :
      insert (c : V) leaves ⊆ fixedFinset σ := by
    intro v hv
    rw [Finset.mem_insert] at hv
    rw [mem_fixedFinset]
    rcases hv with hv | hv
    · rw [hv]
      exact hc_fixed
    · change h.smul (DihedralGroup.sr k) v = v
      exact (Finset.mem_filter.mp hv).2
  have hinsert_card : (insert (c : V) leaves).card = 56 := by
    rw [Finset.card_insert_of_notMem hcenter_notMem]
    rw [show leaves.card = 55 from hc]
  have hfixed_card : (fixedFinset σ).card = 56 := by
    simpa [σ] using hfix
  have hinsert_eq_fixed : insert (c : V) leaves = fixedFinset σ :=
    Finset.eq_of_subset_of_card_le hinsert_subset (by omega)
  refine
    { involutive := ?_
      automorphism := ?_
      center := (c : V)
      leaves := leaves
      center_notMem := hcenter_notMem
      leaves_card := by
        exact hc
      fixed_iff := ?_
      center_adj_leaves := ?_
      leaves_pairwise_not_adj := ?_ }
  · intro v
    change (h.smulEquiv (DihedralGroup.sr k) *
        h.smulEquiv (DihedralGroup.sr k)) v = v
    rw [← h.smulEquiv_mul, DihedralGroup.sr_mul_self, h.smulEquiv_one]
    rfl
  · intro v w
    change Γ.Adj v w ↔
      Γ.Adj (h.smul (DihedralGroup.sr k) v)
        (h.smul (DihedralGroup.sr k) w)
    exact h.smul_adj (DihedralGroup.sr k) v w
  · intro v
    constructor
    · intro hv
      have hv_mem : v ∈ fixedFinset σ := by
        simpa [mem_fixedFinset] using hv
      have hv_insert : v ∈ insert (c : V) leaves := by
        rwa [hinsert_eq_fixed]
      simpa [Finset.mem_insert] using hv_insert
    · intro hv
      have hv_insert : v ∈ insert (c : V) leaves := by
        simpa [Finset.mem_insert] using hv
      have hv_mem : v ∈ fixedFinset σ := by
        simpa [hinsert_eq_fixed] using hv_insert
      simpa [mem_fixedFinset] using hv_mem
  · intro l hl
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp hl).1
  · intro l₁ hl₁ l₂ hl₂ hAdj
    have hcenter_l₁ : Γ.Adj (c : V) l₁ :=
      by simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp hl₁).1
    have hcenter_l₂ : Γ.Adj (c : V) l₂ :=
      by simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp hl₂).1
    exact h.isMoore.no_triangle hAdj hcenter_l₂.symm hcenter_l₁

/-- Prop-valued wrapper around
`involutionK155OfReflectionFixedNeighborCenterCount`. -/
theorem nonempty_involutionK155_of_reflectionFixedNeighbor_center_count
    (k : ZMod 19)
    (c : reflectionFixedVertex h k)
    (hc :
      (reflectionFixedNeighborFinset h k (c : V)).card = 55)
    (hfix :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  ⟨h.involutionK155OfReflectionFixedNeighborCenterCount k c hc hfix⟩

end D19ActsOnMoore57

/-- Constructive, Type-valued center data: for each reflection, an explicit
fixed center with exactly `55` fixed neighbors.  Unlike
`ReflectionFixedNeighborStarCounts`, this can be eliminated to construct
`InvolutionK155` witnesses. -/
structure ReflectionFixedNeighborStarCenterData
    (h : D19ActsOnMoore57 V Γ) where
  center : ∀ k : ZMod 19, reflectionFixedVertex h k
  center_count :
    ∀ k : ZMod 19,
      (reflectionFixedNeighborFinset h k (center k : V)).card = 55

namespace ReflectionFixedNeighborStarCenterData

variable {h : D19ActsOnMoore57 V Γ}

/-- Construct explicit per-reflection `K_{1,55}` witnesses from constructive
fixed-neighbor center data and the reflection fixed-count `56`. -/
def toInvolutionK155
    (input : ReflectionFixedNeighborStarCenterData h)
    (hfix : ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    ∀ k : ZMod 19, InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k)) := by
  intro k
  exact h.involutionK155OfReflectionFixedNeighborCenterCount
    k (input.center k) (input.center_count k) (hfix k)

end ReflectionFixedNeighborStarCenterData

/-- Constructive, Type-valued induced-degree center data: for each reflection,
an explicit fixed center of degree `55` in the induced fixed graph. -/
structure ReflectionFixedInducedStarCenterData
    (h : D19ActsOnMoore57 V Γ) where
  center : ∀ k : ZMod 19, reflectionFixedVertex h k
  center_degree :
    ∀ k : ZMod 19,
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree (center k) = 55

namespace ReflectionFixedInducedStarCenterData

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert constructive induced-degree center data to constructive
fixed-neighbor center data. -/
def toReflectionFixedNeighborStarCenterData
    (input : ReflectionFixedInducedStarCenterData h) :
    ReflectionFixedNeighborStarCenterData h where
  center := input.center
  center_count := by
    intro k
    have hdegree :=
      h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
        (DihedralGroup.sr k) (input.center k)
    simpa [reflectionFixedNeighborFinset] using
      hdegree.symm.trans (input.center_degree k)

/-- Construct explicit per-reflection `K_{1,55}` witnesses from constructive
induced-degree center data and the reflection fixed-count `56`. -/
def toInvolutionK155
    (input : ReflectionFixedInducedStarCenterData h)
    (hfix : ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    ∀ k : ZMod 19, InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  input.toReflectionFixedNeighborStarCenterData.toInvolutionK155 hfix

end ReflectionFixedInducedStarCenterData

namespace ReflectionFixedNeighborStarCenterData

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructive fixed-neighbor center data gives the fixed-center-leaf boundary
once the reflection fixed-count is `56` and the selected star center is known
not to be `rotationFixedCenter`. -/
def toReflectionFixedCenterLeafBoundary
    (input : ReflectionFixedNeighborStarCenterData h)
    (hfix : ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56)
    (hcenter_ne : ∀ k : ZMod 19,
      h.rotationFixedCenter ≠ (input.center k : V)) :
    ReflectionFixedCenterLeafBoundary h :=
  h.reflectionFixedCenterLeafBoundary_of_involutionK155
    (input.toInvolutionK155 hfix)
    (by
      intro k
      simpa using hcenter_ne k)

end ReflectionFixedNeighborStarCenterData

namespace ReflectionFixedInducedStarCenterData

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructive induced-degree center data gives the fixed-center-leaf boundary
under the same fixed-count and center-separation hypotheses. -/
def toReflectionFixedCenterLeafBoundary
    (input : ReflectionFixedInducedStarCenterData h)
    (hfix : ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56)
    (hcenter_ne : ∀ k : ZMod 19,
      h.rotationFixedCenter ≠ (input.center k : V)) :
    ReflectionFixedCenterLeafBoundary h :=
  input.toReflectionFixedNeighborStarCenterData.toReflectionFixedCenterLeafBoundary
    hfix hcenter_ne

end ReflectionFixedInducedStarCenterData

namespace ReflectionFixedNeighborStarCounts

variable {h : D19ActsOnMoore57 V Γ}

/-- Fixed-neighbor star counts plus the reflection fixed-count `56` give
nonempty per-reflection explicit `K_{1,55}` witnesses.  The result is
Prop-valued because `ReflectionFixedNeighborStarCounts` itself is Prop-valued. -/
theorem nonempty_involutionK155
    (input : ReflectionFixedNeighborStarCounts h)
    (hfix : ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    ∀ k : ZMod 19,
      Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) := by
  intro k
  rcases input.exists_center_count k with ⟨c, hc, _⟩
  exact h.nonempty_involutionK155_of_reflectionFixedNeighbor_center_count
    k c hc (hfix k)

end ReflectionFixedNeighborStarCounts

namespace ReflectionFixedInducedStarDegrees

variable {h : D19ActsOnMoore57 V Γ}

/-- Induced fixed-graph star degrees plus the reflection fixed-count `56` give
nonempty per-reflection explicit `K_{1,55}` witnesses.  The result is
Prop-valued because `ReflectionFixedInducedStarDegrees` itself is Prop-valued. -/
theorem nonempty_involutionK155
    (input : ReflectionFixedInducedStarDegrees h)
    (hfix : ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    ∀ k : ZMod 19,
      Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) := by
  intro k
  rcases input.exists_center_degree k with ⟨c, hc, _⟩
  have hdegree :=
    h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
      (DihedralGroup.sr k) c
  have hcount :
      (reflectionFixedNeighborFinset h k (c : V)).card = 55 := by
    simpa [reflectionFixedNeighborFinset] using hdegree.symm.trans hc
  exact h.nonempty_involutionK155_of_reflectionFixedNeighbor_center_count
    k c hcount (hfix k)

end ReflectionFixedInducedStarDegrees

namespace ReflectionFixedStarBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The fixed-star boundary, when paired with the exact reflection fixed-count
`56`, yields nonempty per-reflection explicit `K_{1,55}` witnesses.  The
result is Prop-valued because `ReflectionFixedStarBoundary` itself is
Prop-valued. -/
theorem nonempty_involutionK155
    (boundary : ReflectionFixedStarBoundary h)
    (hfix : ∀ k : ZMod 19,
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56) :
    ∀ k : ZMod 19,
      Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) := by
  intro k
  rcases boundary.exists_center k with ⟨c, hc⟩
  have hdegree :=
    h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
      (DihedralGroup.sr k) c
  have hcount :
      (reflectionFixedNeighborFinset h k (c : V)).card = 55 := by
    simpa [reflectionFixedNeighborFinset, IsReflectionFixedStarCenter] using
      hdegree.symm.trans hc.1
  exact h.nonempty_involutionK155_of_reflectionFixedNeighbor_center_count
    k c hcount (hfix k)

end ReflectionFixedStarBoundary

end

end Moore57
