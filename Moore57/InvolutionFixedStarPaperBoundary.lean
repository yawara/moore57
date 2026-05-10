import Moore57.InvolutionFixedStarA1

/-!
# Paper-shaped involution fixed-star boundary

The paper formulation says that the fixed set of an involution is a star with
`56` vertices.  This file records that statement in a Prop-valued form and
connects it to the existing explicit `InvolutionK155` data used downstream.
-/

namespace Moore57

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The fixed set of `σ` is a star centered at `c`, stated directly in terms
of fixed vertices. -/
structure FixedSetStarWithCenter
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (σ : Equiv.Perm V) (c : V) : Prop where
  center_fixed : σ c = c
  center_adj_fixed :
    ∀ v : V, σ v = v → v ≠ c → Γ.Adj c v
  fixed_noncenter_not_adj :
    ∀ v : V, σ v = v → v ≠ c →
      ∀ w : V, σ w = w → w ≠ c → ¬ Γ.Adj v w

/-- Paper-shaped fixed-star input for an involution: the automorphism is an
involution and graph automorphism, and its fixed set is a `56`-vertex star. -/
structure InvolutionFixedSetStar56
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (σ : Equiv.Perm V) : Prop where
  involutive : Function.Involutive σ
  automorphism : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)
  fixed_card : (fixedFinset σ).card = 56
  exists_center : ∃ c : V, FixedSetStarWithCenter Γ σ c

namespace InvolutionFixedSetStar56

variable {σ : Equiv.Perm V}

/-- The paper-shaped fixed-star input includes the exact fixed-point count in
the `fixedVertexCount` normalization used by the D19 trace pipeline. -/
theorem fixedVertexCount_eq_56
    (hStar : InvolutionFixedSetStar56 Γ σ) :
    fixedVertexCount σ = 56 := by
  simpa using hStar.fixed_card

/-- The paper-shaped fixed-star input yields a nonempty explicit `K_{1,55}`
witness.  The result is Prop-valued, so it can eliminate Prop-level paper
statements without requiring constructive center data. -/
theorem nonempty_involutionK155
    (hStar : InvolutionFixedSetStar56 Γ σ) :
    Nonempty (InvolutionK155 Γ σ) := by
  classical
  rcases hStar.exists_center with ⟨c, hc⟩
  let leaves : Finset V := (fixedFinset σ).erase c
  have hc_mem : c ∈ fixedFinset σ := by
    simpa [mem_fixedFinset] using hc.center_fixed
  have hcenter_notMem : c ∉ leaves := by
    simp [leaves]
  have hleaves_card : leaves.card = 55 := by
    rw [show leaves.card = (fixedFinset σ).card - 1 by
      exact Finset.card_erase_of_mem hc_mem]
    rw [hStar.fixed_card]
  refine
    ⟨{ involutive := hStar.involutive
       automorphism := hStar.automorphism
       center := c
       leaves := leaves
       center_notMem := hcenter_notMem
       leaves_card := hleaves_card
       fixed_iff := ?_
       center_adj_leaves := ?_
       leaves_pairwise_not_adj := ?_ }⟩
  · intro v
    constructor
    · intro hv
      by_cases hvc : v = c
      · exact Or.inl hvc
      · exact Or.inr (by simp [leaves, mem_fixedFinset, hv, hvc])
    · rintro (rfl | hv)
      · exact hc.center_fixed
      · exact (by
          have hv_fixed : v ∈ fixedFinset σ := by
            exact Finset.mem_of_mem_erase hv
          simpa [mem_fixedFinset] using hv_fixed)
  · intro l hl
    have hl_fixed : σ l = l := by
      have : l ∈ fixedFinset σ := Finset.mem_of_mem_erase hl
      simpa [mem_fixedFinset] using this
    have hl_ne : l ≠ c := by
      exact (Finset.mem_erase.mp hl).1
    exact hc.center_adj_fixed l hl_fixed hl_ne
  · intro l₁ hl₁ l₂ hl₂
    have hl₁_fixed : σ l₁ = l₁ := by
      have : l₁ ∈ fixedFinset σ := Finset.mem_of_mem_erase hl₁
      simpa [mem_fixedFinset] using this
    have hl₂_fixed : σ l₂ = l₂ := by
      have : l₂ ∈ fixedFinset σ := Finset.mem_of_mem_erase hl₂
      simpa [mem_fixedFinset] using this
    have hl₁_ne : l₁ ≠ c := (Finset.mem_erase.mp hl₁).1
    have hl₂_ne : l₂ ≠ c := (Finset.mem_erase.mp hl₂).1
    exact hc.fixed_noncenter_not_adj l₁ hl₁_fixed hl₁_ne l₂ hl₂_fixed hl₂_ne

/-- A paper-shaped fixed-star input also yields the weaker fixed-star count
abstraction used by the representation-count pipeline. -/
theorem nonempty_involutionFixedStar55
    (hΓ : IsMoore57 Γ)
    (hStar : InvolutionFixedSetStar56 Γ σ) :
    Nonempty (InvolutionFixedStar55 Γ σ) := by
  rcases hStar.nonempty_involutionK155 with ⟨hK⟩
  exact ⟨hK.toInvolutionFixedStar55 hΓ⟩

/-- The paper-shaped fixed-star input gives the standard adjacent-moved count
for the involution. -/
theorem adjacentMovedCount_eq_112
    (hΓ : IsMoore57 Γ)
    (hStar : InvolutionFixedSetStar56 Γ σ) :
    adjacentMovedCount Γ σ = 112 := by
  rcases hStar.nonempty_involutionFixedStar55 hΓ with ⟨hFixedStar⟩
  exact hFixedStar.adjacentMovedCount_eq_112 hΓ

end InvolutionFixedSetStar56

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Reflection-specialized bridge from the paper-shaped fixed-star statement to
the explicit `K_{1,55}` witness used in the current Lean pipeline. -/
theorem nonempty_involutionK155_of_reflectionFixedSetStar56
    {k : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k))) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  hStar.nonempty_involutionK155

/-- Reflection-specialized fixed-point count extracted from the paper-shaped
fixed-star statement. -/
theorem fixedVertexCount_reflection_eq_56_of_reflectionFixedSetStar56
    {k : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k))) :
    fixedVertexCount (h.smulEquiv (DihedralGroup.sr k)) = 56 :=
  hStar.fixedVertexCount_eq_56

/-- Reflection-specialized adjacent-moved count extracted from the paper-shaped
fixed-star statement. -/
theorem adjacentMovedCount_reflection_eq_112_of_reflectionFixedSetStar56
    {k : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k))) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 112 :=
  hStar.adjacentMovedCount_eq_112 h.isMoore

/-- Reflection-specialized bridge from the paper-shaped fixed-star statement to
the fixed-star count abstraction. -/
theorem nonempty_involutionFixedStar55_of_reflectionFixedSetStar56
    {k : ZMod 19}
    (hStar :
      InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k))) :
    Nonempty (InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  hStar.nonempty_involutionFixedStar55 h.isMoore

end D19ActsOnMoore57

end Moore57
