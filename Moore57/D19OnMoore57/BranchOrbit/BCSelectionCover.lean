import Moore57.D19OnMoore57.BranchOrbit.ABCFromCenter
import Moore57.D19OnMoore57.AdjacentMoved.Reflection

set_option maxRecDepth 10000

/-!
# B/C-side coverage from a selected `L_{b0}` base

This file records the finite-set coverage supplied by choosing the `56` points
of `L_{b0} = branchFiber Γ u b0` as orbit representatives.  The original
rotation copies cover the whole B-side leaf.  If a chosen reflection sends
`b0` to `c0`, the reflected copy covers the C-side leaf.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- The union of all branch fibers over the rotation orbit of one branch. -/
noncomputable def branchOrbitLeaf (u b : V) : Finset V :=
  (Finset.univ : Finset (ZMod 19)).biUnion fun i =>
    branchFiber Γ u (h.rotation i b)

@[simp] theorem mem_branchOrbitLeaf_iff (u b y : V) :
    y ∈ h.branchOrbitLeaf u b ↔
      ∃ i : ZMod 19, y ∈ branchFiber Γ u (h.rotation i b) := by
  simp [branchOrbitLeaf]

/-- Applying a rotation and then its inverse rotation returns the vertex. -/
theorem rotation_neg_apply_rotation (i : ZMod 19) (x : V) :
    h.rotation (-i) (h.rotation i x) = x := by
  calc
    h.rotation (-i) (h.rotation i x) =
        (h.rotation (-i) * h.rotation i) x := by
          simp [Equiv.Perm.mul_apply]
    _ = h.rotation ((-i) + i) x := by
          rw [← h.rotation_add]
    _ = x := by
          simp

/-- Applying the inverse rotation and then the rotation returns the vertex. -/
theorem rotation_apply_neg_rotation (i : ZMod 19) (x : V) :
    h.rotation i (h.rotation (-i) x) = x := by
  calc
    h.rotation i (h.rotation (-i) x) =
        (h.rotation i * h.rotation (-i)) x := by
          simp [Equiv.Perm.mul_apply]
    _ = h.rotation (i + (-i)) x := by
          rw [← h.rotation_add]
    _ = x := by
          simp

/-- A reflection of the form `sr k` is an involution on vertices. -/
theorem reflection_smul_reflection_smul (k : ZMod 19) (x : V) :
    h.smul (DihedralGroup.sr k) (h.smul (DihedralGroup.sr k) x) = x := by
  calc
    h.smul (DihedralGroup.sr k) (h.smul (DihedralGroup.sr k) x) =
        h.smul (DihedralGroup.sr k * DihedralGroup.sr k) x := by
          rw [← h.mul_smul]
    _ = h.smul 1 x := by
          rw [DihedralGroup.sr_mul_self]
    _ = x := h.one_smul x

/-- A fiber-surjective selection of one branch fiber has rotation-orbit union
exactly the full branch leaf over the rotation orbit of that branch. -/
theorem orbitFamilyUnion_eq_branchOrbitLeaf_of_base_fiber_surjective
    {u b : V} (hu : ∀ d : ZMod 19, h.rotation d u = u)
    (base : Fin 56 → V)
    (hmem : ∀ q : Fin 56, base q ∈ branchFiber Γ u b)
    (hsurj :
      ∀ x : V, x ∈ branchFiber Γ u b → ∃ q : Fin 56, base q = x) :
    h.orbitFamilyUnion base = h.branchOrbitLeaf u b := by
  ext y
  constructor
  · intro hy
    rcases (h.mem_orbitFamilyUnion base y).mp hy with ⟨q, i, hi⟩
    rw [← hi]
    rw [h.mem_branchOrbitLeaf_iff]
    exact ⟨i, (h.rotation_mem_branchFiber_iff i
      (u := u) (b := b) (x := base q) (hu i)).2 (hmem q)⟩
  · intro hy
    rw [h.mem_branchOrbitLeaf_iff] at hy
    rcases hy with ⟨i, hyi⟩
    have hpre :
        h.rotation (-i) y ∈ branchFiber Γ u b := by
      have hpre' :
          h.rotation (-i) y ∈
            branchFiber Γ u (h.rotation (-i) (h.rotation i b)) :=
        (h.rotation_mem_branchFiber_iff (-i)
          (u := u) (b := h.rotation i b) (x := y) (hu (-i))).2 hyi
      simpa [h.rotation_neg_apply_rotation i b] using hpre'
    rcases hsurj (h.rotation (-i) y) hpre with ⟨q, hq⟩
    exact (h.mem_orbitFamilyUnion base y).mpr
      ⟨q, i, by
        rw [hq]
        exact h.rotation_apply_neg_rotation i y⟩

end D19ActsOnMoore57

namespace BranchOrbitABCFromCenter

variable {h : D19ActsOnMoore57 V Γ}

/-- The B-side leaf over the rotation orbit of `b0`. -/
noncomputable abbrev bSideLeaf (data : BranchOrbitABCFromCenter h) :
    Finset V :=
  h.branchOrbitLeaf data.u data.b0

/-- The C-side leaf over the rotation orbit of `c0`. -/
noncomputable abbrev cSideLeaf (data : BranchOrbitABCFromCenter h) :
    Finset V :=
  h.branchOrbitLeaf data.u data.c0

/-- Select the `56` points of the base B-fiber as orbit representatives. -/
noncomputable def b0FiberBase
    (data : BranchOrbitABCFromCenter h)
    (e : Fin 56 ≃ {x : V // x ∈ branchFiber Γ data.u data.b0}) :
    Fin 56 → V :=
  fun q => ((e q : {x : V // x ∈ branchFiber Γ data.u data.b0}) : V)

@[simp] theorem b0FiberBase_mem
    (data : BranchOrbitABCFromCenter h)
    (e : Fin 56 ≃ {x : V // x ∈ branchFiber Γ data.u data.b0})
    (q : Fin 56) :
    data.b0FiberBase e q ∈ branchFiber Γ data.u data.b0 :=
  (e q).property

/-- The selected `L_{b0}` base enumerates every point of the base B-fiber. -/
theorem b0FiberBase_surjective
    (data : BranchOrbitABCFromCenter h)
    (e : Fin 56 ≃ {x : V // x ∈ branchFiber Γ data.u data.b0}) :
    ∀ x : V, x ∈ branchFiber Γ data.u data.b0 →
      ∃ q : Fin 56, data.b0FiberBase e q = x := by
  intro x hx
  let p : {x : V // x ∈ branchFiber Γ data.u data.b0} := ⟨x, hx⟩
  refine ⟨e.symm p, ?_⟩
  change ((e (e.symm p) :
    {x : V // x ∈ branchFiber Γ data.u data.b0}) : V) = x
  simp [p]

/-- The selected `L_{b0}` base covers the full B-side leaf under rotations. -/
theorem orbitFamilyUnion_b0FiberBase_eq_bSideLeaf
    (data : BranchOrbitABCFromCenter h)
    (e : Fin 56 ≃ {x : V // x ∈ branchFiber Γ data.u data.b0}) :
    h.orbitFamilyUnion (data.b0FiberBase e) = data.bSideLeaf := by
  exact h.orbitFamilyUnion_eq_branchOrbitLeaf_of_base_fiber_surjective
    data.u_fixed (data.b0FiberBase e)
    (data.b0FiberBase_mem e)
    (data.b0FiberBase_surjective e)

/-- If `sr k` sends `b0` to `c0`, then applying `sr k` again sends `c0`
back to `b0`. -/
theorem reflection_smul_c0_eq_b0_of_reflection_smul_b0_eq_c0
    (data : BranchOrbitABCFromCenter h) {k : ZMod 19}
    (href : h.smul (DihedralGroup.sr k) data.b0 = data.c0) :
    h.smul (DihedralGroup.sr k) data.c0 = data.b0 := by
  rw [← href]
  exact h.reflection_smul_reflection_smul k data.b0

/-- Every reflected selected base point lies in `L_{c0}` when the reflection
sends `b0` to `c0`. -/
theorem reflection_b0FiberBase_mem_c0Fiber
    (data : BranchOrbitABCFromCenter h)
    (e : Fin 56 ≃ {x : V // x ∈ branchFiber Γ data.u data.b0})
    {k : ZMod 19}
    (href : h.smul (DihedralGroup.sr k) data.b0 = data.c0)
    (q : Fin 56) :
    h.smul (DihedralGroup.sr k) (data.b0FiberBase e q) ∈
      branchFiber Γ data.u data.c0 := by
  have hu :
      h.smul (DihedralGroup.sr k) data.u = data.u := by
    rw [data.u_eq_rotationFixedCenter]
    exact h.reflection_smul_rotationFixedCenter k
  have hmem :
      h.smul (DihedralGroup.sr k) (data.b0FiberBase e q) ∈
        branchFiber Γ data.u (h.smul (DihedralGroup.sr k) data.b0) :=
    (h.smul_mem_branchFiber_iff (DihedralGroup.sr k)
      (u := data.u) (b := data.b0) (x := data.b0FiberBase e q) hu).2
      (data.b0FiberBase_mem e q)
  simpa [href] using hmem

/-- The reflected `L_{b0}` base enumerates every point of `L_{c0}` when the
reflection sends `b0` to `c0`. -/
theorem reflection_b0FiberBase_surjective_c0Fiber
    (data : BranchOrbitABCFromCenter h)
    (e : Fin 56 ≃ {x : V // x ∈ branchFiber Γ data.u data.b0})
    {k : ZMod 19}
    (href : h.smul (DihedralGroup.sr k) data.b0 = data.c0) :
    ∀ x : V, x ∈ branchFiber Γ data.u data.c0 →
      ∃ q : Fin 56,
        h.smul (DihedralGroup.sr k) (data.b0FiberBase e q) = x := by
  intro x hx
  have hu :
      h.smul (DihedralGroup.sr k) data.u = data.u := by
    rw [data.u_eq_rotationFixedCenter]
    exact h.reflection_smul_rotationFixedCenter k
  have href_symm :
      h.smul (DihedralGroup.sr k) data.c0 = data.b0 :=
    data.reflection_smul_c0_eq_b0_of_reflection_smul_b0_eq_c0 href
  have hxpre :
      h.smul (DihedralGroup.sr k) x ∈ branchFiber Γ data.u data.b0 := by
    have hxpre' :
        h.smul (DihedralGroup.sr k) x ∈
          branchFiber Γ data.u (h.smul (DihedralGroup.sr k) data.c0) :=
      (h.smul_mem_branchFiber_iff (DihedralGroup.sr k)
        (u := data.u) (b := data.c0) (x := x) hu).2 hx
    simpa [href_symm] using hxpre'
  rcases data.b0FiberBase_surjective e
      (h.smul (DihedralGroup.sr k) x) hxpre with
    ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [hq]
  exact h.reflection_smul_reflection_smul k x

/-- If `sr k` sends `b0` to `c0`, then the reflected copy of the selected
`L_{b0}` orbit family covers the full C-side leaf. -/
theorem reflectionOrbitFamilyUnion_b0FiberBase_eq_cSideLeaf
    (data : BranchOrbitABCFromCenter h)
    (e : Fin 56 ≃ {x : V // x ∈ branchFiber Γ data.u data.b0})
    {k : ZMod 19}
    (href : h.smul (DihedralGroup.sr k) data.b0 = data.c0) :
    h.reflectionOrbitFamilyUnion (data.b0FiberBase e) k = data.cSideLeaf := by
  simpa [D19ActsOnMoore57.reflectionOrbitFamilyUnion] using
    h.orbitFamilyUnion_eq_branchOrbitLeaf_of_base_fiber_surjective
      data.u_fixed
      (fun q : Fin 56 =>
        h.smul (DihedralGroup.sr k) (data.b0FiberBase e q))
      (fun q => data.reflection_b0FiberBase_mem_c0Fiber e href q)
      (data.reflection_b0FiberBase_surjective_c0Fiber e href)

/-- Original rotations from `L_{b0}` plus their `sr k` reflection copy cover
exactly the B- and C-side leaves, provided `sr k` sends `b0` to `c0`. -/
theorem reflectionCopyUnion_b0FiberBase_eq_bSideLeaf_union_cSideLeaf
    (data : BranchOrbitABCFromCenter h)
    (e : Fin 56 ≃ {x : V // x ∈ branchFiber Γ data.u data.b0})
    {k : ZMod 19}
    (href : h.smul (DihedralGroup.sr k) data.b0 = data.c0) :
    reflectionCopyUnion h (data.b0FiberBase e) k =
      data.bSideLeaf ∪ data.cSideLeaf := by
  ext y
  rw [h.mem_reflectionCopyUnion_iff_orbitFamilyUnion_or_reflectionOrbitFamilyUnion,
    data.orbitFamilyUnion_b0FiberBase_eq_bSideLeaf e,
    data.reflectionOrbitFamilyUnion_b0FiberBase_eq_cSideLeaf e href,
    Finset.mem_union]

end BranchOrbitABCFromCenter

end

end Moore57
