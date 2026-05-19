import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Lemma 20

> Let `O` be an orbit of an action of a group `X` on a set and let `X_o` be
> a stabilizer of an element `o ∈ O`. Let `Conj(X_o)` be the number of
> conjugates of `X_o` in `X`. Then
> ```
> |Fix(X_o) ∩ O| · Conj(X_o) = |O|.
> ```

This is a general orbit-stabilizer / conjugate counting fact, not specific
to Γ.

## Lean formalization

We use the standard correspondences in Mathlib:

* `|Fix(X_o) ∩ O| = [N_G(X_o) : X_o]` — proven below as
  `ncard_fixedPoints_inter_orbit_eq_relIndex_normalizer` (for finite `G`).
  The proof goes by showing the set equality
  `Fix(stab o) ∩ orbit G o = orbit (N_G(stab o)) o` and then applying
  the orbit-stabilizer theorem to the `N_G(stab o)`-action.
* `Conj(X_o) = [G : N_G(X_o)]` — not formalized here yet; corresponds to
  the orbit-stabilizer theorem for the conjugation action of `G` on
  subgroups (`MulAut.conj` action).  Layer-5 downstream consumers use
  the index form `(N stab).index` directly, so this bridge is currently
  optional.
* `|O| = [G : X_o]` — `MulAction.index_stabilizer`.

The identity then reduces to the tower formula
`[N_G(X_o) : X_o] · [G : N_G(X_o)] = [G : X_o]`, which is
`Subgroup.relIndex_mul_index` applied to `X_o ≤ N_G(X_o)`.
-/

namespace Moore57.Papers.MacajSiran2010.S6

open MulAction Subgroup

variable {G : Type*} [Group G]

/-- **Lemma 20** in its abstract index form: for any subgroup `H` of `G`,
`[N_G(H) : H] · [G : N_G(H)] = [G : H]`.  This is the algebraic core
behind the orbit-conjugate counting identity. -/
theorem lem20_index_form (H : Subgroup G) :
    H.relIndex (normalizer (H : Set G)) * (normalizer (H : Set G)).index = H.index :=
  Subgroup.relIndex_mul_index Subgroup.le_normalizer

/-- **Lemma 20** in its index form for actions: for any `MulAction G α` and
`o : α`, `[N_G(stab o) : stab o] · [G : N_G(stab o)] = |orbit G o|`. -/
theorem lem20_fix_conjugate {α : Type*} [MulAction G α] (o : α) :
    (stabilizer G o).relIndex (normalizer (stabilizer G o : Set G)) *
        (normalizer (stabilizer G o : Set G)).index = (orbit G o).ncard := by
  rw [← MulAction.index_stabilizer]
  exact lem20_index_form (stabilizer G o)

/-! ### Geometric bridge `|Fix(stab) ∩ orbit| = [N(stab) : stab]`

We prove `Fix(stab o) ∩ orbit G o = orbit (N_G(stab o)) o` as sets and
deduce the cardinality identity. -/

section GeometricBridge

variable {α : Type*} [MulAction G α]

/-- If `n` normalises `stabilizer G o` and `h` fixes `o`, then `h` fixes
`n • o`.  The half of the set equality that does not require finiteness. -/
private lemma smul_normalizer_mem_fixedPoints
    (o : α) {n : G} (hn : n ∈ normalizer (stabilizer G o : Set G))
    {h : G} (hh : h ∈ stabilizer G o) :
    h • (n • o) = n • o := by
  have hconj : n⁻¹ * h * n ∈ stabilizer G o := by
    rw [mem_normalizer_iff''] at hn
    exact (hn h).mp hh
  have hfix : (n⁻¹ * h * n) • o = o := hconj
  calc h • (n • o)
      = (h * n) • o := (mul_smul _ _ _).symm
    _ = (n * (n⁻¹ * h * n)) • o := by
      rw [show h * n = n * (n⁻¹ * h * n) from by simp [mul_assoc]]
    _ = n • ((n⁻¹ * h * n) • o) := mul_smul _ _ _
    _ = n • o := by rw [hfix]

/-- `(N_G(stab o))-orbit of o ⊆ Fix(stab o) ∩ orbit G o`.  No finiteness needed. -/
theorem orbit_normalizer_subset_fixedPoints_inter_orbit (o : α) :
    orbit (normalizer (stabilizer G o : Set G)) o ⊆
      fixedPoints (stabilizer G o) α ∩ orbit G o := by
  rintro y ⟨⟨n, hn⟩, rfl⟩
  refine ⟨?_, mem_orbit_of_mem_orbit_subgroup ⟨⟨n, hn⟩, rfl⟩⟩
  intro h
  exact smul_normalizer_mem_fixedPoints o hn h.2

/-- The reverse inclusion: a point in `orbit G o` fixed by `stab o` is in
the `N(stab o)`-orbit of `o`.  Requires finiteness so that
`stab o ⊆ stab (g • o)` implies `stab o = stab (g • o)`. -/
theorem fixedPoints_inter_orbit_subset_orbit_normalizer
    (o : α) [Finite (stabilizer G o : Set G)] :
    fixedPoints (stabilizer G o) α ∩ orbit G o ⊆
      orbit (normalizer (stabilizer G o : Set G)) o := by
  rintro y ⟨hfix, g, rfl⟩
  refine ⟨⟨g, ?_⟩, rfl⟩
  -- show g ∈ normalizer (stabilizer G o : Set G)
  -- via: stabilizer G o ≤ stabilizer G (g • o) and same finite cardinality
  rw [mem_normalizer_iff'']
  intro h
  constructor
  · intro hh
    -- h ∈ stab(o) → g⁻¹ h g ∈ stab(o)
    have : h • (g • o) = g • o := hfix ⟨h, hh⟩
    -- h • (g • o) = g • o ⟺ (g⁻¹ h g) • o = o
    have : (g⁻¹ * h * g) • o = o := by
      have step1 : (h * g) • o = g • o := by
        rw [mul_smul]; exact this
      have step2 : (g⁻¹ * (h * g)) • o = g⁻¹ • (g • o) := by
        simpa [mul_smul] using congrArg (fun z => g⁻¹ • z) step1
      rw [show g⁻¹ * h * g = g⁻¹ * (h * g) from by simp [mul_assoc], step2,
          ← mul_smul, inv_mul_cancel, one_smul]
    exact this
  · intro hh
    -- g⁻¹ h g ∈ stab(o) → h ∈ stab(o)
    -- Use cardinality argument: stab(o) ≤ "conjugate by g of stab(o)" = stab(g • o)
    -- and both have same finite cardinality, so equal.
    -- Alternative direct route: stab(o) is also a subgroup of size = card
    -- preserved by conjugation. We exhibit a bijection of stab(o) onto itself
    -- via h ↦ g⁻¹ h g (well-defined since the image is in stab(o) by the first
    -- direction). Injectivity is automatic. Surjectivity uses finite stab.
    have key : ∀ k : G, k ∈ stabilizer G o → g⁻¹ * k * g ∈ stabilizer G o := by
      intro k hk
      have : k • (g • o) = g • o := hfix ⟨k, hk⟩
      have : (g⁻¹ * k * g) • o = o := by
        have step1 : (k * g) • o = g • o := by rw [mul_smul]; exact this
        have step2 : (g⁻¹ * (k * g)) • o = g⁻¹ • (g • o) := by
          simpa [mul_smul] using congrArg (fun z => g⁻¹ • z) step1
        rw [show g⁻¹ * k * g = g⁻¹ * (k * g) from by simp [mul_assoc], step2,
            ← mul_smul, inv_mul_cancel, one_smul]
      exact this
    -- Define φ : stab(o) → stab(o) by φ(k) = g⁻¹ k g.
    let φ : stabilizer G o → stabilizer G o :=
      fun k => ⟨g⁻¹ * k.1 * g, key k.1 k.2⟩
    -- φ is injective (conjugation is injective in G).
    have hφ_inj : Function.Injective φ := by
      intro a b hab
      have : g⁻¹ * a.1 * g = g⁻¹ * b.1 * g := congrArg Subtype.val hab
      have : a.1 = b.1 := by
        have hcancel := congrArg (fun x => g * x * g⁻¹) this
        have hsub : a = b := by
          simpa [mul_assoc] using hcancel
        exact congrArg Subtype.val hsub
      exact Subtype.ext this
    -- Since stab(o) is finite, φ is bijective.
    have hφ_surj : Function.Surjective φ :=
      Finite.injective_iff_surjective.mp hφ_inj
    -- So h = φ(k) for some k, meaning h = g⁻¹ k g.
    -- We have h.1 = g⁻¹ * k.1 * g with k.1 ∈ stab(o).
    -- Equivalently, g * h.1 * g⁻¹ = k.1 ∈ stab(o), i.e., g h g⁻¹ ∈ stab(o).
    -- But we assumed g⁻¹ h g ∈ stab(o), i.e., hh : g⁻¹ * h * g ∈ stabilizer G o.
    -- Let's use hh directly: we have hh : g⁻¹ h g ∈ stab.
    -- Then h = g * (g⁻¹ h g) * g⁻¹.
    -- Surjectivity: exists k ∈ stab, φ(k) = ⟨g⁻¹ h g, hh⟩, i.e., g⁻¹ k g = g⁻¹ h g.
    -- So k = h. So h ∈ stab(o). ✓
    obtain ⟨k, hk⟩ := hφ_surj ⟨g⁻¹ * h * g, hh⟩
    have h_eq_k : h = k.1 := by
      have hconj : g⁻¹ * k.1 * g = g⁻¹ * h * g := by
        simpa [φ] using congrArg Subtype.val hk
      have hcancel := congrArg (fun x => g * x * g⁻¹) hconj
      have hkh : k.1 = h := by
        simpa [mul_assoc] using hcancel
      exact hkh.symm
    rw [h_eq_k]
    exact k.2

/-- **The set equality**: `Fix(stab o) ∩ orbit G o = orbit (N_G(stab o)) o`. -/
theorem fixedPoints_inter_orbit_eq_orbit_normalizer
    (o : α) [Finite (stabilizer G o : Set G)] :
    fixedPoints (stabilizer G o) α ∩ orbit G o =
      orbit (normalizer (stabilizer G o : Set G)) o :=
  le_antisymm (fixedPoints_inter_orbit_subset_orbit_normalizer (G := G) (α := α) o)
    (orbit_normalizer_subset_fixedPoints_inter_orbit (G := G) (α := α) o)

/-- **The cardinality bridge**:
`|Fix(stab o) ∩ orbit G o| = [N_G(stab o) : stab o]`. -/
theorem ncard_fixedPoints_inter_orbit_eq_relIndex_normalizer
    (o : α) [Finite (stabilizer G o : Set G)] :
    (fixedPoints (stabilizer G o) α ∩ orbit G o).ncard =
      (stabilizer G o).relIndex (normalizer (stabilizer G o : Set G)) := by
  rw [fixedPoints_inter_orbit_eq_orbit_normalizer (G := G) (α := α) o]
  rw [← MulAction.index_stabilizer
    (G := normalizer (stabilizer G o : Set G)) (x := o)]
  rw [show stabilizer (normalizer (stabilizer G o : Set G)) o =
      (stabilizer G o).subgroupOf (normalizer (stabilizer G o : Set G)) from by
    ext n
    rfl]
  rfl

end GeometricBridge

end Moore57.Papers.MacajSiran2010.S6
