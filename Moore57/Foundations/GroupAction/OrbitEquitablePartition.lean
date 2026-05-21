import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition
import Moore57.Foundations.GroupAction.SemiRegularOrbit
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# σ-orbit equitable partition

For a permutation `σ : Equiv.Perm V` that is an automorphism of a finite
simple graph `Γ`, the σ-orbits partition `V` into an **equitable partition**
(in the sense of `Moore57.Papers.MacajSiran2010.S3.EquitablePartition`).

This is the structural backbone of paper §8 Prop 3 Step 1-4: the
σ-orbits give the coarsest partition refining Fix(σ) + N(a) cells, and
their Lem 5(5) identity yields the Diophantine constraints
Σ bᵢ = 7, Σ bᵢ² = 31.

## Main definitions

* `Moore57.orbitClass σ` — the quotient of `V` by `MulAction.orbitRel
  (Subgroup.zpowers σ)`. Carries `Fintype` and `DecidableEq` instances
  via classical choice.
* `Moore57.orbitClass.cell σ c` — the σ-orbit corresponding to a class
  `c : orbitClass σ`, as a `Finset V`.
* `Moore57.orbitEquitablePartition Γ σ smul_adj` — the
  `EquitablePartition Γ (orbitClass σ)` derived from σ being a graph
  automorphism.

The equitable property is proved by exhibiting σ as a graph
automorphism: for any v, w in the same orbit, `w = σ^k v` for some `k`,
and `σ^k` permutes both the neighborhoods of v ↔ w and the orbit cells.

Here we take `smul_adj` in **iff form**, matching `HSFixedData` and
`hs_orderOf_dvd_50_of_semiRegular`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The σ-orbit classes: quotient of `V` by `MulAction.orbitRel
(Subgroup.zpowers σ)`. -/
def orbitClass (σ : Equiv.Perm V) : Type _ :=
  Quotient (MulAction.orbitRel (Subgroup.zpowers σ) V)

namespace orbitClass

variable {σ : Equiv.Perm V}

/-- `Quotient.mk` for `orbitClass σ`. -/
def mk (σ : Equiv.Perm V) (v : V) : orbitClass σ :=
  Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) V) v

noncomputable instance fintype (σ : Equiv.Perm V) : Fintype (orbitClass σ) := by
  classical
  unfold orbitClass
  infer_instance

noncomputable instance decidableEq (σ : Equiv.Perm V) : DecidableEq (orbitClass σ) :=
  Classical.decEq _

/-- The cell of an orbit class: the finset of vertices in that orbit. -/
noncomputable def cell (σ : Equiv.Perm V) (c : orbitClass σ) : Finset V :=
  Finset.univ.filter (fun v => mk σ v = c)

@[simp] theorem mem_cell {σ : Equiv.Perm V} {c : orbitClass σ} {v : V} :
    v ∈ cell σ c ↔ mk σ v = c := by
  unfold cell
  simp

theorem mem_cell_self (σ : Equiv.Perm V) (v : V) :
    v ∈ cell σ (mk σ v) := by simp

/-- Distinct cells are disjoint. -/
theorem pairwise_disjoint (σ : Equiv.Perm V) :
    ((Finset.univ : Finset (orbitClass σ)) : Set (orbitClass σ)).PairwiseDisjoint
      (cell σ) := by
  intro c _ c' _ hcc'
  rw [Function.onFun, Finset.disjoint_left]
  intro v hv hv'
  rw [mem_cell] at hv hv'
  exact hcc' (hv.symm.trans hv')

/-- The cells cover `V`. -/
theorem cells_cover (σ : Equiv.Perm V) :
    (Finset.univ : Finset (orbitClass σ)).biUnion (cell σ) = Finset.univ := by
  ext v
  rw [Finset.mem_biUnion]
  refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
  exact ⟨mk σ v, Finset.mem_univ _, mem_cell.mpr rfl⟩

/-- σ-step preserves the orbit class. -/
theorem mk_apply (σ : Equiv.Perm V) (v : V) :
    mk σ (σ v) = mk σ v := by
  unfold mk
  apply Quotient.sound
  -- show σ v ∈ orbit (zpowers σ) v: take g = σ
  refine ⟨⟨σ, Subgroup.mem_zpowers σ⟩, ?_⟩
  rfl

/-- `(σ^k)` (nat power) preserves the orbit class. -/
theorem mk_pow_apply (σ : Equiv.Perm V) (k : ℕ) (v : V) :
    mk σ ((σ^k) v) = mk σ v := by
  induction k with
  | zero => simp
  | succ n ihn =>
      have hstep : (σ^(n+1)) v = σ ((σ^n) v) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [hstep, mk_apply, ihn]

/-- `(σ^k)` (int power) preserves the orbit class. -/
theorem mk_zpow_apply (σ : Equiv.Perm V) (k : ℤ) (v : V) :
    mk σ ((σ^k) v) = mk σ v := by
  unfold mk
  apply Quotient.sound
  refine ⟨⟨σ^k, Subgroup.zpow_mem_zpowers σ k⟩, ?_⟩
  -- (σ^k) • v = (σ^k) v.  We need: (⟨σ^k, _⟩ : zpowers σ) • v = (σ^k) v
  rfl

/-- For `a : V` with `σ a = a`, every nat power of σ fixes a. -/
theorem pow_apply_of_fixed {σ : Equiv.Perm V} {a : V} (ha : σ a = a) (n : ℕ) :
    (σ^n) a = a := by
  induction n with
  | zero => rfl
  | succ m ihm => rw [pow_succ', Equiv.Perm.mul_apply, ihm, ha]

/-- For `a : V` with `σ a = a`, every int power of σ fixes a. -/
theorem zpow_apply_of_fixed {σ : Equiv.Perm V} {a : V} (ha : σ a = a) (k : ℤ) :
    (σ^k) a = a := by
  cases k with
  | ofNat n =>
      have hcast : (σ : Equiv.Perm V)^(Int.ofNat n) = σ^n := by
        change (σ : Equiv.Perm V)^((n : ℕ) : ℤ) = σ^n
        exact zpow_natCast σ n
      rw [hcast]
      exact pow_apply_of_fixed ha n
  | negSucc n =>
      have hzpow : (σ : Equiv.Perm V)^(Int.negSucc n) = (σ^(n+1))⁻¹ := by
        have h1 : (Int.negSucc n : ℤ) = -((n+1 : ℕ) : ℤ) := by
          rw [Int.negSucc_eq]; push_cast; ring
        rw [h1, zpow_neg, zpow_natCast]
      rw [hzpow]
      -- (σ^(n+1))⁻¹ a = a from σ^(n+1) a = a
      have h : (σ^(n+1)) a = a := pow_apply_of_fixed ha (n+1)
      exact ((σ^(n+1) : Equiv.Perm V).symm_apply_eq).mpr h.symm

/-- **Singleton-cell at a fixed vertex**: if `σ a = a`, then
`cell σ (mk σ a) = {a}`.  Used for the 50 fix-singleton orbits in Prop 3. -/
theorem cell_mk_of_fixed [Fintype V] [DecidableEq V] {σ : Equiv.Perm V}
    {a : V} (ha : σ a = a) :
    orbitClass.cell σ (orbitClass.mk σ a) = {a} := by
  ext v
  rw [orbitClass.mem_cell, Finset.mem_singleton]
  constructor
  · -- mk σ v = mk σ a → v = a (since orbit of a is just {a})
    intro hv
    unfold orbitClass.mk at hv
    have : v ∈ MulAction.orbit (Subgroup.zpowers σ) a :=
      Quotient.exact hv
    obtain ⟨g, hg⟩ := this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    have h_smul : (g : Equiv.Perm V) a = v := hg
    rw [← hk] at h_smul
    -- (σ^k) a = a (since σ a = a)
    rw [zpow_apply_of_fixed ha k] at h_smul
    exact h_smul.symm
  · rintro rfl; rfl

/-- **Cell coincides with `cyclicOrbitFinset`**: for any representative
`v`, the orbit class cell equals the standard cyclic orbit Finset. -/
theorem cell_mk_eq_cyclicOrbitFinset [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) (v : V) :
    orbitClass.cell σ (orbitClass.mk σ v) =
      Moore57.cyclicOrbitFinset σ v := by
  ext w
  rw [orbitClass.mem_cell, Moore57.cyclicOrbitFinset.mem_cyclicOrbitFinset]
  constructor
  · -- mk σ w = mk σ v → ∃ k < orderOf σ, σ^k v = w
    intro hwv
    unfold orbitClass.mk at hwv
    have : w ∈ MulAction.orbit (Subgroup.zpowers σ) v := Quotient.exact hwv
    obtain ⟨g, hg⟩ := this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    have h_smul : (g : Equiv.Perm V) v = w := hg
    rw [← hk] at h_smul
    -- σ^k v = w; reduce k mod orderOf σ
    have hpos : 0 < orderOf σ := (isOfFinOrder_of_finite σ).orderOf_pos
    -- For k : ℤ, find m : ℕ with 0 ≤ m < orderOf σ and σ^m v = σ^k v.
    -- Use k = orderOf σ * q + r form, with 0 ≤ r < orderOf σ.
    -- For ℤ this is k.emod (orderOf σ : ℤ).
    set r := (k % (orderOf σ : ℤ)).toNat with hr_def
    have hr_lt : r < orderOf σ := by
      have h1 : k % (orderOf σ : ℤ) < (orderOf σ : ℤ) := by
        apply Int.emod_lt_of_pos
        exact_mod_cast hpos
      have h2 : 0 ≤ k % (orderOf σ : ℤ) := by
        apply Int.emod_nonneg
        omega
      have h3 : (r : ℤ) = k % (orderOf σ : ℤ) := by
        rw [hr_def]; exact (Int.toNat_of_nonneg h2)
      have : (r : ℤ) < (orderOf σ : ℤ) := by rw [h3]; exact h1
      exact_mod_cast this
    refine ⟨r, hr_lt, ?_⟩
    -- (σ^r) v = (σ^k) v
    rw [← h_smul]
    -- σ^r = σ^k via zpow_mod_orderOf.
    have h_emod : (r : ℤ) = k % (orderOf σ : ℤ) := by
      rw [hr_def]
      apply Int.toNat_of_nonneg
      apply Int.emod_nonneg; omega
    have h_zpow_eq : (σ : Equiv.Perm V)^(r : ℤ) = σ^k := by
      rw [h_emod, zpow_mod_orderOf]
    rw [← zpow_natCast, h_zpow_eq]
  · -- ∃ k < orderOf σ, σ^k v = w → mk σ w = mk σ v
    rintro ⟨k, _, hk⟩
    rw [← hk]
    exact orbitClass.mk_pow_apply σ k v

end orbitClass

section EquitablePartitionFromOrbits

variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {σ : Equiv.Perm V}

/-- For an iff-form graph automorphism σ, any integer power σ^k also
preserves adjacency in iff form. -/
theorem adj_iff_of_smul_adj_zpow
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (k : ℤ) (v w : V) :
    Γ.Adj v w ↔ Γ.Adj ((σ^k) v) ((σ^k) w) := by
  -- Nat case: induction.
  have nat_case : ∀ n : ℕ, ∀ v w : V, Γ.Adj v w ↔ Γ.Adj ((σ^n) v) ((σ^n) w) := by
    intro n
    induction n with
    | zero => intro v w; simp
    | succ m ihm =>
        intro v w
        have hl : (σ^(m+1)) v = σ ((σ^m) v) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
        have hr : (σ^(m+1)) w = σ ((σ^m) w) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
        rw [hl, hr]
        exact (ihm v w).trans (smul_adj ((σ^m) v) ((σ^m) w))
  -- Int case: split into ofNat (≥ 0) and negSucc (< 0).
  cases k with
  | ofNat n =>
      change Γ.Adj v w ↔ Γ.Adj ((σ^(Int.ofNat n)) v) ((σ^(Int.ofNat n)) w)
      have hcast : (σ : Equiv.Perm V)^(Int.ofNat n) = σ^n := by
        change (σ : Equiv.Perm V)^((n : ℕ) : ℤ) = σ^n
        exact zpow_natCast σ n
      rw [hcast]
      exact nat_case n v w
  | negSucc n =>
      -- σ^(-[n+1]) = (σ^(n+1))⁻¹.
      have hzpow : (σ : Equiv.Perm V)^(Int.negSucc n) = (σ^(n+1))⁻¹ := by
        have h1 : (Int.negSucc n : ℤ) = -((n+1 : ℕ) : ℤ) := by
          rw [Int.negSucc_eq]; push_cast; ring
        rw [h1, zpow_neg, zpow_natCast]
      rw [hzpow]
      -- Goal: Adj v w ↔ Adj ((σ^(n+1))⁻¹ v) ((σ^(n+1))⁻¹ w).
      -- Apply nat_case (n+1) at v' := (σ^(n+1))⁻¹ v, w' := (σ^(n+1))⁻¹ w,
      -- then use σ^(n+1) (σ^(n+1))⁻¹ = 1 to close.
      set v' := ((σ : Equiv.Perm V)^(n+1))⁻¹ v with hv'_def
      set w' := ((σ : Equiv.Perm V)^(n+1))⁻¹ w with hw'_def
      have hpv : ((σ : Equiv.Perm V)^(n+1)) v' = v := by
        rw [hv'_def, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
      have hpw : ((σ : Equiv.Perm V)^(n+1)) w' = w := by
        rw [hw'_def, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
      have hiff := nat_case (n+1) v' w'
      rw [hpv, hpw] at hiff
      exact hiff.symm

/-- **σ-orbit equitable partition.** If `σ : Equiv.Perm V` is a graph
automorphism of `Γ` (preserves adjacency in iff form), then the σ-orbits
give an equitable partition of `V`. -/
noncomputable def orbitEquitablePartition
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    Moore57.Papers.MacajSiran2010.S3.EquitablePartition Γ (orbitClass σ) where
  cell := orbitClass.cell σ
  pairwise_disjoint := orbitClass.pairwise_disjoint σ
  covers := orbitClass.cells_cover σ
  adjMatrix := fun c c' =>
    ((orbitClass.cell σ c').filter (fun w => Γ.Adj c.out w)).card
  equitable := by
    intro c c' v hv
    rw [orbitClass.mem_cell] at hv
    -- mk σ c.out = c
    have h_out : orbitClass.mk σ c.out = c := by
      change Quotient.mk _ c.out = c
      exact Quotient.out_eq c
    -- c.out and v are in the same orbit; get σ^k v = c.out
    have hequiv : (MulAction.orbitRel (Subgroup.zpowers σ) V).r c.out v := by
      have hmk : orbitClass.mk σ c.out = orbitClass.mk σ v := h_out.trans hv.symm
      exact Quotient.exact hmk
    obtain ⟨g, hg⟩ := hequiv
    have hg' : (g : Equiv.Perm V) v = c.out := hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    have hkv : (σ^k) v = c.out := by
      rw [← hk] at hg'
      exact hg'
    -- f := σ^k is a bijection that maps {w ∈ cell c' | Adj v w} ≃ {w ∈ cell c' | Adj c.out w}.
    refine Finset.card_bij (fun w _ => (σ^k) w) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, orbitClass.mem_cell] at hw ⊢
      obtain ⟨hw_cell, hw_adj⟩ := hw
      refine ⟨?_, ?_⟩
      · -- mk σ ((σ^k) w) = mk σ w = c'
        rw [orbitClass.mk_zpow_apply σ k w]; exact hw_cell
      · -- Γ.Adj ((σ^k) v) ((σ^k) w) ; (σ^k) v = c.out
        have := (adj_iff_of_smul_adj_zpow smul_adj k v w).mp hw_adj
        rwa [hkv] at this
    · intro w₁ _ w₂ _ h
      exact (σ^k).injective h
    · intro w' hw'
      simp only [Finset.mem_filter, orbitClass.mem_cell] at hw'
      obtain ⟨hw'_cell, hw'_adj⟩ := hw'
      refine ⟨(σ^k)⁻¹ w', ?_, ?_⟩
      · simp only [Finset.mem_filter, orbitClass.mem_cell]
        refine ⟨?_, ?_⟩
        · -- mk σ ((σ^k)⁻¹ w') = c'
          have heq : (σ^k)⁻¹ w' = (σ^(-k)) w' := by
            change (σ^k)⁻¹ w' = (σ^(-k)) w'
            rw [zpow_neg]
          rw [heq, orbitClass.mk_zpow_apply σ (-k) w']
          exact hw'_cell
        · -- Adj v ((σ^k)⁻¹ w') via the iff
          have hbij : (σ^k) ((σ^k)⁻¹ w') = w' :=
            Equiv.apply_symm_apply (σ^k) w'
          have hgoal : Γ.Adj v ((σ^k)⁻¹ w') ↔
              Γ.Adj ((σ^k) v) ((σ^k) ((σ^k)⁻¹ w')) :=
            adj_iff_of_smul_adj_zpow smul_adj k v ((σ^k)⁻¹ w')
          rw [hbij, hkv] at hgoal
          exact hgoal.mpr hw'_adj
      · -- (σ^k) ((σ^k)⁻¹ w') = w'
        exact Equiv.apply_symm_apply (σ^k) w'

end EquitablePartitionFromOrbits

end Moore57
