import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Lemma 7

> If `x ∈ X` is central and contributing to `O`, then
> `|{v ∈ O : vˣ ∼ v}| = |O|`.

Equivalent: every vertex of `O` is moved by `x` to an adjacent vertex.

Proof: For any `v ∈ O`, transitivity gives `g ∈ X` with `g v₀ = v`
(where `v₀` is the witness from `hcontrib`).  By centrality,
`x v = x (g v₀) = g (x v₀)`.  Since `g` is an automorphism,
`Γ.Adj (g v₀) (g (x v₀)) ↔ Γ.Adj v₀ (x v₀)`, which holds by hypothesis.
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 7 (central contribution is total on the orbit).**

Let `X ≤ Aut(Γ)` be a group of automorphisms acting transitively on
`O ⊆ V`, and let `x ∈ X` be central (commutes with every `g ∈ X`).
If there exists `v₀ ∈ O` with `Γ.Adj v₀ (x v₀)`, then this holds for
every `v ∈ O`. -/
theorem lem7_central_full_contribution
    (x : Equiv.Perm V)
    (O : Set V)
    (hX_central : ∀ g : Equiv.Perm V, g ∈ ({y | ∀ v ∈ O, y v ∈ O} : Set _) →
      (∀ a b, Γ.Adj a b ↔ Γ.Adj (g a) (g b)) → g * x = x * g)
    (hO_transitive : ∀ v w, v ∈ O → w ∈ O →
      ∃ g : Equiv.Perm V,
        (∀ u ∈ O, g u ∈ O) ∧
        (∀ a b, Γ.Adj a b ↔ Γ.Adj (g a) (g b)) ∧
        g v = w)
    (hcontrib : ∃ v₀ ∈ O, Γ.Adj v₀ (x v₀)) :
    ∀ v ∈ O, Γ.Adj v (x v) := by
  obtain ⟨v₀, hv₀_mem, hv₀_adj⟩ := hcontrib
  intro v hv_mem
  obtain ⟨g, hg_inv, hg_aut, hgv⟩ := hO_transitive v₀ v hv₀_mem hv_mem
  have hcomm : g * x = x * g := hX_central g hg_inv hg_aut
  -- Show: Γ.Adj v (x v).  Substitute v = g v₀ and rewrite x v using centrality.
  have hxv : x v = g (x v₀) := by
    have : x v = (x * g) v₀ := by simp [← hgv, Equiv.Perm.mul_apply]
    rw [this, ← hcomm]
    simp [Equiv.Perm.mul_apply]
  -- Γ.Adj v (x v) = Γ.Adj (g v₀) (g (x v₀)) ↔ Γ.Adj v₀ (x v₀).
  rw [hxv, ← hgv, ← hg_aut]
  exact hv₀_adj

end Moore57.Papers.MacajSiran2010.S3
