import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition
import Moore57.Foundations.GraphTheory.InducedTrace
import Moore57.Foundations.GraphTheory.OrbitInducedTrace

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Lemma 9

> (1) Let `O` be an orbit of `X` and let `v ∈ O`. Then
> ```
> Tr(O) = |{x ∈ X : v ∼ vˣ}| · |O| / |X|.
> ```
>
> (2) ```
> |X| · Tr(X) = |{(x, v) ∈ X × Γ : v ∼ vˣ}| = Σ_{x ∈ X} a₁(x).
> ```

Status:
* (2) **proven** in two forms:
  - `lem9_global_trace_formula` : ℕ-form double-counting.
  - `lem9_global_trace_formula_rat` : ℚ-form using `groupTrace Γ X = Tr(X)`.
* (1) [deferred-heavy] — requires orbit-stabilizer + connecting to the
  abstract orbit Tr(O).
-/

namespace Moore57.Papers.MacajSiran2010.S3

open Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 9 (1) (orbit trace formula).** [deferred-heavy]

Paper-stub kept for backwards compatibility; the proper-signature
form is `lem9_orbit_inducedTrace_eq_neighborhood` (partial: equality
to `deg_{Γ[O]}(v)`).

For `v ∈ O` an `X`-orbit, the induced-subgraph trace `Tr(O)` (the
average in-orbit degree) equals `#{x ∈ X : v ∼ xv} · |O| / |X|`.

Proof outline: by orbit-stabilizer, `|X| = |O| · |Stab_X(v)|`, and the
multiplicity of `xv = w` over `x ∈ X` is `|Stab_X(v)|` for each
`w ∈ O`.  Hence `#{x : v ∼ xv} = deg_O(v) · |Stab_X(v)|`, giving
`Tr(O) = deg_O(v) = #{x : v ∼ xv} · |O| / |X|`. -/
theorem lem9_orbit_trace_formula
    (X : Subgroup (Equiv.Perm V)) [Fintype X]
    (hX_aut : ∀ x : X, ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (x • a) (x • b))
    {O : Finset V} {v : V}
    (h_orbit_eq : O = (Finset.univ : Finset X).image (fun x : X => x • v)) :
    inducedTrace Γ O =
      (((Finset.univ : Finset X).filter (fun x : X => Γ.Adj v (x • v))).card : ℚ) *
        (O.card : ℚ) / (Fintype.card X : ℚ) :=
  Moore57.inducedTrace_orbit_count_formula_finite_group
    (Γ := Γ) (G := X) hX_aut h_orbit_eq

/-- **Lemma 9 (1) (proper signature: `Tr(O) = deg_{Γ[O]}(v)` for any
`v ∈ O`).**

For a vertex subset `O ⊆ V` that is transitively acted upon by graph
automorphisms (each `w ∈ O` is the image of `v` under some graph
automorphism `φ_w` preserving `O`), the induced-subgraph trace
`Tr(Γ[O])` equals the in-`O` degree of any fixed `v ∈ O`.

This is the geometric (transitivity-based) content of Lemma 9 (1).
The full count form `Tr(O) = #{x ∈ X : v ∼ xv} · |O| / |X|` is below
in `lem9_orbit_inducedTrace_count_formula`.

See `Moore57.inducedTrace_eq_neighborhood_card_of_transitive`. -/
theorem lem9_orbit_inducedTrace_eq_neighborhood
    {O : Finset V} {v : V} (hv : v ∈ O)
    (hO_trans : ∀ w ∈ O, ∃ φ : Equiv.Perm V,
        (∀ a b : V, Γ.Adj a b ↔ Γ.Adj (φ a) (φ b)) ∧
        φ v = w ∧
        ∀ u : V, u ∈ O ↔ φ u ∈ O) :
    inducedTrace Γ O = ((O.filter (fun w => Γ.Adj v w)).card : ℚ) :=
  Moore57.inducedTrace_eq_neighborhood_card_of_transitive hv hO_trans

/-- **Lemma 9 (1) (full count form): `Tr(O) = count · |O| / |X|`.**

Given:
* `O` a vertex subset transitively acted upon by graph automorphisms
  (the geometric data; see `lem9_orbit_inducedTrace_eq_neighborhood`),
* `Xfs : Finset (Equiv.Perm V)` modelling the (finite) automorphism
  group whose orbits we are studying,
* the orbit-stabilizer fiber-uniformity property:
  every `w ∈ O` has the same `Xfs`-fiber size `stabCard`.

Then `inducedTrace Γ O = count · |O| / |X|` where
`count = #{y ∈ Xfs : v ~ y v}`.

The fiber-uniformity hypothesis encodes the orbit-stabilizer theorem
applied pointwise (`#{y ∈ Xfs : y v = w} = |Stab|` is constant); it
is taken as a hypothesis so the result is purely combinatorial. -/
theorem lem9_orbit_inducedTrace_count_formula
    {O : Finset V} {v : V} (hv : v ∈ O)
    (hO_trans : ∀ w ∈ O, ∃ φ : Equiv.Perm V,
        (∀ a b : V, Γ.Adj a b ↔ Γ.Adj (φ a) (φ b)) ∧
        φ v = w ∧
        ∀ u : V, u ∈ O ↔ φ u ∈ O)
    {Xfs : Finset (Equiv.Perm V)} (hXfs_nonempty : Xfs.Nonempty)
    (stabCard : ℕ)
    (h_fiber : ∀ w ∈ O,
        (Xfs.filter (fun y : Equiv.Perm V => y v = w)).card = stabCard)
    (h_orbit_eq : O = Xfs.image (fun y : Equiv.Perm V => y v))
    (h_yv_in_O : ∀ y ∈ Xfs, y v ∈ O) :
    inducedTrace Γ O =
      ((Xfs.filter (fun y : Equiv.Perm V => Γ.Adj v (y v))).card : ℚ) *
        (O.card : ℚ) / (Xfs.card : ℚ) :=
  Moore57.inducedTrace_orbit_count_formula hv hO_trans hXfs_nonempty
    stabCard h_fiber h_orbit_eq h_yv_in_O

/-- **Lemma 9 (1) (finite subgroup form).**

For a finite subgroup `X ≤ Sym(V)` acting by graph automorphisms and
`O = X · v`, the orbit trace formula needs no separate fiber-uniformity
hypothesis: the uniform fiber count is supplied by orbit-stabilizer.

This is the preferred formal entry point when the paper's `X` is available
as an actual subgroup rather than a raw `Finset` of permutations. -/
theorem lem9_orbit_inducedTrace_count_formula_subgroup
    (X : Subgroup (Equiv.Perm V)) [Fintype X]
    (hX_aut : ∀ x : X, ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (x • a) (x • b))
    {O : Finset V} {v : V}
    (h_orbit_eq : O = (Finset.univ : Finset X).image (fun x : X => x • v)) :
    inducedTrace Γ O =
      (((Finset.univ : Finset X).filter (fun x : X => Γ.Adj v (x • v))).card : ℚ) *
        (O.card : ℚ) / (Fintype.card X : ℚ) :=
  Moore57.inducedTrace_orbit_count_formula_finite_group
    (Γ := Γ) (G := X) hX_aut h_orbit_eq

/-- **Lemma 9 (2) (ℕ-form: double-counting `Σ_x a₁(x) = |{(x, v) : v ~ x v}|`).**

Pure double-counting identity (no Moore57 hypothesis needed).  The
LHS counts pairs `(x, v)` with `v ~ x v`, where `x` ranges over a
finite set `X` of permutations.  By `Finset.card_filter` and
`Finset.sum_product`, this equals `Σ_{x ∈ X} a₁(x)`. -/
theorem lem9_global_trace_formula
    {X : Finset (Equiv.Perm V)} :
    (((X ×ˢ (Finset.univ : Finset V)).filter
        (fun p => Γ.Adj p.2 (p.1 p.2))).card : ℕ) =
      ∑ x ∈ X, adjacentMovedCount Γ x := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  unfold adjacentMovedCount
  rw [Finset.card_filter]

/-- **Lemma 9 (2) (ℚ-form: `|X| · Tr(X) = Σ a₁(x)`).**

The rational form using `groupTrace Γ X` from
`Moore57.Foundations.GraphTheory.InducedTrace`. -/
theorem lem9_global_trace_formula_rat
    {X : Finset (Equiv.Perm V)} (hX : X.Nonempty) :
    (X.card : ℚ) * groupTrace Γ X =
      ∑ x ∈ X, (adjacentMovedCount Γ x : ℚ) :=
  groupTrace_card_mul_eq_sum_a1 X hX

end Moore57.Papers.MacajSiran2010.S3
