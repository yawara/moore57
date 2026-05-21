import Moore57.Foundations.GraphTheory.PetersenGraph

/-!
# Petersen uniqueness (statement-only, classical theorem)

A classical theorem (Bose 1963; Hoffman–Singleton 1960 in the Moore-graph
context) states that the Petersen graph is the **unique** strongly regular
graph with parameters `(10, 3, 0, 1)` up to isomorphism.  Equivalently, any
`IsSRGWith G 10 3 0 1` admits a graph isomorphism `G ≃g petersenGraph`.

Formalising this theorem is paper-level work (a few-hundred LOC of
combinatorial case analysis or a Bose–Mesner / spectral argument), so we
package only the **statement** here as a `Prop` (`PetersenUniqueness`) and
provide forward dispatch lemmas conditional on it.  The actual proof is
left as a deferred-heavy formalisation goal.

## Why a Prop-level statement?

Moore57's §6 Lem 17 case (1) dispatch produces `IsSRGWith 10 3 0 1` on the
σ-fixed induced subgraph (`OrderThreeShapeClassification.lean`).  Promoting
this to `PetersenFixedData` (the structure consumed by the §6 Lem 17
arithmetic dispatch) needs a graph isomorphism to the explicit
`petersenGraph`, i.e. exactly Petersen uniqueness.

By packaging the statement as a `Prop`, we can:

* keep the §6 dispatch closed (any future Lean-side proof of
  `PetersenUniqueness` immediately unblocks the full Lem 17 case (1)
  branch);
* expose paper-level conditional lemmas of the form
  `PetersenUniqueness → ... → PetersenFixedData Γ σ` that downstream files
  can apply once the uniqueness Prop is supplied;
* keep the §6 dispatch decoupled from any specific uniqueness-proof
  strategy (Bose–Mesner, spectral, direct combinatorial enumeration).

## Main statements

* `PetersenUniqueness` — the uniqueness Prop:
  `∀ {α} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj],
     G.IsSRGWith 10 3 0 1 → Nonempty (G ≃g petersenGraph)`.
* `petersenGraph_satisfies_isSRGWith` — `petersenGraph` itself is an
  instance (a sanity check that the Prop is consistent with the explicit
  graph).

## Not in scope

* The actual proof of `PetersenUniqueness`.  This is paper-level work
  (Bose 1963; cf. Hoffman–Singleton 1960 for the Moore-graph parameter
  family).  We do **not** introduce any `sorry`/`axiom` here — the Prop
  remains a statement that downstream constructions are conditional on.
-/

namespace Moore57

open SimpleGraph

/-- **Petersen uniqueness (statement).**

Any strongly regular graph with parameters `(10, 3, 0, 1)` is isomorphic
to the explicit `petersenGraph` (`SimpleGraph (Fin 10)`).

This is a classical theorem (Bose 1963; cf. Hoffman–Singleton 1960
specialised to the Petersen parameter row).  We encode it as a `Prop` so
that downstream Moore57 dispatch lemmas can be **conditional** on it
without committing to a specific Lean-side proof strategy.

The `Nonempty` wrapping reflects that the isomorphism is not canonical
(Petersen has a non-trivial automorphism group, namely `S_5`). -/
def PetersenUniqueness : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj],
    G.IsSRGWith 10 3 0 1 → Nonempty (G ≃g petersenGraph)

/-- **Petersen graph realises `IsSRGWith 10 3 0 1`** (sanity check).

A trivial consequence of `petersenGraph_isSRG`: the explicit `petersenGraph`
itself satisfies the SRG signature.  Recorded as a re-export under the
`PetersenUniqueness` namespace to confirm the Prop's statement is
consistent (the explicit graph is at minimum in its own equivalence
class). -/
theorem petersenGraph_satisfies_isSRGWith :
    petersenGraph.IsSRGWith 10 3 0 1 := petersenGraph_isSRG

/-- **The `PetersenUniqueness` Prop holds for `petersenGraph` itself.**

A trivial special case: `petersenGraph` is isomorphic to itself via
the identity isomorphism. -/
theorem petersenGraph_self_iso : Nonempty (petersenGraph ≃g petersenGraph) :=
  ⟨SimpleGraph.Iso.refl⟩

/-- **Reflexivity of the Petersen-uniqueness claim on `petersenGraph`.**

Applying any putative proof of `PetersenUniqueness` to the explicit
`petersenGraph` (with the parameter hypothesis discharged by
`petersenGraph_isSRG`) yields the trivial self-isomorphism.  This
serves as a sanity check for the Prop's statement. -/
theorem PetersenUniqueness.apply_self (h : PetersenUniqueness.{0}) :
    Nonempty (petersenGraph ≃g petersenGraph) := by
  -- `petersenGraph : SimpleGraph (Fin 10)` has universe 0.
  -- Use the universe-0 specialisation of `h`.
  exact h petersenGraph petersenGraph_isSRG

/-! ### Equivalent reformulations of `PetersenUniqueness`

The uniqueness Prop can be restated in several equivalent forms.
We provide a few convenient bridge lemmas for downstream proofs
that prefer specific shapes. -/

/-- **Transitivity: any two Petersen-like graphs over the same carrier
`α` are isomorphic to each other, via `petersenGraph` as a bridge.**

This is a single-universe version of the symmetric form, avoiding
the universe-polymorphism issue with two distinct carriers `α, β`. -/
theorem PetersenUniqueness.iso_of_two_petersenLike
    (h : PetersenUniqueness.{u}) {α : Type u} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (hG : G.IsSRGWith 10 3 0 1) (hH : H.IsSRGWith 10 3 0 1) :
    Nonempty (G ≃g H) := by
  obtain ⟨φ⟩ := h G hG
  obtain ⟨ψ⟩ := h H hH
  exact ⟨φ.trans ψ.symm⟩

/-- **Any Petersen-like graph has exactly 15 edges.**

A consequence of the SRG parameters via degree-sum (independent of
the `PetersenUniqueness` hypothesis).  This is a useful "smoke test"
lemma showing that the parameters give concrete numerical information,
matching `petersenGraph_edgeFinset_card`. -/
theorem isSRGWith_10_3_0_1_edge_count
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.IsSRGWith 10 3 0 1) : G.edgeFinset.card = 15 := by
  have hcard : Fintype.card α = 10 := hG.card
  have hreg : ∀ v : α, G.degree v = 3 := hG.regular
  have hsum := G.sum_degrees_eq_twice_card_edges
  have h30 : ∑ v : α, G.degree v = 30 := by
    calc ∑ v : α, G.degree v
        = ∑ _v : α, 3 := Finset.sum_congr rfl (fun v _ => hreg v)
      _ = Fintype.card α * 3 := by
          rw [Finset.sum_const, Finset.card_univ]; ring
      _ = 30 := by rw [hcard]
  rw [h30] at hsum
  omega

end Moore57
