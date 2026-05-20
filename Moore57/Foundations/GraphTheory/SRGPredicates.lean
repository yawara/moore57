import Moore57.Foundations.GraphTheory.PetersenGraph
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# SRG identification predicates: Petersen-like and Hoffman–Singleton-like

Abstract predicates capturing "this graph looks like Petersen" or
"this graph looks like Hoffman–Singleton" via the parameters of a strongly
regular graph (without committing to a specific carrier type).

## Main definitions

* `IsPetersenLike G` ⇔ `G.IsSRGWith 10 3 0 1`.
* `IsHoffmanSingletonLike G` ⇔ `G.IsSRGWith 50 7 0 1`.

## Uniqueness

Classical results (Hoffman–Singleton 1960) imply each predicate uniquely
determines the graph up to isomorphism:
* `IsPetersenLike G` ⟹ `G ≃ petersenGraph` (provable via classification).
* `IsHoffmanSingletonLike G` ⟹ `G ≃ hoffmanSingletonGraph` (the latter not
  explicitly constructed here, but characterized by its SRG parameters).

These uniqueness statements feed the `lem17_*` / `lem18_*` bridge lemmas in
`Section06_PGroupsOverview`.
-/

namespace Moore57

open SimpleGraph

variable {V : Type*} [Fintype V]

/-- **Petersen-like predicate**: `G` is a `(10, 3, 0, 1)`-strongly regular
graph.

The explicit `petersenGraph` (`Moore57.Foundations.GraphTheory.PetersenGraph`)
satisfies this predicate (`petersenGraph_isPetersenLike`).  By the classical
Hoffman–Singleton classification, any graph satisfying this predicate is
isomorphic to the explicit Petersen graph. -/
abbrev IsPetersenLike (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.IsSRGWith 10 3 0 1

/-- **Hoffman–Singleton-like predicate**: `G` is a `(50, 7, 0, 1)`-strongly
regular graph.

The Hoffman–Singleton graph is the unique (up to isomorphism) graph satisfying
this predicate — see `Moore57.Foundations.GraphTheory.HoffmanSingleton` for
the classical Hoffman–Singleton classification chain. -/
abbrev IsHoffmanSingletonLike (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.IsSRGWith 50 7 0 1

/-- **The explicit `petersenGraph` is Petersen-like.** -/
theorem petersenGraph_isPetersenLike : IsPetersenLike petersenGraph :=
  petersenGraph_isSRG

/-- **Petersen-like graphs have 10 vertices.** -/
theorem isPetersenLike_card {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) : Fintype.card V = 10 := h.card

/-- **Petersen-like graphs are 3-regular.** -/
theorem isPetersenLike_regular {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) : G.IsRegularOfDegree 3 := h.regular

/-- **Hoffman–Singleton-like graphs have 50 vertices.** -/
theorem isHoffmanSingletonLike_card {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsHoffmanSingletonLike G) : Fintype.card V = 50 := h.card

/-- **Hoffman–Singleton-like graphs are 7-regular.** -/
theorem isHoffmanSingletonLike_regular {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsHoffmanSingletonLike G) : G.IsRegularOfDegree 7 := h.regular

end Moore57
