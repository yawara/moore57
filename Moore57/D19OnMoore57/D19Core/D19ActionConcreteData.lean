import Moore57.D19OnMoore57.Trace.TraceMultiplicityPackaging
import Moore57.D19Contradiction

/-!
# Concrete D19 action data

This file specializes the concrete Section 5/6 data to a fixed
`D19ActsOnMoore57` witness.  The rotation, `a1`, and trace-character fields are
therefore inherited from the action and from the reduced `D19TraceInput`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Reduced concrete orbit data attached to a fixed `D19ActsOnMoore57` action.

The action supplies the rotation maps and `a1`; `traceInput` supplies just the
reduced trace data needed to build `TraceRepresentationData h.a1`. -/
structure D19ActionConcreteData (h : D19ActsOnMoore57 V Γ) where
  W : Fin 56 → ZMod 19 → V
  W_injective : ∀ q : Fin 56, Function.Injective (W q)
  traceInput : D19TraceInput h
  a1_contribution :
    ∀ d : ZMod 19, d ≠ 0 →
      h.a1 d =
        38 + 38 *
          ((Finset.univ : Finset (Fin 56)).filter
            (fun q => d ∈ internalDiffSet Γ (W q))).card

namespace D19ActionConcreteData

variable {h : D19ActsOnMoore57 V Γ}

/-- The internal difference set defined by the concrete orbit representative. -/
noncomputable def D (data : D19ActionConcreteData h) (q : Fin 56) :
    Finset (ZMod 19) :=
  internalDiffSet Γ (data.W q)

/-- The internal difference set never contains zero. -/
theorem D_zero (data : D19ActionConcreteData h) (q : Fin 56) :
    (0 : ZMod 19) ∉ data.D q :=
  internalDiffSet_zero (data.W q)

/-- Membership in the internal difference set gives the corresponding
adjacency relation along the orbit. -/
theorem D_adj (data : D19ActionConcreteData h) (q : Fin 56) (d : ZMod 19)
    (hd : d ∈ data.D q) :
    ∀ i : ZMod 19, Γ.Adj (data.W q i) (data.W q (i + d)) :=
  internalDiffSet_adj (data.W q) hd

/-- Internal difference sets are closed under negation. -/
theorem D_symm (data : D19ActionConcreteData h) (q : Fin 56) (d : ZMod 19)
    (hd : d ∈ data.D q) :
    -d ∈ data.D q :=
  internalDiffSet_symm (data.W q) hd

/-- The Section 5 upper bound `|D_q| ≤ 2`, using the Moore graph
no-four-cycle property from the action witness. -/
theorem Dq_le_two (data : D19ActionConcreteData h) :
    ∀ q : Fin 56, (data.D q).card ≤ 2 := by
  intro q
  exact Dq_card_le_two_of_moore h.isMoore (data.W q) (data.W_injective q) (data.D q)
    (data.D_zero q) (data.D_adj q) (data.D_symm q)

/-- Convert the reduced trace input into the arithmetic representation data
for the action's `a1`. -/
noncomputable def traceRep (data : D19ActionConcreteData h) :
    TraceRepresentationData h.a1 :=
  data.traceInput.toTraceRepresentationData

/-- The Section 4 lower bound `N_d ≥ 8`, now using the action's `a1`. -/
theorem Nd_lower (data : D19ActionConcreteData h) :
    ∀ d : ZMod 19, d ≠ 0 →
      8 ≤ ((Finset.univ : Finset (Fin 56)).filter
        (fun q => d ∈ data.D q)).card :=
  Nd_lower_of_trace_representation data.D h.a1 data.traceRep (by
    intro d hd
    simpa [D] using data.a1_contribution d hd)

/-- Reduced concrete action data cannot exist for a `D19ActsOnMoore57` action. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ActionConcreteData h) := by
  rintro ⟨data⟩
  exact counting_contradiction_zmod data.D (fun q => data.D_zero q)
    data.Dq_le_two data.Nd_lower

end D19ActionConcreteData

end Moore57
