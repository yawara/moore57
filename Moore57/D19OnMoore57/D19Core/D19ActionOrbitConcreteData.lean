import Moore57.D19OnMoore57.D19Core.D19ActionConcreteData
import Moore57.D19OnMoore57.Rotation.RotationOrbitFinset

/-!
# Orbit-generated concrete data for a D19 action

This file packages the Section 5/6 concrete orbit data in a reduced form:
each `W q` is generated from one base vertex by the rotation action, so
injectivity of `W q` is derived from a moved-vertex hypothesis.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Reduced concrete data for a `D19ActsOnMoore57` action.

The `Fin 56` many 19-cycles are represented by base vertices.  The full
orbit map is recovered as `h.rotation i (base q)`, and its injectivity follows
from `base_moved`. -/
structure D19ActionOrbitConcreteData (h : D19ActsOnMoore57 V Γ) where
  /-- One representative for each of the 56 rotation orbits. -/
  base : Fin 56 → V
  /-- The chosen representatives are moved by the first nontrivial rotation. -/
  base_moved : ∀ q : Fin 56, h.rotation 1 (base q) ≠ base q
  /-- Split trace input for the action. -/
  traceInput : D19TraceInput h
  /-- Contribution of the 56 rotation orbits to the adjacent-moved count. -/
  a1_contribution :
    ∀ d : ZMod 19, d ≠ 0 →
      h.a1 d =
        38 + 38 *
          ((Finset.univ : Finset (Fin 56)).filter
            (fun q => d ∈ internalDiffSet Γ (fun i => h.rotation i (base q)))).card

namespace D19ActionOrbitConcreteData

variable {h : D19ActsOnMoore57 V Γ}

/-- The full orbit map generated from the base vertex of orbit `q`. -/
noncomputable def W (data : D19ActionOrbitConcreteData h) (q : Fin 56) :
    ZMod 19 → V :=
  fun i => h.rotation i (data.base q)

/-- Injectivity of the generated orbit map. -/
theorem W_injective (data : D19ActionOrbitConcreteData h) (q : Fin 56) :
    Function.Injective (data.W q) := by
  exact h.rotationOrbitW_injective_of_nonzero_moved
    (d := 1) (x := data.base q) (by decide) (data.base_moved q)

/-- Forget that the concrete orbit maps are generated from base vertices. -/
noncomputable def toActionConcreteData (data : D19ActionOrbitConcreteData h) :
    D19ActionConcreteData h where
  W := data.W
  W_injective := data.W_injective
  traceInput := data.traceInput
  a1_contribution := by
    intro d hd
    simpa [W] using data.a1_contribution d hd

/-- Internal difference set attached to the generated orbit `q`. -/
noncomputable def D (data : D19ActionOrbitConcreteData h) (q : Fin 56) :
    Finset (ZMod 19) :=
  internalDiffSet Γ (data.W q)

/-- The generated internal difference set never contains zero. -/
theorem D_zero (data : D19ActionOrbitConcreteData h) (q : Fin 56) :
    (0 : ZMod 19) ∉ data.D q :=
  internalDiffSet_zero (data.W q)

/-- Membership in the generated internal difference set gives adjacency along
the generated orbit. -/
theorem D_adj (data : D19ActionOrbitConcreteData h) (q : Fin 56) (d : ZMod 19)
    (hd : d ∈ data.D q) :
    ∀ i : ZMod 19, Γ.Adj (data.W q i) (data.W q (i + d)) :=
  internalDiffSet_adj (data.W q) hd

/-- The generated internal difference set is closed under sign. -/
theorem D_symm (data : D19ActionOrbitConcreteData h) (q : Fin 56) (d : ZMod 19)
    (hd : d ∈ data.D q) :
    -d ∈ data.D q :=
  internalDiffSet_symm (data.W q) hd

/-- The Moore no-4-cycle argument bounds every generated internal difference
set by two elements. -/
theorem Dq_le_two (data : D19ActionOrbitConcreteData h) :
    ∀ q : Fin 56, (data.D q).card ≤ 2 := by
  intro q
  exact Dq_card_le_two_of_moore h.isMoore (data.W q) (data.W_injective q) (data.D q)
    (data.D_zero q) (data.D_adj q) (data.D_symm q)

/-- Trace representation data derived from the reduced action trace input. -/
noncomputable def traceRep (data : D19ActionOrbitConcreteData h) :
    TraceRepresentationData h.a1 :=
  data.traceInput.toTraceRepresentationData

/-- The trace arithmetic gives the Section 6 lower bound for each nontrivial
difference. -/
theorem Nd_lower (data : D19ActionOrbitConcreteData h) :
    ∀ d : ZMod 19, d ≠ 0 →
      8 ≤ ((Finset.univ : Finset (Fin 56)).filter (fun q => d ∈ data.D q)).card := by
  exact Nd_lower_of_trace_representation data.D h.a1 data.traceRep (by
    intro d hd
    simpa [D, W] using data.a1_contribution d hd)

/-- Orbit-generated concrete data for a `D19ActsOnMoore57` action cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ActionOrbitConcreteData h) := by
  rintro ⟨data⟩
  exact D19ActionConcreteData.not_nonempty h ⟨data.toActionConcreteData⟩

end D19ActionOrbitConcreteData

end Moore57
