import Moore57.Moore57Graph.Moore57Definition
import Moore57.D19OnMoore57.Counting.AbstractCounting

namespace Moore57

/-- Translate the indices of a `ZMod 19`-indexed orbit by `t`. -/
def translateW {V : Type*} (W : ZMod 19 → V) (t : ZMod 19) : ZMod 19 → V :=
  fun i => W (i + t)

/-- Membership in the internal difference set is preserved by translating indices. -/
theorem internalDiffSet_translate_mem
    {V : Type*} {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (W : ZMod 19 → V) (t : ZMod 19) {d : ZMod 19}
    (hd : d ∈ internalDiffSet Γ W) :
    d ∈ internalDiffSet Γ (translateW W t) := by
  classical
  rw [internalDiffSet] at hd ⊢
  rcases (by simpa using hd) with ⟨hd0, hAdj⟩
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hd0 ⊢
  refine ⟨hd0, ?_⟩
  intro i
  have h := hAdj (i + t)
  simpa [translateW, add_assoc, add_left_comm, add_comm] using h

/-- Membership in the internal difference set reflects back from translated indices. -/
theorem internalDiffSet_mem_of_translate_mem
    {V : Type*} {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (W : ZMod 19 → V) (t : ZMod 19) {d : ZMod 19}
    (hd : d ∈ internalDiffSet Γ (translateW W t)) :
    d ∈ internalDiffSet Γ W := by
  classical
  rw [internalDiffSet] at hd ⊢
  rcases (by simpa using hd) with ⟨hd0, hAdj⟩
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hd0 ⊢
  refine ⟨hd0, ?_⟩
  intro i
  have h := hAdj (i - t)
  have hleft : i - t + t = i := by
    simp [sub_eq_add_neg, add_assoc]
  have hright : (i - t + d) + t = i + d := by
    calc
      (i - t + d) + t = (i - t + t) + d := by
        ac_rfl
      _ = i + d := by
        rw [hleft]
  simpa [translateW, hleft, hright] using h

/-- Translating all indices of an orbit does not change its internal difference set. -/
theorem internalDiffSet_translate
    {V : Type*} {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (W : ZMod 19 → V) (t : ZMod 19) :
    internalDiffSet Γ (translateW W t) = internalDiffSet Γ W := by
  classical
  ext d
  exact ⟨internalDiffSet_mem_of_translate_mem W t,
    internalDiffSet_translate_mem W t⟩

/-- Inline version of `internalDiffSet_translate` for the translated function
`fun i => W (i + t)`. -/
theorem internalDiffSet_translate_fun
    {V : Type*} {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (W : ZMod 19 → V) (t : ZMod 19) :
    internalDiffSet Γ (fun i => W (i + t)) = internalDiffSet Γ W := by
  simpa [translateW] using internalDiffSet_translate (Γ := Γ) W t

end Moore57
