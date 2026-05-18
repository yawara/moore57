import Moore57.Foundations.ZMod19.Lemmas

-- `native_decide` is intentional here (see `Moore57/AxiomsCheck.lean`).
set_option linter.style.nativeDecide false

/-!
# Small avoidance witnesses in `ZMod 19`

This file isolates the elementary arithmetic needed to choose two nonzero
residues avoiding a prescribed nonzero residue.  It is intended as a reusable
boundary lemma for card-two common-neighbor constructions.
-/

namespace Moore57

/-- Given a nonzero residue `j` in `ZMod 19`, there are two distinct nonzero
residues `k` and `l` which both avoid `j`. -/
theorem zmod19_card_two_avoidance_witnesses
    (j : ZMod 19) (_hj : j ≠ 0) :
    ∃ k l : ZMod 19,
      k ≠ 0 ∧ l ≠ 0 ∧ k ≠ j ∧ l ≠ j ∧ k ≠ l := by
  by_cases h1 : j = (1 : ZMod 19)
  · refine ⟨2, 3, ?_, ?_, ?_, ?_, ?_⟩
    · native_decide
    · native_decide
    · simpa [h1] using (by native_decide : (2 : ZMod 19) ≠ 1)
    · simpa [h1] using (by native_decide : (3 : ZMod 19) ≠ 1)
    · native_decide
  · by_cases h2 : j = (2 : ZMod 19)
    · refine ⟨1, 3, ?_, ?_, ?_, ?_, ?_⟩
      · native_decide
      · native_decide
      · simpa [h2] using (by native_decide : (1 : ZMod 19) ≠ 2)
      · simpa [h2] using (by native_decide : (3 : ZMod 19) ≠ 2)
      · native_decide
    · refine ⟨1, 2, ?_, ?_, ?_, ?_, ?_⟩
      · native_decide
      · native_decide
      · intro h
        exact h1 h.symm
      · intro h
        exact h2 h.symm
      · native_decide

end Moore57
