import Moore57.Foundations.ZMod19.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

-- `native_decide` is intentional here (see `Moore57/AxiomsCheck.lean`).
set_option linter.style.nativeDecide false

/-!
# Doubling-orbit cardinality propagation in `ZMod 19`

This file isolates the arithmetic part of the natural-language Lemma 6.3
argument: on the nonzero elements of `ZMod 19`, multiplication by `2` is one
18-cycle.  Therefore a natural-valued function that is monotone along doubling
is constant on all nonzero inputs.
-/

namespace Moore57

/-- The doubling map on `ZMod 19`. -/
def zmod19Double (d : ZMod 19) : ZMod 19 :=
  (2 : ZMod 19) * d

@[simp]
theorem zmod19Double_apply (d : ZMod 19) :
    zmod19Double d = (2 : ZMod 19) * d :=
  rfl

/-- Iterating doubling `n` times is multiplication by `2^n`. -/
theorem zmod19Double_iterate_apply (n : ℕ) (d : ZMod 19) :
    (zmod19Double^[n]) d = ((2 : ZMod 19) ^ n) * d := by
  induction n generalizing d with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ, Function.comp_apply, ih, zmod19Double_apply,
        ← mul_assoc, pow_succ]

/-- Doubling has period dividing `18` on all of `ZMod 19`. -/
theorem zmod19Double_iterate_eighteen_apply (d : ZMod 19) :
    (zmod19Double^[18]) d = d := by
  rw [zmod19Double_iterate_apply]
  exact two_pow_eighteen_mul_zmod19 d

/-- The nonzero elements of `ZMod 19` are exactly the powers `2^0, ..., 2^17`. -/
theorem zmod19_nonzero_eq_two_pow {d : ZMod 19} (hd : d ≠ 0) :
    ∃ k : Fin 18, d = ((2 : ZMod 19) ^ (k : ℕ)) := by
  exact
    (show ∀ d : ZMod 19, d ≠ 0 →
        ∃ k : Fin 18, d = ((2 : ZMod 19) ^ (k : ℕ)) by
      native_decide) d hd

/-- Relative orbit form: every nonzero element is a power-of-two multiple of
any chosen nonzero base point. -/
theorem zmod19_nonzero_eq_two_pow_mul
    {d h : ZMod 19} (hd : d ≠ 0) (hh : h ≠ 0) :
    ∃ k : Fin 18, d = ((2 : ZMod 19) ^ (k : ℕ)) * h := by
  have hx : d * h⁻¹ ≠ 0 := mul_ne_zero hd (inv_ne_zero hh)
  rcases zmod19_nonzero_eq_two_pow hx with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    d = (d * h⁻¹) * h := by
      rw [mul_assoc, inv_mul_cancel₀ hh, mul_one]
    _ = ((2 : ZMod 19) ^ (k : ℕ)) * h := by
      rw [hk]

/-- A one-step doubling monotonicity propagates along any finite doubling
iterate. -/
theorem zmod19_le_two_pow_mul_of_double_le
    (e : ZMod 19 → ℕ)
    (hstep : ∀ d : ZMod 19, d ≠ 0 → e d ≤ e ((2 : ZMod 19) * d))
    (n : ℕ) {d : ZMod 19} (hd : d ≠ 0) :
    e d ≤ e (((2 : ZMod 19) ^ n) * d) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hcurrent : ((2 : ZMod 19) ^ n) * d ≠ 0 :=
        two_pow_mul_ne_zero_zmod19 hd n
      exact le_trans ih (by
        calc
          e (((2 : ZMod 19) ^ n) * d)
              ≤ e ((2 : ZMod 19) * (((2 : ZMod 19) ^ n) * d)) :=
                hstep (((2 : ZMod 19) ^ n) * d) hcurrent
          _ = e (((2 : ZMod 19) ^ (n + 1)) * d) := by
                congr 1
                rw [← mul_assoc, pow_succ]
                ring)

/-- Under one-step doubling monotonicity, each nonzero value equals its doubled
value. -/
theorem zmod19_eq_double_of_double_le
    (e : ZMod 19 → ℕ)
    (hstep : ∀ d : ZMod 19, d ≠ 0 → e d ≤ e ((2 : ZMod 19) * d))
    {d : ZMod 19} (hd : d ≠ 0) :
    e d = e ((2 : ZMod 19) * d) := by
  apply le_antisymm
  · exact hstep d hd
  · have hdouble : (2 : ZMod 19) * d ≠ 0 :=
      two_mul_ne_zero_zmod19 hd
    have hle :=
      zmod19_le_two_pow_mul_of_double_le e hstep 17 hdouble
    have hwrap :
        ((2 : ZMod 19) ^ 17) * ((2 : ZMod 19) * d) = d := by
      rw [← mul_assoc]
      change ((2 : ZMod 19) ^ 18) * d = d
      exact two_pow_eighteen_mul_zmod19 d
    simpa [hwrap] using hle

/-- Equality propagates from a nonzero base point along every doubling
iterate. -/
theorem zmod19_eq_two_pow_mul_of_double_le
    (e : ZMod 19 → ℕ)
    (hstep : ∀ d : ZMod 19, d ≠ 0 → e d ≤ e ((2 : ZMod 19) * d))
    (n : ℕ) {d : ZMod 19} (hd : d ≠ 0) :
    e d = e (((2 : ZMod 19) ^ n) * d) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hcurrent : ((2 : ZMod 19) ^ n) * d ≠ 0 :=
        two_pow_mul_ne_zero_zmod19 hd n
      calc
        e d = e (((2 : ZMod 19) ^ n) * d) := ih
        _ = e ((2 : ZMod 19) * (((2 : ZMod 19) ^ n) * d)) :=
          zmod19_eq_double_of_double_le e hstep hcurrent
        _ = e (((2 : ZMod 19) ^ (n + 1)) * d) := by
          congr 1
          rw [← mul_assoc, pow_succ]
          ring

/-- Main propagation lemma for functions on `ZMod 19`: monotonicity along
doubling forces all nonzero values to be equal. -/
theorem zmod19_nonzero_values_eq_of_double_le
    (e : ZMod 19 → ℕ)
    (hstep : ∀ d : ZMod 19, d ≠ 0 → e d ≤ e ((2 : ZMod 19) * d))
    {d h0 : ZMod 19} (hd : d ≠ 0) (hh0 : h0 ≠ 0) :
    e d = e h0 := by
  rcases zmod19_nonzero_eq_two_pow_mul hd hh0 with ⟨k, hk⟩
  have hpow :=
    zmod19_eq_two_pow_mul_of_double_le e hstep (k : ℕ) hh0
  calc
    e d = e (((2 : ZMod 19) ^ (k : ℕ)) * h0) := by
      rw [hk]
    _ = e h0 := hpow.symm

/-- Nonzero subtype for the `ZMod 19` doubling orbit. -/
abbrev ZMod19Nonzero :=
  {d : ZMod 19 // d ≠ 0}

/-- Doubling as a self-map of the nonzero subtype. -/
def zmod19DoubleNonzero (d : ZMod19Nonzero) : ZMod19Nonzero :=
  ⟨(2 : ZMod 19) * d.1, two_mul_ne_zero_zmod19 d.2⟩

@[simp]
theorem zmod19DoubleNonzero_val (d : ZMod19Nonzero) :
    (zmod19DoubleNonzero d : ZMod 19) = (2 : ZMod 19) * d.1 :=
  rfl

/-- Subtype form of the main propagation lemma. -/
theorem zmod19_nonzero_subtype_values_eq_of_double_le
    (e : ZMod19Nonzero → ℕ)
    (hstep : ∀ d : ZMod19Nonzero, e d ≤ e (zmod19DoubleNonzero d))
    (d h0 : ZMod19Nonzero) :
    e d = e h0 := by
  let e0 : ZMod 19 → ℕ := fun x =>
    if hx : x ≠ 0 then e ⟨x, hx⟩ else 0
  have hstep0 :
      ∀ x : ZMod 19, x ≠ 0 → e0 x ≤ e0 ((2 : ZMod 19) * x) := by
    intro x hx
    simpa [e0, hx, two_mul_ne_zero_zmod19 hx] using hstep ⟨x, hx⟩
  have hmain :
      e0 d.1 = e0 h0.1 :=
    zmod19_nonzero_values_eq_of_double_le e0 hstep0 d.2 h0.2
  simpa [e0, d.2, h0.2] using hmain

/-- Finset cardinality boundary form: if the intersections grow under
doubling, then their cardinalities are constant on nonzero inputs. -/
theorem zmod19_card_inter_values_eq_of_double_subset
    {α : Type*} [DecidableEq α]
    (S : ZMod 19 → Finset α) (E : Finset α)
    (hsubset :
      ∀ d : ZMod 19, d ≠ 0 →
        S d ∩ E ⊆ S ((2 : ZMod 19) * d) ∩ E)
    {d h0 : ZMod 19} (hd : d ≠ 0) (hh0 : h0 ≠ 0) :
    (S d ∩ E).card = (S h0 ∩ E).card := by
  exact
    zmod19_nonzero_values_eq_of_double_le
      (fun x : ZMod 19 => (S x ∩ E).card)
      (fun x hx => Finset.card_le_card (hsubset x hx))
      hd hh0

end Moore57
