import Moore57.Moore57Graph.Moore57Definition
import Moore57.Foundations.GroupAction.FixedPoints
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Cyclic group `C₃₈` action on a Moore57 graph

This file packages "an element `g` of order `38` in `Aut(Γ)`" as
`C38ActsOnMoore57`, the cyclic-group analogue of `D19ActsOnMoore57`. A single
element of order `38` is enough to encode the action of `C₃₈ = ⟨g⟩` faithfully,
so we keep the data minimal:

* `g : Equiv.Perm V` — the generator;
* `g_aut` — `g` preserves the adjacency relation;
* `g_pow_thirtyEight = 1` — `g ^ 38 = id`;
* `g_pow_two_ne_one` and `g_pow_nineteen_ne_one` together with
  `g_pow_thirtyEight = 1` force the order of `g` to be exactly `38`.

From `g` we extract the order-`19` rotation `ρ := g ^ 2` and the involution
`τ := g ^ 19`. The two commute (powers of the same element); that is how
`C₃₈` differs from `D₁₉` (where the reflection inverts the rotation).

The non-existence theorem `no_C38_acts_on_Moore57_unconditional` is proved in
`Moore57/C38OnMoore57/NoGo.lean` using the abstract Tier-2 results
`order19_aut_fixedVertexCount_eq_one` and the involution candidate analysis.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Packaging of "an automorphism `g` of `Γ` with order exactly `38`". The
subgroup `⟨g⟩` is then cyclic of order `38`. -/
structure C38ActsOnMoore57
    (V : Type*) [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] where
  /-- `Γ` is a Moore graph of degree `57`. -/
  isMoore : IsMoore57 Γ
  /-- The generator of `C₃₈`. -/
  g : Equiv.Perm V
  /-- The generator preserves edges. -/
  g_aut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (g v) (g w)
  /-- The generator has order dividing `38`. -/
  g_pow_thirtyEight : g ^ 38 = 1
  /-- The generator does not have order `2`. -/
  g_pow_two_ne_one : g ^ 2 ≠ 1
  /-- The generator does not have order `19`. -/
  g_pow_nineteen_ne_one : g ^ 19 ≠ 1

namespace C38ActsOnMoore57

variable (h : C38ActsOnMoore57 V Γ)

/-- Any power of the generator preserves adjacency. -/
theorem g_pow_aut (n : ℕ) :
    ∀ v w : V, Γ.Adj v w ↔ Γ.Adj ((h.g ^ n) v) ((h.g ^ n) w) := by
  induction n with
  | zero => intros; simp
  | succ n ih =>
      intro v w
      rw [pow_succ]
      simp only [Equiv.Perm.mul_apply]
      rw [h.g_aut v w]
      exact ih (h.g v) (h.g w)

/-- The order-`19` element `ρ := g²`. -/
def rho : Equiv.Perm V := h.g ^ 2

/-- The involution `τ := g^19`. -/
def tau : Equiv.Perm V := h.g ^ 19

@[simp] theorem rho_pow_nineteen : h.rho ^ 19 = 1 := by
  show (h.g ^ 2) ^ 19 = 1
  rw [← pow_mul]
  exact h.g_pow_thirtyEight

@[simp] theorem tau_pow_two : h.tau ^ 2 = 1 := by
  show (h.g ^ 19) ^ 2 = 1
  rw [← pow_mul]
  exact h.g_pow_thirtyEight

theorem rho_ne_one : h.rho ≠ 1 := h.g_pow_two_ne_one

theorem tau_ne_one : h.tau ≠ 1 := h.g_pow_nineteen_ne_one

/-- `ρ` and `τ` commute (both are powers of `g`). -/
theorem rho_mul_tau_eq_tau_mul_rho : h.rho * h.tau = h.tau * h.rho := by
  show h.g ^ 2 * h.g ^ 19 = h.g ^ 19 * h.g ^ 2
  rw [← pow_add, ← pow_add, Nat.add_comm]

/-- `ρ` is a graph automorphism. -/
theorem rho_aut (v w : V) : Γ.Adj v w ↔ Γ.Adj (h.rho v) (h.rho w) :=
  h.g_pow_aut 2 v w

/-- `τ` is a graph automorphism. -/
theorem tau_aut (v w : V) : Γ.Adj v w ↔ Γ.Adj (h.tau v) (h.tau w) :=
  h.g_pow_aut 19 v w

/-- `τ` is involutive as a function. -/
theorem tau_involutive : Function.Involutive (h.tau : V → V) := by
  intro v
  have hsq : h.tau ^ 2 = 1 := h.tau_pow_two
  have : (h.tau * h.tau) v = (1 : Equiv.Perm V) v := by
    rw [show h.tau * h.tau = h.tau ^ 2 from (pow_two _).symm, hsq]
  simpa using this

end C38ActsOnMoore57

end Moore57
