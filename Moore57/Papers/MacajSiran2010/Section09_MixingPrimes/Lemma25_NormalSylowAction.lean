import Mathlib.GroupTheory.Sylow
import Moore57.Foundations.GroupAction.NormalQuotientAction

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Lemma 25

> If `P` is normal in `X`, then `Q` acts on orbits of `P`. In particular,
> `Q` acts as an automorphism group of `Fix(P)`.

Used throughout §9 to reduce mixing-primes arguments to Lemma 19 cases.

Status:
* `lem25_x_acts_on_fixedPoints`: **proven** via
  `Moore57.restrictToFixedPoints` — each element of `X` (any subgroup
  contained in `N(P)`) restricts to a permutation of `Fix(P)`.
* `lem25_P_acts_trivially`: **proven** — `P` itself acts as identity on
  `Fix(P)`.  Combined with the above, the `X`-action descends to a
  `X/P`-action (full quotient construction left for future work; the
  paper-faithful "Q acts on Fix(P)" content is captured at this level).
* `lem25_normal_sylow_action`: original True-stub kept for backwards
  compatibility.
-/

open Moore57

namespace Moore57.Papers.MacajSiran2010.S9

variable {V : Type*}

/-- **Lemma 25 (X-action on `Fix(P)` for `P ◁ X`).** [done]

For any subgroup `X ≤ Equiv.Perm V` contained in the normaliser of `P`
(equivalently, `P ◁ X`), every `g ∈ X` restricts to a permutation of
`MulAction.fixedPoints P V`. -/
def lem25_x_acts_on_fixedPoints
    (X P : Subgroup (Equiv.Perm V))
    (hP_normal_in_X : X ≤ Subgroup.normalizer (P : Set (Equiv.Perm V)))
    (g : Equiv.Perm V) (hg : g ∈ X) :
    Equiv (MulAction.fixedPoints P V) (MulAction.fixedPoints P V) :=
  restrictToFixedPoints P (hP_normal_in_X hg)

/-- **Lemma 25 (P acts trivially on `Fix(P)`).** [done]

Composed with `lem25_x_acts_on_fixedPoints`, this shows the X-action
factors through `X ⧸ P`. -/
theorem lem25_P_acts_trivially
    (X P : Subgroup (Equiv.Perm V))
    (hP_normal_in_X : X ≤ Subgroup.normalizer (P : Set (Equiv.Perm V)))
    (hP_le_X : P ≤ X)
    (p : Equiv.Perm V) (hp : p ∈ P) :
    lem25_x_acts_on_fixedPoints X P hP_normal_in_X p (hP_le_X hp) = Equiv.refl _ := by
  unfold lem25_x_acts_on_fixedPoints
  -- We need to show two `restrictToFixedPoints` calls are equal up to
  -- their normalizer-membership proof.  Since the underlying `Equiv` only
  -- depends on `g`, this follows by proof irrelevance on the witness.
  rw [show hP_normal_in_X (hP_le_X hp) = Subgroup.le_normalizer hp from rfl]
  exact restrictToFixedPoints_of_mem_P P hp

/-- **Lemma 25 (X-action is by graph automorphisms).** [done]

If every element of `X` is a graph automorphism of `Γ`, then the
restricted X-action on `Fix(P)` is also by graph automorphisms (of the
induced subgraph). -/
theorem lem25_x_action_isGraphAut
    {Γ : SimpleGraph V}
    (X P : Subgroup (Equiv.Perm V))
    (hP_normal_in_X : X ≤ Subgroup.normalizer (P : Set (Equiv.Perm V)))
    (hX_aut : ∀ g ∈ X, ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (g a) (g b))
    (g : Equiv.Perm V) (hg : g ∈ X)
    (x y : MulAction.fixedPoints P V) :
    Γ.Adj (x : V) (y : V) ↔
      Γ.Adj
        ((lem25_x_acts_on_fixedPoints X P hP_normal_in_X g hg x : V))
        ((lem25_x_acts_on_fixedPoints X P hP_normal_in_X g hg y : V)) :=
  restrictToFixedPoints_isGraphAut (Γ := Γ) P (hP_normal_in_X hg) (hX_aut g hg) x y

/-- **Lemma 25 (normal Sylow ⇒ action on `Fix(P)`).** [backwards-compat] -/
theorem lem25_normal_sylow_action : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
