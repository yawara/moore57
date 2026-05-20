import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring

-- `native_decide` is intentional here (see `Moore57/AxiomsCheck.lean`).

set_option linter.style.nativeDecide false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# `SmallGroup(625, 12)` — explicit Lean construction

Mačaj–Širáň 2010 §7 Lemma 22 identifies a hypothetical `5`-group `X` of
order `625` acting on a Moore (57, 2)-graph with the GAP small group
`SmallGroup(625, 12)`.  Their proof goes by inspecting subgroup lattices
of all 14 non-abelian groups of order 625 in GAP.

This file constructs `SG625_12` and verifies its structural invariants
by `native_decide`.

## Construction

`SG625_12` is the direct product `Heis(F₅) × Z₅`, where `Heis(F₅)` is the
order-`125` Heisenberg group over `F₅`.  Elements are quadruples
`⟨a, b, c, d⟩ ∈ (Z₅)⁴` with multiplication
`⟨a₁, b₁, c₁, d₁⟩ * ⟨a₂, b₂, c₂, d₂⟩ = ⟨a₁+a₂, b₁+b₂, c₁+c₂+(a₁b₂−a₂b₁), d₁+d₂⟩`.

The `(a, b)` directions are the Heisenberg generators, `c` is the
commutator-direction (= derived subgroup), and `d` is the direct `Z₅` factor.
A direct computation shows:

* `Z(G) = ⟨(0, 0, 1, 0), (0, 0, 0, 1)⟩` has order `25`.
* `G' = ⟨(0, 0, 1, 0)⟩` has order `5` (and equals the Frattini subgroup
  `Φ(G)` since `G` has exponent `5`).
* Every element has order dividing `5`; only the identity has order `1`.

These match the GAP invariants of `SmallGroup(625, 12)` (all elements of
order `5`, center of order `25`, Frattini subgroup of order `5`).

## Status

The construction matches the GAP-quoted structural invariants of
`SmallGroup(625, 12)`.  A formal isomorphism to GAP's `SmallGroup(625, 12)`
is not yet established in Lean.

## References

* Mačaj, J. Širáň, *Search for properties of the missing Moore graph*,
  Linear Algebra Appl. 432 (2010) 2381–2398, §7, Lemma 22.
* GAP `SmallGroups` library, group `(625, 12)`.
-/

namespace Moore57.Foundations.GroupTheory

/-- `SmallGroup(625, 12)`: the `5`-group `Heis(F₅) × Z₅` of order `625`,
exponent `5`, center order `25`, Frattini order `5`. -/
structure SG625_12 where
  /-- The first Heisenberg generator. -/
  a : ZMod 5
  /-- The second Heisenberg generator. -/
  b : ZMod 5
  /-- The commutator-direction (= derived subgroup generator). -/
  c : ZMod 5
  /-- The direct `Z₅` factor. -/
  d : ZMod 5
  deriving DecidableEq, Fintype

namespace SG625_12

/-- Multiplication: encodes the Heisenberg cocycle in the `c`-coordinate. -/
instance : Mul SG625_12 where
  mul g h := ⟨g.a + h.a, g.b + h.b, g.c + h.c + (g.a * h.b - h.a * g.b),
              g.d + h.d⟩

/-- Identity element `⟨0, 0, 0, 0⟩`. -/
instance : One SG625_12 where one := ⟨0, 0, 0, 0⟩

/-- Inverse: `⟨a, b, c, d⟩⁻¹ = ⟨-a, -b, -c, -d⟩`.  Direct check using
`a · (-b) - (-a) · b = -ab + ab = 0`. -/
instance : Inv SG625_12 where
  inv g := ⟨-g.a, -g.b, -g.c, -g.d⟩

/-- Extensionality for `SG625_12` (coordinate-wise equality). -/
@[ext] theorem ext : ∀ {g h : SG625_12},
    g.a = h.a → g.b = h.b → g.c = h.c → g.d = h.d → g = h
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl, rfl, rfl, rfl => rfl

@[simp] theorem mul_a (g h : SG625_12) : (g * h).a = g.a + h.a := rfl
@[simp] theorem mul_b (g h : SG625_12) : (g * h).b = g.b + h.b := rfl
@[simp] theorem mul_c (g h : SG625_12) :
    (g * h).c = g.c + h.c + (g.a * h.b - h.a * g.b) := rfl
@[simp] theorem mul_d (g h : SG625_12) : (g * h).d = g.d + h.d := rfl

@[simp] theorem one_a : (1 : SG625_12).a = 0 := rfl
@[simp] theorem one_b : (1 : SG625_12).b = 0 := rfl
@[simp] theorem one_c : (1 : SG625_12).c = 0 := rfl
@[simp] theorem one_d : (1 : SG625_12).d = 0 := rfl

@[simp] theorem inv_a (g : SG625_12) : g⁻¹.a = -g.a := rfl
@[simp] theorem inv_b (g : SG625_12) : g⁻¹.b = -g.b := rfl
@[simp] theorem inv_c (g : SG625_12) : g⁻¹.c = -g.c := rfl
@[simp] theorem inv_d (g : SG625_12) : g⁻¹.d = -g.d := rfl

/-- The group instance.  Each axiom reduces to a coordinate-wise
polynomial identity over `ZMod 5`. -/
instance : Group SG625_12 where
  mul_assoc g h k := by
    apply SG625_12.ext
    · show (g * h * k).a = (g * (h * k)).a
      simp only [mul_a]; ring
    · show (g * h * k).b = (g * (h * k)).b
      simp only [mul_b]; ring
    · show (g * h * k).c = (g * (h * k)).c
      simp only [mul_c, mul_a, mul_b]; ring
    · show (g * h * k).d = (g * (h * k)).d
      simp only [mul_d]; ring
  one_mul g := by
    apply SG625_12.ext
    · show (1 * g).a = g.a; simp [mul_a, one_a]
    · show (1 * g).b = g.b; simp [mul_b, one_b]
    · show (1 * g).c = g.c; simp [mul_c, one_a, one_b, one_c]
    · show (1 * g).d = g.d; simp [mul_d, one_d]
  mul_one g := by
    apply SG625_12.ext
    · show (g * 1).a = g.a; simp [mul_a, one_a]
    · show (g * 1).b = g.b; simp [mul_b, one_b]
    · show (g * 1).c = g.c; simp [mul_c, one_a, one_b, one_c]
    · show (g * 1).d = g.d; simp [mul_d, one_d]
  inv_mul_cancel g := by
    apply SG625_12.ext
    · show (g⁻¹ * g).a = (1 : SG625_12).a
      simp only [mul_a, inv_a, one_a]; ring
    · show (g⁻¹ * g).b = (1 : SG625_12).b
      simp only [mul_b, inv_b, one_b]; ring
    · show (g⁻¹ * g).c = (1 : SG625_12).c
      simp only [mul_c, inv_a, inv_b, inv_c, one_c]; ring
    · show (g⁻¹ * g).d = (1 : SG625_12).d
      simp only [mul_d, inv_d, one_d]; ring

/-- `|SG625_12| = 625`. -/
theorem card_eq : Fintype.card SG625_12 = 625 := by native_decide

/-! ### Structural invariants (verified by `native_decide`).

The following lemmas record the GAP-quoted invariants of
`SmallGroup(625, 12)` that distinguish it from the other 13 non-abelian
groups of order `625`. -/

/-- Number of (strict) order-`5` elements; matches `624 = 625 − 1`
(every non-identity element of an exponent-`5` group has order `5`). -/
theorem card_orderEq_five :
    (Finset.univ.filter (fun g : SG625_12 => g ^ 5 = 1 ∧ g ≠ 1)).card = 624 := by
  native_decide

/-- Number of elements `g` with `g⁵ = 1` (i.e., the whole group, since
exponent equals `5`). -/
theorem card_orderDvd_five :
    (Finset.univ.filter (fun g : SG625_12 => g ^ 5 = 1)).card = 625 := by
  native_decide

/-- `SG625_12` is not abelian. -/
theorem not_commutative : ¬ ∀ g h : SG625_12, g * h = h * g := by native_decide

/-- The centre has order `25`.  In the paper's notation, the centre is
the rank-`2` direct summand `⟨f₃, f₄⟩`. -/
theorem card_center :
    (Finset.univ.filter (fun g : SG625_12 => ∀ h, g * h = h * g)).card = 25 := by
  native_decide

/-- The Frattini subgroup (= derived subgroup `G'` for an exponent-`5`
group) has order `5`.

For the Heisenberg-style group `Heis(F₅) × Z₅`, `G'` is the `c`-direction
`⟨(0, 0, 1, 0)⟩`, so we verify the size directly via membership in this
explicit subset (`a = b = d = 0`). -/
theorem card_frattini :
    (Finset.univ.filter
      (fun g : SG625_12 => g.a = 0 ∧ g.b = 0 ∧ g.d = 0)).card = 5 := by
  native_decide

/-- The Frattini subgroup `⟨(0, 0, 1, 0)⟩` is precisely the set of
commutators (since `G` has class `2`, every element of `G'` is a single
commutator).

`(0, 0, k, 0)` is the commutator `[g, h]` of `g = (a, b, 0, 0)` and
`h = (a', b', 0, 0)` with `a·b' − a'·b = k/2 ≡ 3k (mod 5)`. -/
theorem frattini_is_commutator_image :
    ∀ k : ZMod 5,
      ∃ g h : SG625_12, g⁻¹ * h⁻¹ * g * h = ⟨0, 0, k, 0⟩ := by
  native_decide

end SG625_12

end Moore57.Foundations.GroupTheory
