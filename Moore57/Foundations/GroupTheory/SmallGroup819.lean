import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.DeriveFintype

-- `native_decide` is intentional here (see `Moore57/AxiomsCheck.lean`).

set_option linter.style.nativeDecide false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# `SmallGroup(81, 9)` — explicit Lean construction

Mačaj–Širáň 2010 §7 Corollary 2 identifies a hypothetical 3-group `X` of
order 81 acting on a Moore (57, 2)-graph with the GAP small group
`SmallGroup(81, 9)`.  Their proof goes by inspecting subgroup lattices of
all 15 groups of order 81 in GAP.

This file constructs `SG819` and verifies its GAP-quoted structural
invariants by `native_decide`.

## Construction

`SG819` is the split extension `(Z₉ × Z₃) ⋊ Z₃`, where the outer `Z₃`
acts on the normal `Z₉ × Z₃` via the order-`3` automorphism
`ψ(a, b) = (a + 3b, -a + b)`  (where `-a` is reduced `mod 3`).  The key
property of `ψ` is that it satisfies the *Eisenstein relation*
`1 + ψ + ψ² = 0` as an endomorphism of `Z₉ × Z₃`; one can check
`ψ²(a, b) = (7a + 6b, a + b)` and verify
`ψ(a, b) + ψ²(a, b) + (a, b) = (a + a + 3b + 7a + 6b, -a + b + a + b + b)
= (9a + 9b, 3b) = (0, 0)`.

This Eisenstein relation makes every element of `SG819 \ Y` (where
`Y = Z₉ × Z₃` is the normal subgroup at `c = 0`) order `3`.  Indeed for
any `c ≠ 0` and `(a, b) ∈ Z₉ × Z₃`:
`(a, b, c)³ = ((1 + ψ + ψ²)(a, b), 0) = (0, 0, 0)`.

The two cosets `c = 1, c = 2` contribute `27 + 27 = 54` order-`3`
elements; together with the `8` order-`3` elements of `Y` we obtain `62`
order-`3` elements (matching the Mačaj–Širáň count of `31`
order-`3` subgroups — see `card_orderEq_three` below).

We represent elements as triples `⟨a, b, c⟩ ∈ Z₉ × Z₃ × Z₃` with
multiplication
`⟨a₁, b₁, c₁⟩ * ⟨a₂, b₂, c₂⟩ = ⟨(a₁, b₁) + ψ^{c₁}(a₂, b₂), c₁ + c₂⟩`.

## Status

The construction matches the GAP-quoted element-order distribution of
`SmallGroup(81, 9)` (62 elements of order 3, 18 of order 9; cf.
`card_orderEq_three` and `card_orderEq_nine`).  A formal isomorphism to
GAP's `SmallGroup(81, 9)` is not yet established in Lean.

## References

* Mačaj, J. Širáň, *Search for properties of the missing Moore graph*,
  Linear Algebra Appl. 432 (2010) 2381–2398, §7.
* GAP `SmallGroups` library, group `(81, 9)`.
-/

namespace Moore57.Foundations.GroupTheory

/-- `SmallGroup(81, 9)`: the 3-group `(Z₉ × Z₃) ⋊ Z₃` where the outer
`Z₃` acts via the Eisenstein-type automorphism `ψ(a, b) = (a + 3b, -a + b)`. -/
structure SG819 where
  /-- The `a`-generator (lives in the `Z₉` factor of the normal subgroup `Y`). -/
  a : ZMod 9
  /-- The `b`-generator (lives in the `Z₃` factor of the normal subgroup `Y`). -/
  b : ZMod 3
  /-- The `c`-generator (the quotient `Z₃`). -/
  c : ZMod 3
  deriving DecidableEq, Fintype

namespace SG819

/-- Cast `ZMod 9 → ZMod 3`. -/
private def cast93 (a : ZMod 9) : ZMod 3 := (a.val : ZMod 3)

/-- Cast `ZMod 3 → ZMod 9` (lifts `b ↦ b ∈ {0, 1, 2} ⊂ Z/9`). -/
private def cast39 (b : ZMod 3) : ZMod 9 := (b.val : ZMod 9)

/-- The `ZMod 9`-component of `ψ^c(a, b)`. -/
private def actA (c : ZMod 3) (a : ZMod 9) (b : ZMod 3) : ZMod 9 :=
  match c.val with
  | 0 => a
  | 1 => a + 3 * cast39 b
  | _ => 7 * a + 6 * cast39 b

/-- The `ZMod 3`-component of `ψ^c(a, b)`. -/
private def actB (c : ZMod 3) (a : ZMod 9) (b : ZMod 3) : ZMod 3 :=
  match c.val with
  | 0 => b
  | 1 => -(cast93 a) + b
  | _ => cast93 a + b

/-- Multiplication: encodes the semidirect-product law. -/
instance : Mul SG819 where
  mul g h := ⟨g.a + actA g.c h.a h.b, g.b + actB g.c h.a h.b, g.c + h.c⟩

/-- Identity element `⟨0, 0, 0⟩`. -/
instance : One SG819 where one := ⟨0, 0, 0⟩

/-- Inverse: `⟨a, b, c⟩⁻¹ = ⟨ψ^{-c}(-a, -b), -c⟩`. -/
instance : Inv SG819 where
  inv g := ⟨actA (-g.c) (-g.a) (-g.b), actB (-g.c) (-g.a) (-g.b), -g.c⟩

/-- The group instance, with the four axioms verified by `native_decide`
(81 elements — the worst case is `mul_assoc` with `81³ = 531 441` cases,
beyond what kernel `decide` can handle within the default recursion depth). -/
instance : Group SG819 where
  mul_assoc := by native_decide
  one_mul := by native_decide
  mul_one := by native_decide
  inv_mul_cancel := by native_decide

/-- `|SG819| = 81`. -/
theorem card_eq : Fintype.card SG819 = 81 := by decide

/-! ### Structural invariants (verified by `native_decide`).

The following lemmas record the GAP-quoted invariants of `SmallGroup(81, 9)`
that distinguish it from the other 14 groups of order 81. -/

/-- Number of elements `g` with `g³ = 1` (the order-`≤ 3` subgroup
quoted by Mačaj–Širáň as having order `27`). -/
theorem card_orderDvd_three :
    (Finset.univ.filter (fun g : SG819 => g ^ 3 = 1)).card = 63 := by
  native_decide

/-- Number of (strict) order-`3` elements; matches the
Mačaj–Širáň count `31 · 2 = 62`. -/
theorem card_orderEq_three :
    (Finset.univ.filter (fun g : SG819 => g ^ 3 = 1 ∧ g ≠ 1)).card = 62 := by
  native_decide

/-- Number of order-`9` elements (everything not of order `≤ 3`). -/
theorem card_orderEq_nine :
    (Finset.univ.filter (fun g : SG819 => g ^ 3 ≠ 1)).card = 18 := by
  native_decide

/-- `SG819` is not abelian. -/
theorem not_commutative : ¬ ∀ g h : SG819, g * h = h * g := by native_decide

/-- The centre has order `3`.  In the paper's notation, the centre is
the unique order-`3` subgroup whose conjugacy class is a singleton. -/
theorem card_center :
    (Finset.univ.filter (fun g : SG819 => ∀ h, g * h = h * g)).card = 3 := by
  native_decide

/-! ### Subgroup-of-order-`3` conjugacy class structure

We represent each order-`3` subgroup as its underlying `Finset SG819`
(namely `{1, x, x²}` for any non-identity `x` of order `3`).  This is
the canonical computational representation usable by `native_decide`. -/

/-- The order-`3` subgroup generated by `x` as a `Finset SG819`. -/
def sub3 (x : SG819) : Finset SG819 := {1, x, x * x}

/-- The collection of all order-`3` subgroups, indexed by their underlying
`Finset`.  Each appears once because the canonical representation deduplicates
the two generators `{x, x²}` of a given cyclic subgroup. -/
def allSub3 : Finset (Finset SG819) :=
  (Finset.univ.filter (fun g : SG819 => g ^ 3 = 1 ∧ g ≠ 1)).image sub3

/-- The conjugate of a subgroup `H` by `g`. -/
def conjSub3 (g : SG819) (H : Finset SG819) : Finset SG819 :=
  H.image (fun x => g * x * g⁻¹)

/-- The conjugacy class of an order-`3` subgroup `H`. -/
def classSub3 (H : Finset SG819) : Finset (Finset SG819) :=
  Finset.univ.image (fun g : SG819 => conjSub3 g H)

/-- Number of order-`3` subgroups, matching the GAP count `31 = 1 + 3 + 9 + 9 + 9`. -/
theorem card_allSub3 : allSub3.card = 31 := by native_decide

/-- Number of order-`3` subgroups whose conjugacy-class size is `1`
(i.e., the central order-`3` subgroup). -/
theorem class_size_1_count :
    (allSub3.filter (fun H => (classSub3 H).card = 1)).card = 1 := by
  native_decide

/-- Number of order-`3` subgroups whose conjugacy-class size is `3`. -/
theorem class_size_3_count :
    (allSub3.filter (fun H => (classSub3 H).card = 3)).card = 3 := by
  native_decide

/-- Number of order-`3` subgroups whose conjugacy-class size is `9`;
matches `9 + 9 + 9 = 27` (three classes of size 9). -/
theorem class_size_9_count :
    (allSub3.filter (fun H => (classSub3 H).card = 9)).card = 27 := by
  native_decide

/-- The total number of conjugacy classes of order-`3` subgroups is `5`,
matching the Mačaj–Širáň multiset of sizes `1, 3, 9, 9, 9`. -/
theorem num_classes_sub3 :
    (allSub3.image classSub3).card = 5 := by native_decide

/-- The Mačaj–Širáň premise of Corollary 2:  `SG819` has at least two
conjugacy classes of order-`3` subgroups each of size `9`. -/
theorem two_classes_size_9 :
    2 ≤ ((allSub3.image classSub3).filter (fun C => C.card = 9)).card := by
  native_decide

/-! ### Cyclic subgroups of order `9`

The paper states: *"Cyclic subgroups of order 9 form a single conjugacy
class of `X` of size 3"*.  We verify this directly. -/

/-- The cyclic subgroup generated by an order-`9` element `x`. -/
def sub9 (x : SG819) : Finset SG819 :=
  (Finset.range 9).image (fun k => x ^ k)

/-- All order-`9` cyclic subgroups. -/
def allSub9 : Finset (Finset SG819) :=
  (Finset.univ.filter (fun g : SG819 => g ^ 3 ≠ 1)).image sub9

/-- Number of cyclic subgroups of order `9`.  We expect `3` since each
contains `6 = φ(9)` generators and there are `18` order-`9` elements. -/
theorem card_allSub9 : allSub9.card = 3 := by native_decide

/-- All order-`9` subgroups form a single conjugacy class. -/
theorem allSub9_single_class :
    (allSub9.image classSub3).card = 1 := by native_decide

end SG819

end Moore57.Foundations.GroupTheory
