import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Logic.Equiv.Defs
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Moore57Definition
import Moore57.Foundations.GroupAction.FixedPoints

/-!
# 固定部分グラフのデータ構造 (Tier 2)

自然言語証明 `proofs/no_aut_order_22_moore57.md` が外部入力として使う 2 つの事実
(Fix(σ) ≅ C_5, Fix(τ) ≅ K_{1,55}) を「データ束」として保持する構造体を定義する.

これらの構造体は単にデータの形を規定するもので, それ自身として実在するかは
問わない. 利用側 (`Order22OnMoore57`) は `structure` のフィールドとしてこの
データを取り込み, conditional theorem を構築する.

* `C5FixedData Γ σ` — σ の固定点集合が `Γ` 内で 5-cycle を成すデータ.
  自然言語証明の §1 で使う `u, a, b, c, d` に対応.

* `K155FixedData Γ τ` — τ の固定点集合が `Γ` 内で星グラフ K_{1,55} を成す
  データ. 中心 1 頂点と 55 個の葉.
-/

namespace Moore57

variable {V : Type*}

/-! ## C_5 fixed subgraph data -/

/-- 自己同型 `σ` の固定点集合が `Γ` 内で 5-cycle として実現される,
というデータ.

フィールド:
* `v : Fin 5 → V` — 5 個の固定点. インデックスは循環順 (0-1-2-3-4-0).
* `v_injective` — 5 頂点は相異.
* `v_fixed` — σ は各頂点を固定.
* `span` — それ以外の固定点は無い.
* `cycle_adj` — 循環隣接: v(i) - v(i+1) が辺 (mod 5).
* `cycle_only` — 5 頂点間の辺は循環辺のみ.

`v 0, v 1, v 2, v 3, v 4` はそれぞれ自然言語証明の `u, a, b, c, d` に対応. -/
structure C5FixedData (Γ : SimpleGraph V) (σ : Equiv.Perm V) where
  /-- 5-cycle 上の頂点 (循環順). -/
  v : Fin 5 → V
  /-- 5 頂点は相異なる. -/
  v_injective : Function.Injective v
  /-- σ は 5 頂点を固定する. -/
  v_fixed : ∀ i : Fin 5, σ (v i) = v i
  /-- σ の固定点は `v` の像に含まれる. -/
  span : ∀ x : V, σ x = x → ∃ i : Fin 5, x = v i
  /-- v(i) と v(i+1) は隣接 (循環辺). -/
  cycle_adj : ∀ i : Fin 5, Γ.Adj (v i) (v (i + 1))
  /-- 5 頂点間の隣接は循環辺のみ. -/
  cycle_only : ∀ i j : Fin 5, Γ.Adj (v i) (v j) → (j = i + 1 ∨ j = i - 1)

namespace C5FixedData

variable {Γ : SimpleGraph V} {σ : Equiv.Perm V}

/-- 自然言語証明の `u` に対応する頂点. -/
def u (h : C5FixedData Γ σ) : V := h.v 0

/-- 自然言語証明の `a` に対応する頂点. -/
def a (h : C5FixedData Γ σ) : V := h.v 1

/-- 自然言語証明の `b` に対応する頂点. -/
def b (h : C5FixedData Γ σ) : V := h.v 2

/-- 自然言語証明の `c` に対応する頂点. -/
def c (h : C5FixedData Γ σ) : V := h.v 3

/-- 自然言語証明の `d` に対応する頂点. -/
def d (h : C5FixedData Γ σ) : V := h.v 4

/-- **Pentagon induced degree**: each `v i` has exactly 2 neighbours among
the 4 other indexed fixed vertices (namely `v (i+1)` and `v (i-1)`).

This is the C₅ induced-degree fact: pentagon is 2-regular. -/
theorem induced_degree_two [DecidableRel Γ.Adj] (h : C5FixedData Γ σ)
    (i : Fin 5) :
    ((Finset.univ : Finset (Fin 5)).filter (fun j => Γ.Adj (h.v i) (h.v j))).card
      = 2 := by
  have hset :
      ((Finset.univ : Finset (Fin 5)).filter (fun j => Γ.Adj (h.v i) (h.v j)))
        = {i + 1, i - 1} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
               Finset.mem_singleton]
    constructor
    · intro hadj
      exact h.cycle_only i j hadj
    · rintro (rfl | rfl)
      · exact h.cycle_adj i
      · have := h.cycle_adj (i - 1)
        rw [sub_add_cancel] at this
        exact this.symm
  rw [hset]
  have hne : (i + 1 : Fin 5) ≠ i - 1 := by
    fin_cases i <;> decide
  rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]

/-- **C₅ bridge to `autFixedNeighborFinset`**: for σ with `C5FixedData`,
the σ-fixed neighbour count at any of the 5 fixed vertices equals `2`. -/
theorem autFixedNeighborFinset_card_eq_two
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (h : C5FixedData Γ σ) (i : Fin 5) :
    (autFixedNeighborFinset Γ σ (h.v i)).card = 2 := by
  have heq :
      autFixedNeighborFinset Γ σ (h.v i)
        = ((Finset.univ : Finset (Fin 5)).filter
            (fun j => Γ.Adj (h.v i) (h.v j))).image h.v := by
    ext w
    simp only [mem_autFixedNeighborFinset, Finset.mem_image, Finset.mem_filter,
               Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hadj, hfix⟩
      obtain ⟨j, hj⟩ := h.span w hfix
      exact ⟨j, hj ▸ hadj, hj.symm⟩
    · rintro ⟨j, hadj, rfl⟩
      exact ⟨hadj, h.v_fixed j⟩
  rw [heq, Finset.card_image_of_injective _ h.v_injective]
  exact h.induced_degree_two i

/-- **C₅ `fixedVertexCount = 5`**: the σ-fixed-vertex count equals `5`. -/
theorem fixedVertexCount_eq_5
    [Fintype V] [DecidableEq V] (h : C5FixedData Γ σ) :
    fixedVertexCount σ = 5 := by
  unfold fixedVertexCount
  have heq :
      ((Finset.univ : Finset V).filter (fun w => σ w = w))
        = (Finset.univ : Finset (Fin 5)).image h.v := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hfix
      obtain ⟨i, hi⟩ := h.span w hfix
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      exact h.v_fixed i
  rw [heq, Finset.card_image_of_injective _ h.v_injective, Finset.card_univ,
      Fintype.card_fin]

/-- **C₅ complement neighbour count**: for σ with `C5FixedData` on a
Moore57 graph, the σ-moved neighbour count at any of the 5 fixed vertices
equals `55 = 57 − 2`.

This is the §6 Lem 18 case (2) (Pentagon) semi-regular orbit input:
σ acts on a 55-element set, and the orbit-stabilizer argument gives
`orderOf σ ∣ 55`, which combined with `orderOf σ = 5^k` gives
`orderOf σ ∣ 5`. -/
theorem c5FixedData_complement_neighbor_count
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (h : C5FixedData Γ σ) (i : Fin 5) :
    ((Γ.neighborFinset (h.v i)).filter (fun w => σ w ≠ w)).card = 55 := by
  have h57 : (Γ.neighborFinset (h.v i)).card = 57 := by
    have := hΓ.regular.degree_eq (h.v i)
    rwa [SimpleGraph.degree] at this
  have h2 : ((Γ.neighborFinset (h.v i)).filter (fun w => σ w = w)).card = 2 :=
    h.autFixedNeighborFinset_card_eq_two i
  have hsum := Finset.card_filter_add_card_filter_not (s := Γ.neighborFinset (h.v i))
    (p := fun w => σ w = w)
  change ((Γ.neighborFinset (h.v i)).filter (fun w => ¬ σ w = w)).card = 55
  omega

end C5FixedData

/-! ## K_{1,55} fixed subgraph data -/

/-- 自己同型 `τ` の固定点集合が `Γ` 内で星グラフ K_{1,55} として実現される,
というデータ.

フィールド:
* `center : V` — 星の中心頂点.
* `leaf : Fin 55 → V` — 55 個の葉頂点.
* `center_ne_leaf`, `leaf_injective` — 56 頂点はすべて相異.
* `center_fixed`, `leaf_fixed` — τ はすべて固定.
* `span` — それ以外の固定点は無い.
* `adj_center` — 中心と各葉は隣接.
* `no_leaf_leaf` — 葉同士は非隣接.

自然言語証明の §5 (involution) で `τ` の固定星として使う. -/
structure K155FixedData (Γ : SimpleGraph V) (τ : Equiv.Perm V) where
  /-- 星の中心. -/
  center : V
  /-- 葉 55 個. -/
  leaf : Fin 55 → V
  /-- 中心は葉ではない. -/
  center_ne_leaf : ∀ i : Fin 55, center ≠ leaf i
  /-- 葉は相異なる. -/
  leaf_injective : Function.Injective leaf
  /-- τ は中心を固定. -/
  center_fixed : τ center = center
  /-- τ は各葉を固定. -/
  leaf_fixed : ∀ i : Fin 55, τ (leaf i) = leaf i
  /-- τ の固定点は中心または葉のいずれか. -/
  span : ∀ x : V, τ x = x → x = center ∨ ∃ i : Fin 55, x = leaf i
  /-- 中心と各葉は隣接. -/
  adj_center : ∀ i : Fin 55, Γ.Adj center (leaf i)
  /-- 葉同士は非隣接 (= star の特性). -/
  no_leaf_leaf : ∀ i j : Fin 55, ¬ Γ.Adj (leaf i) (leaf j)

namespace K155FixedData

variable {Γ : SimpleGraph V} {τ : Equiv.Perm V}

/-- **K_{1,55} center bridge**: at the centre vertex, the τ-fixed neighbour
count equals `55` (= number of leaves).

The 55 leaves are exactly the fixed neighbours of the centre. -/
theorem autFixedNeighborFinset_card_center_eq_55
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (h : K155FixedData Γ τ) :
    (autFixedNeighborFinset Γ τ h.center).card = 55 := by
  have heq :
      autFixedNeighborFinset Γ τ h.center
        = (Finset.univ : Finset (Fin 55)).image h.leaf := by
    ext w
    simp only [mem_autFixedNeighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hadj, hfix⟩
      rcases h.span w hfix with rfl | ⟨i, rfl⟩
      · exact absurd hadj (SimpleGraph.irrefl Γ)
      · exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨h.adj_center i, h.leaf_fixed i⟩
  rw [heq, Finset.card_image_of_injective _ h.leaf_injective, Finset.card_univ,
      Fintype.card_fin]

/-- **K_{1,55} leaf bridge**: at each leaf vertex, the τ-fixed neighbour
count equals `1` (= just the centre).

Other leaves are non-adjacent (`no_leaf_leaf`), so the centre is the unique
fixed neighbour of any leaf. -/
theorem autFixedNeighborFinset_card_leaf_eq_one
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (h : K155FixedData Γ τ) (i : Fin 55) :
    (autFixedNeighborFinset Γ τ (h.leaf i)).card = 1 := by
  have heq :
      autFixedNeighborFinset Γ τ (h.leaf i) = {h.center} := by
    ext w
    simp only [mem_autFixedNeighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hadj, hfix⟩
      rcases h.span w hfix with rfl | ⟨j, rfl⟩
      · rfl
      · exact absurd hadj (h.no_leaf_leaf i j)
    · rintro rfl
      exact ⟨(h.adj_center i).symm, h.center_fixed⟩
  rw [heq]
  exact Finset.card_singleton h.center

/-- **K_{1,55} centre complement count**: for `τ` involution with
`K155FixedData` on Moore57, `|N(centre) \ Fix(τ)| = 2 = 57 − 55`.

Combined with τ being a τ²=1 involution acting semi-regularly on the
2-element complement, gives orbit size 2 ⟹ orderOf τ ∣ 2. -/
theorem k155FixedData_complement_center_count
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (h : K155FixedData Γ τ) :
    ((Γ.neighborFinset h.center).filter (fun w => τ w ≠ w)).card = 2 := by
  have h57 : (Γ.neighborFinset h.center).card = 57 := by
    have := hΓ.regular.degree_eq h.center
    rwa [SimpleGraph.degree] at this
  have h55 : ((Γ.neighborFinset h.center).filter (fun w => τ w = w)).card = 55 :=
    h.autFixedNeighborFinset_card_center_eq_55
  have hsum := Finset.card_filter_add_card_filter_not (s := Γ.neighborFinset h.center)
    (p := fun w => τ w = w)
  change ((Γ.neighborFinset h.center).filter (fun w => ¬ τ w = w)).card = 2
  omega

/-- **K_{1,55} `fixedVertexCount = 56`**: the τ-fixed-vertex count equals
`56 = 1 + 55` (centre + leaves). -/
theorem fixedVertexCount_eq_56
    [Fintype V] [DecidableEq V] (h : K155FixedData Γ τ) :
    fixedVertexCount τ = 56 := by
  unfold fixedVertexCount
  -- Fix(τ) = {center} ∪ image(leaf) (disjoint union by center_ne_leaf)
  have hcenter_not_image :
      h.center ∉ (Finset.univ : Finset (Fin 55)).image h.leaf := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨i, hi⟩
    exact h.center_ne_leaf i hi.symm
  have heq :
      ((Finset.univ : Finset V).filter (fun w => τ w = w))
        = insert h.center ((Finset.univ : Finset (Fin 55)).image h.leaf) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
               Finset.mem_image]
    constructor
    · intro hfix
      rcases h.span w hfix with rfl | ⟨i, hi⟩
      · left; rfl
      · right; exact ⟨i, hi.symm⟩
    · rintro (rfl | ⟨i, rfl⟩)
      · exact h.center_fixed
      · exact h.leaf_fixed i
  rw [heq, Finset.card_insert_of_notMem hcenter_not_image,
      Finset.card_image_of_injective _ h.leaf_injective, Finset.card_univ,
      Fintype.card_fin]

/-- **K_{1,55} leaf complement count**: for `τ` involution with `K155FixedData`
on Moore57, `|N(leaf i) \ Fix(τ)| = 56 = 57 − 1`. -/
theorem k155FixedData_complement_leaf_count
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (h : K155FixedData Γ τ) (i : Fin 55) :
    ((Γ.neighborFinset (h.leaf i)).filter (fun w => τ w ≠ w)).card = 56 := by
  have h57 : (Γ.neighborFinset (h.leaf i)).card = 57 := by
    have := hΓ.regular.degree_eq (h.leaf i)
    rwa [SimpleGraph.degree] at this
  have h1 : ((Γ.neighborFinset (h.leaf i)).filter (fun w => τ w = w)).card = 1 :=
    h.autFixedNeighborFinset_card_leaf_eq_one i
  have hsum := Finset.card_filter_add_card_filter_not (s := Γ.neighborFinset (h.leaf i))
    (p := fun w => τ w = w)
  change ((Γ.neighborFinset (h.leaf i)).filter (fun w => ¬ τ w = w)).card = 56
  omega

end K155FixedData

end Moore57
