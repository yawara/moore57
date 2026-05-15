import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# 固定部分グラフのデータ構造 (Tier 2)

自然言語証明 `no_aut_order_22_moore57.md` が外部入力として使う 2 つの事実
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

end Moore57
