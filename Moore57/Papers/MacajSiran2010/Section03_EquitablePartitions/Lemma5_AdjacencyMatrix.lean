import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Lemma 5

> Let `S = {S₁, …, Sₖ}` be an equitable partition of a Moore (57, 2) graph
> Γ such that `|Sᵢ| = sᵢ` and let `B = (b_{ij})` be the adjacency matrix of
> `S`. Then
>
> (1) `sᵢ b_{i,j} = sⱼ b_{j,i}`;
>
> (2) 57 is an eigenvalue of `B` with eigenvector `(1, 1, …, 1)ᵀ`;
>
> (3) the characteristic polynomial of `B` divides `(x − 57)(x − 7)^{1729}(x + 8)^{1520}`;
>
> (4) coefficients `b^k_{ij}` of `Bᵏ` are numbers of `k`-walks from a vertex
>     of `Sᵢ` into `Sⱼ`;
>
> (5) `B² + B − 56 I = (1, 1, …, 1)ᵀ (s₁, s₂, …, sₖ)`.
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 5 (1) (reciprocal counts).** `sᵢ · b_{i,j} = sⱼ · b_{j,i}`.

Both sides count the number of edges between cells `Sᵢ` and `Sⱼ`:
`|{(v, w) ∈ Sᵢ × Sⱼ : Γ.Adj v w}|`. Combining the equitable-partition
identity with `SimpleGraph.adj_comm` (symmetry of adjacency) gives the
reciprocity. -/
theorem lem5_reciprocal {ι : Type*} [Fintype ι] (P : EquitablePartition Γ ι)
    (i j : ι) :
    P.cellSize i * P.adjMatrix i j = P.cellSize j * P.adjMatrix j i := by
  classical
  -- Edge set between cells i and j.
  set E : Finset (V × V) := ((P.cell i) ×ˢ (P.cell j)).filter
    (fun p => Γ.Adj p.1 p.2) with hE_def
  -- Count E from cell i side: ∑_{v ∈ Sᵢ} |{w ∈ Sⱼ : Adj v w}| = sᵢ · b_{i,j}.
  have hLeft : E.card = P.cellSize i * P.adjMatrix i j := by
    rw [hE_def, Finset.card_filter, Finset.sum_product]
    -- Inner sum is the cardinality of the filter set.
    have inner : ∀ v ∈ P.cell i,
        (∑ w ∈ P.cell j, if Γ.Adj v w then 1 else 0) = P.adjMatrix i j := by
      intro v hv
      rw [← Finset.card_filter]
      exact P.equitable i j v hv
    rw [Finset.sum_congr rfl inner]
    rw [Finset.sum_const, smul_eq_mul]
    rfl
  -- Count E from cell j side: swap order, use adjacency symmetry.
  have hRight : E.card = P.cellSize j * P.adjMatrix j i := by
    rw [hE_def, Finset.card_filter, Finset.sum_product]
    -- Swap order of summation.
    rw [Finset.sum_comm]
    -- Bridge the inner sum to the equitable identity via adj_comm.
    have inner : ∀ w ∈ P.cell j,
        (∑ v ∈ P.cell i, if Γ.Adj v w then (1 : ℕ) else 0) = P.adjMatrix j i := by
      intro w hw
      -- Sum-of-indicator = filter cardinality.
      have hcard : (∑ v ∈ P.cell i, if Γ.Adj v w then (1 : ℕ) else 0) =
          ((P.cell i).filter (fun v => Γ.Adj w v)).card := by
        rw [← Finset.card_filter]
        congr 1
        apply Finset.filter_congr
        intros v _
        exact SimpleGraph.adj_comm Γ v w
      rw [hcard]
      exact P.equitable j i w hw
    rw [Finset.sum_congr rfl inner]
    rw [Finset.sum_const, smul_eq_mul]
    rfl
  rw [← hLeft, hRight]

/-- **Lemma 5 (2) (57 as eigenvalue, row-sum form).**
Each row of `B` sums to 57 (assuming all cells are non-empty). This is the
all-ones eigenvector statement: `B · (1,1,…,1)ᵀ = 57 · (1,1,…,1)ᵀ`. -/
theorem lem5_eigenvalue_57 (hΓ : IsMoore57 Γ)
    {ι : Type*} [Fintype ι] (P : EquitablePartition Γ ι)
    (h_nonempty : ∀ i, (P.cell i).Nonempty) (i : ι) :
    ∑ j : ι, P.adjMatrix i j = 57 := by
  obtain ⟨v, hv⟩ := h_nonempty i
  exact P.row_sum_eq_57 hΓ i hv

/-- **Lemma 5 (3) (characteristic polynomial divides).** [skeleton] -/
theorem lem5_charpoly_dvd (hΓ : IsMoore57 Γ)
    {ι : Type*} [Fintype ι] (P : EquitablePartition Γ ι) :
    True := by trivial

/-- **Lemma 5 (4) (entries of `Bᵏ` count `k`-walks).** [skeleton] -/
theorem lem5_walks (hΓ : IsMoore57 Γ)
    {ι : Type*} [Fintype ι] (P : EquitablePartition Γ ι) (k : ℕ) :
    True := by trivial

/-- **Lemma 5 (5) (matrix identity `B² + B − 56·I = 1·sᵀ`).** [skeleton]

For an equitable partition with cell sizes `s = (s₁, …, sₖ)` and
adjacency matrix `B`, the rank-1 identity
`B² + B − 56·I = 𝟙·sᵀ` holds (entrywise: `(B²)_{ij} + B_{ij} = 56·δ_{ij} + sⱼ`).

Proof outline:
* Pointwise Moore57 SRG identity at `(v, w) ∈ V × V`:
  `|cN(v, w)| + [v ~ w] = 56·[v = w] + 1`.
* Sum over `w ∈ Sⱼ`:
  - LHS sums to `(B²)_{ij} + B_{ij}` by double-counting (decompose the
    intermediate vertex `x` by which cell it lies in, then apply
    `P.equitable` twice).
  - RHS sums to `56·δ_{ij} + sⱼ` (using `v ∈ Sᵢ`, so `v ∈ Sⱼ ⇔ i = j`).

Pointwise SRG step is proven below as `lem5_pointwise_srg`. The
double-sum decomposition is the missing piece. -/
theorem lem5_matrix_identity (hΓ : IsMoore57 Γ)
    {ι : Type*} [Fintype ι] (P : EquitablePartition Γ ι) :
    True := by trivial

/-- **Lemma 5 (5) helper: pointwise Moore57 SRG identity.**

For Moore57 and any `v, w ∈ V`:
`|cN(v, w)| + [v ~ w] = 56·[v = w] + 1`.

Three cases:
* `v = w`: `|cN(v, v)| = degree v = 57`, `[v ~ v] = 0` (loopless),
  `56·1 + 1 = 57`. ✓
* `v ≠ w, v ~ w`: `|cN| = λ = 0` (SRG `of_adj`), `[v ~ w] = 1`,
  `56·0 + 1 = 1`. ✓
* `v ≠ w, v ≁ w`: `|cN| = μ = 1` (SRG `of_not_adj`), `[v ~ w] = 0`,
  `56·0 + 1 = 1`. ✓ -/
theorem lem5_pointwise_srg (hΓ : IsMoore57 Γ) (v w : V) :
    Fintype.card (Γ.commonNeighbors v w) +
      (if Γ.Adj v w then (1 : ℕ) else 0) =
    56 * (if v = w then 1 else 0) + 1 := by
  classical
  by_cases hvw : v = w
  · subst w
    rw [if_pos rfl]
    have hadj : ¬ Γ.Adj v v := Γ.irrefl
    rw [if_neg hadj, Nat.add_zero, Nat.mul_one]
    have hreg : Γ.degree v = 57 := hΓ.regular v
    have hcN : Fintype.card (Γ.commonNeighbors v v) = Γ.degree v := by
      rw [← SimpleGraph.card_neighborSet_eq_degree]
      apply Fintype.card_congr
      refine Equiv.setCongr ?_
      rw [SimpleGraph.commonNeighbors_eq, Set.inter_self]
    rw [hcN, hreg]
  · rw [if_neg hvw]
    by_cases hadj : Γ.Adj v w
    · rw [if_pos hadj, hΓ.of_adj v w hadj]
    · rw [if_neg hadj, hΓ.of_not_adj hvw hadj]

end Moore57.Papers.MacajSiran2010.S3
