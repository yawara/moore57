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

/-- **Lemma 5 (3) (characteristic polynomial divides).** [deferred-heavy] -/
theorem lem5_charpoly_dvd (hΓ : IsMoore57 Γ)
    {ι : Type*} [Fintype ι] (P : EquitablePartition Γ ι) :
    True := by trivial

/-- **Lemma 5 (4) (entries of `Bᵏ` count `k`-walks).** [deferred-heavy] -/
theorem lem5_walks (hΓ : IsMoore57 Γ)
    {ι : Type*} [Fintype ι] (P : EquitablePartition Γ ι) (k : ℕ) :
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

/-- **Lemma 5 (5) helper: `|cN(v, w)|` as a filter cardinality over `V`.** -/
private theorem cN_card_eq_filter (v w : V) :
    Fintype.card (Γ.commonNeighbors v w) =
      ((Finset.univ : Finset V).filter
        (fun x => Γ.Adj v x ∧ Γ.Adj x w)).card := by
  classical
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_commonNeighbors]
  refine ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩

/-- **Lemma 5 (5) (matrix identity `B² + B − 56·I = 1·sᵀ`).**

For a Moore57 equitable partition with non-empty cells, the entrywise
matrix identity `(B²)_{ij} + B_{ij} = 56·δ_{ij} + sⱼ` holds.

Proof: sum the pointwise Moore57 SRG identity (`lem5_pointwise_srg`)
over `w ∈ Sⱼ`, for a fixed `v ∈ Sᵢ`.  The LHS resolves into `(B²)_{ij}`
via swap-of-sums and the equitable property applied twice; the RHS
resolves into `56·[i = j] + sⱼ` via cell disjointness. -/
theorem lem5_matrix_identity (hΓ : IsMoore57 Γ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : EquitablePartition Γ ι)
    (h_nonempty : ∀ i, (P.cell i).Nonempty)
    (i j : ι) :
    (∑ k : ι, P.adjMatrix i k * P.adjMatrix k j) + P.adjMatrix i j =
      56 * (if i = j then 1 else 0) + P.cellSize j := by
  classical
  -- Pick `v ∈ Sᵢ`.
  obtain ⟨v, hv⟩ := h_nonempty i
  -- Sum the pointwise SRG identity over `w ∈ P.cell j`.
  have hsum := Finset.sum_congr rfl
    (fun w (_ : w ∈ P.cell j) => lem5_pointwise_srg hΓ v w)
  -- ---- RHS computation.
  -- The "v = w" indicator sums to [v ∈ P.cell j] = [i = j].
  have hsum_eq :
      (∑ w ∈ P.cell j, (if v = w then (1 : ℕ) else 0)) =
        (if i = j then 1 else 0) := by
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      rw [Finset.sum_eq_single v]
      · rw [if_pos rfl]
      · intro w _ hw_ne_v
        exact if_neg (fun h => hw_ne_v h.symm)
      · intro h
        exact (h hv).elim
    · rw [if_neg hij]
      apply Finset.sum_eq_zero
      intro w hw
      apply if_neg
      intro heq
      subst heq
      have hdisj : Disjoint (P.cell i) (P.cell j) :=
        P.pairwise_disjoint (Finset.mem_coe.mpr (Finset.mem_univ i))
          (Finset.mem_coe.mpr (Finset.mem_univ j)) hij
      exact (Finset.disjoint_left.mp hdisj) hv hw
  have hRHS_eq :
      ∑ w ∈ P.cell j, (56 * (if v = w then (1 : ℕ) else 0) + 1) =
        56 * (if i = j then 1 else 0) + P.cellSize j := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul,
        Nat.mul_one, hsum_eq]
    rfl
  -- ---- LHS computation.
  have hLHS_split :
      ∑ w ∈ P.cell j,
        (Fintype.card (Γ.commonNeighbors v w) +
          (if Γ.Adj v w then (1 : ℕ) else 0)) =
      (∑ w ∈ P.cell j, Fintype.card (Γ.commonNeighbors v w)) +
        (∑ w ∈ P.cell j, if Γ.Adj v w then (1 : ℕ) else 0) :=
    Finset.sum_add_distrib
  -- The B_{ij} term.
  have hLHS_B :
      (∑ w ∈ P.cell j, if Γ.Adj v w then (1 : ℕ) else 0) = P.adjMatrix i j := by
    rw [← Finset.card_filter]
    exact P.equitable i j v hv
  -- The (B²)_{ij} term.
  have hLHS_Bsq :
      (∑ w ∈ P.cell j, Fintype.card (Γ.commonNeighbors v w)) =
        ∑ k : ι, P.adjMatrix i k * P.adjMatrix k j := by
    -- Step A: rewrite each card cN as filter card.
    have step_a :
        (∑ w ∈ P.cell j, Fintype.card (Γ.commonNeighbors v w)) =
          ∑ w ∈ P.cell j,
            ((Finset.univ : Finset V).filter
              (fun x => Γ.Adj v x ∧ Γ.Adj x w)).card := by
      refine Finset.sum_congr rfl (fun w _ => ?_)
      exact cN_card_eq_filter v w
    -- Step B: filter card as sum-of-indicators.
    have step_b :
        (∑ w ∈ P.cell j,
            ((Finset.univ : Finset V).filter
              (fun x => Γ.Adj v x ∧ Γ.Adj x w)).card) =
          ∑ w ∈ P.cell j, ∑ x : V,
            if Γ.Adj v x ∧ Γ.Adj x w then (1 : ℕ) else 0 := by
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [Finset.card_filter]
    -- Step C: swap sum order.
    have step_c :
        (∑ w ∈ P.cell j, ∑ x : V,
            if Γ.Adj v x ∧ Γ.Adj x w then (1 : ℕ) else 0) =
          ∑ x : V, ∑ w ∈ P.cell j,
            if Γ.Adj v x ∧ Γ.Adj x w then (1 : ℕ) else 0 :=
      Finset.sum_comm
    -- Step D: split by `adj v x`.
    have step_d :
        (∑ x : V, ∑ w ∈ P.cell j,
            if Γ.Adj v x ∧ Γ.Adj x w then (1 : ℕ) else 0) =
          ∑ x : V,
            (if Γ.Adj v x then (1 : ℕ) else 0) *
              ((P.cell j).filter (fun w => Γ.Adj x w)).card := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hadj_vx : Γ.Adj v x
      · rw [if_pos hadj_vx, Nat.one_mul, Finset.card_filter]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        simp [hadj_vx]
      · rw [if_neg hadj_vx, Nat.zero_mul]
        apply Finset.sum_eq_zero
        intro w _
        simp [hadj_vx]
    -- Step E: partition x by cells.
    have step_e :
        (∑ x : V,
            (if Γ.Adj v x then (1 : ℕ) else 0) *
              ((P.cell j).filter (fun w => Γ.Adj x w)).card) =
          ∑ k : ι, ∑ x ∈ P.cell k,
            (if Γ.Adj v x then (1 : ℕ) else 0) *
              ((P.cell j).filter (fun w => Γ.Adj x w)).card := by
      conv_lhs => rw [show (Finset.univ : Finset V) =
        (Finset.univ : Finset ι).biUnion P.cell from P.covers.symm]
      rw [Finset.sum_biUnion P.pairwise_disjoint]
    -- Step F: apply equitable on the inner filter card.
    have step_f :
        (∑ k : ι, ∑ x ∈ P.cell k,
            (if Γ.Adj v x then (1 : ℕ) else 0) *
              ((P.cell j).filter (fun w => Γ.Adj x w)).card) =
          ∑ k : ι, ∑ x ∈ P.cell k,
            (if Γ.Adj v x then (1 : ℕ) else 0) * P.adjMatrix k j := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun x hx => ?_)
      congr 1
      exact P.equitable k j x hx
    -- Step G: factor out adjMatrix k j and resolve inner sum via equitable on v.
    have step_g :
        (∑ k : ι, ∑ x ∈ P.cell k,
            (if Γ.Adj v x then (1 : ℕ) else 0) * P.adjMatrix k j) =
          ∑ k : ι, P.adjMatrix i k * P.adjMatrix k j := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hinner :
          (∑ x ∈ P.cell k, (if Γ.Adj v x then (1 : ℕ) else 0)) =
            P.adjMatrix i k := by
        rw [← Finset.card_filter]
        exact P.equitable i k v hv
      rw [← Finset.sum_mul, hinner]
    rw [step_a, step_b, step_c, step_d, step_e, step_f, step_g]
  -- Combine.
  calc (∑ k : ι, P.adjMatrix i k * P.adjMatrix k j) + P.adjMatrix i j
      = (∑ w ∈ P.cell j, Fintype.card (Γ.commonNeighbors v w)) +
          (∑ w ∈ P.cell j, if Γ.Adj v w then (1 : ℕ) else 0) := by
        rw [hLHS_Bsq, hLHS_B]
    _ = ∑ w ∈ P.cell j,
          (Fintype.card (Γ.commonNeighbors v w) +
            (if Γ.Adj v w then (1 : ℕ) else 0)) := hLHS_split.symm
    _ = ∑ w ∈ P.cell j, (56 * (if v = w then (1 : ℕ) else 0) + 1) := hsum
    _ = 56 * (if i = j then 1 else 0) + P.cellSize j := hRHS_eq

end Moore57.Papers.MacajSiran2010.S3
