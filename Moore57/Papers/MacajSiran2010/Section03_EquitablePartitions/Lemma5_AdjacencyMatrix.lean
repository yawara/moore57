import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Lemma 5 [skeleton]

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

/-- **Lemma 5 (1) (reciprocal counts).** [skeleton] -/
theorem lem5_reciprocal (hΓ : IsMoore57 Γ)
    {ι : Type*} [Fintype ι] (P : EquitablePartition Γ ι) :
    True := by trivial

/-- **Lemma 5 (2) (57 as eigenvalue).** [skeleton] -/
theorem lem5_eigenvalue_57 (hΓ : IsMoore57 Γ)
    {ι : Type*} [Fintype ι] (P : EquitablePartition Γ ι) :
    True := by trivial

/-- **Lemma 5 (3) (characteristic polynomial divides).** [skeleton] -/
theorem lem5_charpoly_dvd (hΓ : IsMoore57 Γ)
    {ι : Type*} [Fintype ι] (P : EquitablePartition Γ ι) :
    True := by trivial

/-- **Lemma 5 (4) (entries of `Bᵏ` count `k`-walks).** [skeleton] -/
theorem lem5_walks (hΓ : IsMoore57 Γ)
    {ι : Type*} [Fintype ι] (P : EquitablePartition Γ ι) (k : ℕ) :
    True := by trivial

/-- **Lemma 5 (5) (matrix identity `B² + B − 56 I = 1ᵀ · s`).** [skeleton] -/
theorem lem5_matrix_identity (hΓ : IsMoore57 Γ)
    {ι : Type*} [Fintype ι] (P : EquitablePartition Γ ι) :
    True := by trivial

end Moore57.Papers.MacajSiran2010.S3
