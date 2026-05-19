import Moore57.Moore57Graph.Moore57Definition
import Moore57.Moore57Graph.E7Matrix.SpectralDecomposition
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Proposition 1

> The graph Γ has 3250 vertices and girth 5. Its adjacency matrix `A` satisfies the
> equation `A² + A − 56I = J`, where `J` is the all-one matrix. Consequently, its
> eigenvalues are 57, 7, and −8, with multiplicities 1, 1729, and 1520, respectively.

* `prop1_card`        — wrapped from `Moore57.IsMoore57.card` (the `IsSRGWith` field).
* `prop1_adjMatrix_sq_eq` — wrapped from `Moore57.IsMoore57.adjMatrix_sq_eq` (paper form).
* `prop1_eigenvalue_*_mult` — trace of each eigenspace projection equals the
  paper's multiplicity (= dim of eigenspace).
-/

open Moore57

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Proposition 1, vertex count:** `|V| = 3250`. -/
theorem prop1_card (hΓ : IsMoore57 Γ) : Fintype.card V = 3250 :=
  hΓ.card

/-- **Proposition 1, SRG identity in the paper's form:** `A² + A − 56I = J`. -/
theorem prop1_adjMatrix_sq_eq (hΓ : IsMoore57 Γ) :
    Γ.adjMatrix ℚ ^ 2 + Γ.adjMatrix ℚ - (56 : ℚ) • (1 : Matrix V V ℚ) = allOnesMatrix V := by
  have h := hΓ.adjMatrix_sq_eq
  rw [h]
  abel

/-- Helper: the permutation matrix of the identity is the identity matrix. -/
private theorem _permMatrix_one : permMatrix (1 : Equiv.Perm V) = 1 := by
  change ((1 : Equiv.Perm V).symm.toPEquiv).toMatrix = 1
  rw [show ((1 : Equiv.Perm V).symm) = Equiv.refl V from rfl,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

/-- Helper: `fixedVertexCount 1 = |V|`. -/
private theorem _fixedVertexCount_one :
    fixedVertexCount (1 : Equiv.Perm V) = Fintype.card V := by
  classical
  unfold fixedVertexCount
  have hfilter :
      ((Finset.univ : Finset V).filter fun v => (1 : Equiv.Perm V) v = v) = Finset.univ := by
    ext v; simp
  rw [hfilter]
  exact Finset.card_univ

/-- Helper: `adjacentMovedCount Γ 1 = 0`. -/
private theorem _adjacentMovedCount_one :
    adjacentMovedCount Γ (1 : Equiv.Perm V) = 0 := by
  classical
  change ((Finset.univ : Finset V).filter fun v => Γ.Adj v ((1 : Equiv.Perm V) v)).card = 0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _
  change ¬ Γ.Adj v v
  exact SimpleGraph.irrefl Γ

/-- **Proposition 1, eigenvalue 57 multiplicity 1.**
The 57-eigenspace projection `E_57` has trace 1. -/
theorem prop1_eigenvalue_57_mult (hΓ : IsMoore57 Γ) :
    Matrix.trace (E57Matrix V) = (1 : ℚ) := by
  have := trace_E57Matrix_mul_permMatrix (V := V) hΓ 1
  rw [_permMatrix_one, Matrix.mul_one] at this
  exact this

/-- **Proposition 1, eigenvalue 7 multiplicity 1729.**
The 7-eigenspace projection `E_7` has trace 1729. -/
theorem prop1_eigenvalue_7_mult (hΓ : IsMoore57 Γ) :
    Matrix.trace (E7Matrix Γ) = (1729 : ℚ) := by
  have h := hΓ.higman_trace_formula 1
  rw [_permMatrix_one, Matrix.mul_one] at h
  rw [_fixedVertexCount_one, _adjacentMovedCount_one, hΓ.card] at h
  rw [h]
  norm_num

/-- **Proposition 1, eigenvalue −8 multiplicity 1520.**
The −8-eigenspace projection `E_-8` has trace 1520. -/
theorem prop1_eigenvalue_neg8_mult (hΓ : IsMoore57 Γ) :
    Matrix.trace (EMinus8Matrix Γ) = (1520 : ℚ) := by
  have hdecomp := trace_decomp_via_spectral (Γ := Γ) (1 : Equiv.Perm V) 1
  simp only [pow_one, _permMatrix_one, Matrix.mul_one] at hdecomp
  have h57 := prop1_eigenvalue_57_mult (V := V) hΓ
  have h7 := prop1_eigenvalue_7_mult hΓ
  have hP : Matrix.trace (1 : Matrix V V ℚ) = 3250 := by
    rw [Matrix.trace_one, hΓ.card]; norm_num
  have hsum :
      (E57Matrix V).trace + (E7Matrix Γ).trace + (EMinus8Matrix Γ).trace = 3250 := by
    rw [← hdecomp]; exact hP
  have : (EMinus8Matrix Γ).trace =
      3250 - (E57Matrix V).trace - (E7Matrix Γ).trace := by linarith
  rw [this, h57, h7]; norm_num

end Moore57.Papers.MacajSiran2010.S2
