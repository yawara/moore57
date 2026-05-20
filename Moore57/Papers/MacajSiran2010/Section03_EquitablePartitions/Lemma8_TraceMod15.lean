import Mathlib.Data.Int.ModEq
import Moore57.Papers.MacajSiran2010.Section03_EquitablePartitions.Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §3, Lemma 8

> Let `X` have `k` orbits on Γ. Then
> ```
> Tr(X) ≡ −8 (k − 10) (mod 15).
> ```

Proof outline (in paper): the eigenvalues of `X`'s orbit-adjacency matrix are
`57, 7, −8`, with `57` appearing exactly once. If `7` appears with multiplicity
`a` and `−8` with multiplicity `k − 1 − a`, the trace is
`57 + 7a − 8(k − 1 − a) = 65 + 15a − 8k`. Reducing modulo 15 kills the
`15·a` term and shifts `65` to `5 ≡ -8·(0 − 10) (mod 15)`, yielding the
stated congruence.  Any swap of `−8` and `7` changes the trace by `15`,
preserving the mod-15 class.

Status:
* `lem8_trace_eq_spectrum_form` — pure ℤ identity `Tr = 65 + 15a − 8k`
  from the spectrum multiplicities (proven).
* `lem8_trace_mod_fifteen_arithmetic` — `(Tr + 8·(k − 10)) % 15 = 0`
  from the spectrum form (proven).
* `lem8_trace_mod_fifteen_zmod` — `Int.ModEq` notation form (proven).
* `lem8_trace_swap_diff` — swapping one `−8` eigenvalue for `7` changes
  the trace by `15` (proven).
* `lem8_trace_mod_fifteen` — paper-faithful Moore57-conditional stub.
  The geometric step from `IsMoore57 Γ` + X-acts-by-graph-autos to the
  spectrum equation (`Tr = 65 + 15a − 8k`) is [deferred-heavy].
-/

namespace Moore57.Papers.MacajSiran2010.S3

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Spectrum-trace identity.** [done]

For the X-orbit adjacency matrix of a Moore57 graph with `k` orbits,
eigenvalue `57` (multiplicity `1`), `7` (multiplicity `a`), and `−8`
(multiplicity `k − 1 − a`), the trace equals `65 + 15·a − 8·k`.

This packages the algebra `57 + 7·a + (−8)·(k − 1 − a) = 65 + 15·a − 8·k`
as a reusable arithmetic identity (no Moore57 hypothesis). -/
theorem lem8_trace_eq_spectrum_form (a k : ℤ) :
    (57 : ℤ) + 7 * a + (-8) * (k - 1 - a) = 65 + 15 * a - 8 * k := by
  ring

/-- **Lemma 8 (arithmetic core: `Tr + 8·(k − 10) ≡ 0 (mod 15)`).** [done]

Pure ℤ form: given the spectrum equation `Tr = 65 + 15·a − 8·k`, the
quantity `Tr + 8·(k − 10) = 15·(a − 1)` is divisible by 15.

No Moore57 / spectral hypothesis is needed — this is the bare arithmetic
that the paper's mod-15 statement encodes. -/
theorem lem8_trace_mod_fifteen_arithmetic (Tr a k : ℤ)
    (h_spectrum : Tr = 65 + 15 * a - 8 * k) :
    (Tr + 8 * (k - 10)) % 15 = 0 := by
  omega

/-- **Lemma 8 (arithmetic core, `Int.ModEq` form).** [done]

Equivalent statement using the standard `a ≡ b [ZMOD n]` notation:
`Tr ≡ −8 · (k − 10) (mod 15)`. -/
theorem lem8_trace_mod_fifteen_zmod (Tr a k : ℤ)
    (h_spectrum : Tr = 65 + 15 * a - 8 * k) :
    Tr ≡ -8 * (k - 10) [ZMOD 15] := by
  unfold Int.ModEq
  omega

/-- **Lemma 8 (eigenvalue-swap invariance).** [done]

The paper's remark "any swap of `−8` and `7` changes the trace by 15"
formalised: if `Tr_a` and `Tr_{a+1}` are the traces for multiplicity-of-7
values `a` and `a + 1` respectively (with the multiplicity of `−8`
adjusted to keep `k` constant), they differ by `15`. -/
theorem lem8_trace_swap_diff (a k : ℤ) :
    ((65 + 15 * (a + 1) - 8 * k) - (65 + 15 * a - 8 * k) : ℤ) = 15 := by
  ring

/-- **Lemma 8 (paper-faithful conditional form).** [done — conditional]

Proper-signature form: given the spectrum equation `Tr = 65 + 15·a − 8·k`
(the geometric/spectral input from the orbit-adjacency matrix), the
paper's mod-15 statement `Tr ≡ −8·(k − 10) (mod 15)` holds.

This is `lem8_trace_mod_fifteen_zmod` lifted to the Moore57 context;
combined with the deferred spectrum bridge (`Tr(X) = 65 + 15·a − 8·k`
from `IsMoore57 Γ` + X-acts-by-graph-autos + SRG eigenvalue theory),
this becomes an unconditional paper-faithful bridge. -/
theorem lem8_trace_mod_fifteen_paper (hΓ : IsMoore57 Γ)
    (Tr a k : ℤ) (h_spectrum : Tr = 65 + 15 * a - 8 * k) :
    Tr ≡ -8 * (k - 10) [ZMOD 15] :=
  lem8_trace_mod_fifteen_zmod Tr a k h_spectrum

/-- **Lemma 8 (`Tr(X) ≡ −8(k − 10) mod 15`).** [deferred-heavy]

Paper-faithful Moore57-conditional statement.  The geometric content —
deriving `Tr(X) = 65 + 15·a − 8·k` from `IsMoore57 Γ` plus the fact
that the X-orbit adjacency matrix is `Γ`-spectrum-compatible — requires
the SRG eigenvalue theory for the orbit-adjacency matrix and is left
as a deferred-heavy skeleton.  Backward-compat True-stub; proper-
signature form is `lem8_trace_mod_fifteen_paper`. -/
theorem lem8_trace_mod_fifteen (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S3
