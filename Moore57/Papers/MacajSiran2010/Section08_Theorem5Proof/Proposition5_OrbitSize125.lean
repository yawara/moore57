import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Lemma24_TwoOrbits

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §8, Proposition 5 [skeleton]

> The graph Γ does not admit a group of automorphisms of order 625 with
> the smallest orbit size 125.

Proof outline (paper §8):
1. Suppose `|X| = 625` with smallest orbit size 125. Let `O₁, …, Oᵢ` be
   size-625 orbits and `Oᵢ₊₁, …, Oₖ` size-125 orbits, with `Oₖ` having
   vertex stabilizer `Y` ﬁxing elements from at most two orbits (Lemma 23).
2. Analyse the bottom-right entry `Σⱼ b²_{k,j} + b_{kk} = 181` from
   `B² + B − 56 I = 1ᵀ s`.
3. Case `i ≤ 3`: no solution. Case `i = 4`: enumerate 6 row types and
   show no compatible trace decomposition with `Tr(X) = 60` exists.
-/

namespace Moore57.Papers.MacajSiran2010.S8

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Proposition 5 (no `|X| = 625` with smallest orbit 125).** [skeleton] -/
theorem prop5_orbit_size_125 (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S8
