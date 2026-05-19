/-!
# Citation: Higman 1964

Donald G. Higman,
"Finite permutation groups of rank 3",
*Math. Zeitschr.* **86** (1964), 145–156.
DOI: [10.1007/BF01111335](https://doi.org/10.1007/BF01111335).

Local extracted text:
* `tmp/pdfs/higman_1964.txt` — abbreviated notes for formalisation.
* `tmp/pdfs/higman_1964_raw.txt` — raw `pdftotext` extract of the PDF.

## Result map

| Statement     | Location                              |
|---------------|---------------------------------------|
| Lemma 1 (§1)  | `Lemma01_PairedOrbits.lean`           |
| Lemma 2 (§2)  | `Lemma02_IntersectionNumbers.lean`    |
| Lemma 3 (§2)  | `Lemma03_SelfPaired.lean`             |
| Lemma 4 (§2)  | `Lemma04_Imprimitivity.lean`          |
| Lemma 5 (§3)  | `Lemma05_BlockDesignCount.lean`       |
| Lemma 6 (§4)  | `Lemma06_TwoEigenvalues.lean`         |
| Lemma 7 (§5)  | `Lemma07_IntegralityCases.lean`       |
| Theorem 1 (§6)| `Theorem1_DegreeKSqPlus1.lean`        |
| (Main)        | `MainTheorem.lean`                    |

This paper is the structural backbone behind Aschbacher 1971's main
theorem. Concretely, **Theorem 1** (§6) shows that a transitive rank-3
permutation group of degree `n = k² + 1` (where `k` is the length of a
`G_a`-orbit) has `k ∈ {2, 3, 7, 57}`. This is exactly the bound
Aschbacher cites with "Results of D. Higman show that 𝒢 satisfies (*)
[2]" — the strong (0, 1) condition together with the valence
classification both originate here.

Sections 7–8 develop the symplectic-group characterisation Theorem 2,
which is independent of the Moore57 line of work.
-/
