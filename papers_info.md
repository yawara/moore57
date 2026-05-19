# Papers and Extracted Texts

Last checked: 2026-05-19 (Higman 1964 added)

This file records which local PDF/text files correspond to which references, so
the proof notes can refer back to them without guessing from filenames.

## Local PDFs

| Local PDF | Extracted text | Reference | Notes for the Moore57 proof |
| --- | --- | --- | --- |
| `/Users/ywr/Downloads/representation_theory.pdf` | `tmp/pdfs/cameron_ch2_representation_theory.txt` | Peter J. Cameron, *Permutation Groups*, Chapter 2, "Representation theory", Cambridge University Press, 1999. Cambridge online DOI chapter suffix: `10.1017/CBO9780511623677.003`. | Representation-theory background: permutation characters, fixed-point counts, orbit averaging, and character methods used around the Higman/Cameron route. |
| `/Users/ywr/Downloads/coherent_configurations.pdf` | `tmp/pdfs/cameron_ch3_coherent_configurations.txt` | Peter J. Cameron, *Permutation Groups*, Chapter 3, "Coherent configurations", Cambridge University Press, 1999. Cambridge online DOI chapter suffix: `10.1017/CBO9780511623677.004`. | Coherent configurations and Moore graph material, including the valency 57 discussion and the vertex-transitivity obstruction context. |
| `/Users/ywr/Downloads/1-s2.0-S0024379519300138-main.pdf` | `tmp/pdfs/dalfo_missing_moore_survey_2019.txt` | C. Dalfo, "A survey on the missing Moore graph", *Linear Algebra and its Applications* 569 (2019), 1-14. DOI: `10.1016/j.laa.2018.12.035`. | Survey reference for known properties of the possible Moore graph of degree 57 and diameter 2, including distance-regularity, regular partitions, spectral material, and automorphism context. |

## Extracted Article Texts

These extracted texts are present under `tmp/pdfs/`. The original article PDFs
were not present under the repository or `/Users/ywr/Downloads` in the current
scan, but the extracted text is available for proof work.

| Extracted text | Reference | Notes for the Moore57 proof |
| --- | --- | --- |
| `tmp/pdfs/j.laa.2009.07.018.txt` | Martin Macaj and Jozef Siran, "Search for properties of the missing Moore graph", *Linear Algebra and its Applications* 432 (2010), 2381-2398. DOI: `10.1016/j.laa.2009.07.018`. | Main source for restrictions on automorphisms of the hypothetical Moore graph of degree 57; useful around order bounds, odd/even automorphism cases, and the D19/no-order-19 route. Scaffolded as `Moore57/Papers/MacajSiran2010/` (paper-structured §2-§9 + MainTheorem). |
| `tmp/pdfs/involution-fixed-star.txt` | A. A. Makhnev and D. V. Paduchikh, "Automorphisms of Aschbacher Graphs", *Algebra and Logic* 40 (2) (2001), 69-74. DOI: `10.1023/A:1010217919915`. | Main source for involution fixed-point structure: every involution fixes a 56-vertex star in the hypothetical Moore graph of valency 57, plus the even-order automorphism-group structure used by later papers. Scaffolded as `Moore57/Papers/MakhnevPaduchikh2001/`. |
| `tmp/pdfs/aschbacher_1971.txt` | Michael Aschbacher, "The Nonexistence of Rank Three Permutation Groups of Degree 3250 and Subdegree 57", *Journal of Algebra* 19 (1971), 538-540. DOI: `10.1016/0021-8693(71)90087-1`. | Foundational paper: Lemma 1.1 (strong (0,1) graph is regular or star), Lemma 1.2 (Fix(G) inherits the property), Lemma 1.3 (valence ∈ {2,3,7,57}), Lemma 1.4 (involution fix structure). Cited as the structural backbone behind Macaj-Siran Lem 1 and MP Lem 1. Scaffolded as `Moore57/Papers/Aschbacher1971/`. |
| `tmp/pdfs/higman_1964.txt` | Donald G. Higman, "Finite permutation groups of rank 3", *Math. Zeitschr.* 86 (1964), 145-156. DOI: `10.1007/BF01111335`. | External dependency cited by Aschbacher 1971 Main Theorem ("Results of D. Higman show that 𝒢 satisfies (*) [2]"). Key payload: Theorem 1 — a transitive rank-3 group of degree `k²+1` (with `k` = G_a-orbit length) has degree in `{5, 10, 50, 3250}`, i.e. `k ∈ {2, 3, 7, 57}`. Higman §6 also establishes `λ = 0, μ = 1` (Aschbacher's (*) condition). Scaffolded as `Moore57/Papers/Higman1964/`. |
