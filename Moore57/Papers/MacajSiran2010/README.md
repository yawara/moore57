# Mačaj–Širáň 2010 — Lean formalization

This directory mirrors the structure of

> Martin Mačaj and Jozef Širáň,
> "Search for properties of the missing Moore graph",
> *Linear Algebra and its Applications* **432** (2010), 2381–2398.
> DOI: [10.1016/j.laa.2009.07.018](https://doi.org/10.1016/j.laa.2009.07.018).

Each `.lean` file under `SectionXX_*/` re-states one lemma / proposition /
theorem / corollary from the paper, in the same numbering. Most files are
thin wrappers around the existing Moore57 infrastructure
(`Moore57/D19OnMoore57/`, `Moore57/Order22OnMoore57/`, `Moore57/Moore57Graph/Aut/`,
`Moore57/Foundations/`); some are new and currently carry `sorry` placeholders.

## Status legend (kept in each file's docstring)

| Marker        | Meaning                                                                |
|---------------|------------------------------------------------------------------------|
| `[wrap]`      | Statement is a thin re-export of an existing Moore57 theorem.          |
| `[skeleton]`  | Statement is correct but proof body is `sorry`.                        |
| `[external]`  | Statement is imported from another paper directory (e.g. Makhnev–Paduchikh 2001). |
| `[GAP]`       | Original proof relies on GAP computations; either Lean `decide`/`native_decide` or `sorry`. |
| `[done]`      | Statement is fully proved (no `sorry`).                                |

## Numbering

| § | Lemmas / Theorems / Propositions / Corollaries                                 |
|---|---------------------------------------------------------------------------------|
| 2 | Prop 1, Lem 1–4, Thm 1–2                                                        |
| 3 | Lem 5–10, Cor 1                                                                 |
| 4 | Thm 3, Prop 2, Lem 11                                                           |
| 5 | Lem 12–15                                                                       |
| 6 | Lem 16–20, Thm 4 (stmt), Thm 5 (stmt)                                           |
| 7 | Lem 21, Cor 2, Thm 4 (proof)                                                    |
| 8 | Prop 3, Lem 22, Prop 4, Lem 23–24, Prop 5, Thm 5 (proof)                        |
| 9 | Lem 25–26, Prop 6–8, Thm 6, Thm 7, Cor 3                                        |

The final unified `|Aut(Γ)| ≤ 375` bound is in `MainTheorem.lean`.
