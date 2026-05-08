from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import numpy as np

from .constraints import ExtensionInstance
from .io import write_json, read_json


@dataclass
class CnfBuildResult:
    cnf_path: Path
    map_path: Path
    stats: dict


def _pairwise_at_most_one(lits: list[int]) -> Iterable[list[int]]:
    for i in range(len(lits)):
        ai = lits[i]
        for j in range(i + 1, len(lits)):
            yield [-ai, -lits[j]]


def build_var_map(inst: ExtensionInstance) -> tuple[dict[tuple[int, int, int], int], list[tuple[int, int, int]]]:
    """Map allowed cells (vi,a,b) to DIMACS variables."""
    var: dict[tuple[int, int, int], int] = {}
    rev: list[tuple[int, int, int]] = [(-1, -1, -1)]
    next_id = 1
    m, n = inst.m, inst.n
    for vi in range(m):
        for a in range(n):
            for b in range(n):
                if inst.unary_allowed[vi, a, b]:
                    var[(vi, a, b)] = next_id
                    rev.append((vi, a, b))
                    next_id += 1
    return var, rev


def build_extend_cnf(inst: ExtensionInstance, cnf_path: str | Path, map_path: str | Path, *, comments: bool = True) -> CnfBuildResult:
    """Build pairwise-encoded DIMACS CNF for an extension instance."""
    cnf_path = Path(cnf_path)
    map_path = Path(map_path)
    cnf_path.parent.mkdir(parents=True, exist_ok=True)
    map_path.parent.mkdir(parents=True, exist_ok=True)
    m, n = inst.m, inst.n
    var, rev = build_var_map(inst)
    clauses: list[list[int]] = []
    stats = {
        "encoding": "pairwise",
        "sheet_size": n,
        "num_unknown_perms": m,
        "unknown_fibers": inst.vars,
        "new_fiber": inst.new,
        "num_vars": len(rev) - 1,
        "row_atleast": 0,
        "row_atmost_pairwise": 0,
        "col_atleast": 0,
        "col_atmost_pairwise": 0,
        "binary_nogoods": 0,
        "empty_domains": [],
    }

    for vi in range(m):
        for a in range(n):
            lits = [var[(vi, a, b)] for b in range(n) if (vi, a, b) in var]
            if not lits:
                clauses.append([])
                stats["empty_domains"].append(["row", vi, a])
                continue
            clauses.append(lits)
            stats["row_atleast"] += 1
            for cl in _pairwise_at_most_one(lits):
                clauses.append(cl)
                stats["row_atmost_pairwise"] += 1

    for vi in range(m):
        for b in range(n):
            lits = [var[(vi, a, b)] for a in range(n) if (vi, a, b) in var]
            if not lits:
                clauses.append([])
                stats["empty_domains"].append(["col", vi, b])
                continue
            clauses.append(lits)
            stats["col_atleast"] += 1
            for cl in _pairwise_at_most_one(lits):
                clauses.append(cl)
                stats["col_atmost_pairwise"] += 1

    for vi in range(m):
        for vj in range(vi + 1, m):
            F = ~inst.pair_allowed[vi, vj]
            bad_pairs = np.argwhere(F)
            for a in range(n):
                for b, c in bad_pairs:
                    key1 = (vi, a, int(b))
                    key2 = (vj, a, int(c))
                    x = var.get(key1)
                    y = var.get(key2)
                    if x is not None and y is not None:
                        clauses.append([-x, -y])
                        stats["binary_nogoods"] += 1

    stats["num_clauses"] = len(clauses)
    with open(cnf_path, "w", encoding="utf-8") as f:
        if comments:
            f.write("c moore57 extend-one-block CNF\n")
            f.write("c vars are allowed cells x[vi,a,b] meaning P[new][vars[vi]](a)=b\n")
        f.write(f"p cnf {stats['num_vars']} {stats['num_clauses']}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")

    mapping = {
        "format": "moore57_cnf_varmap_v1",
        "stats": stats,
        "vars": [None] + [{"vi": vi, "fiber": inst.vars[vi], "a": a, "b": b} for vi, a, b in rev[1:]],
    }
    write_json(mapping, map_path)
    return CnfBuildResult(cnf_path=cnf_path, map_path=map_path, stats=stats)


def parse_dimacs_assignment(path: str | Path) -> tuple[str, set[int]]:
    """Parse a SAT solver output file. Return (status, positive_vars)."""
    status = "unknown"
    pos: set[int] = set()
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        for line in f:
            s = line.strip()
            if not s or s.startswith("c"):
                continue
            if s.startswith("s"):
                if "UNSAT" in s:
                    status = "unsat"
                elif "SAT" in s:
                    status = "sat"
                continue
            toks = s.split()[1:] if s.startswith("v") else s.split()
            for tok in toks:
                try:
                    lit = int(tok)
                except ValueError:
                    continue
                if lit == 0:
                    continue
                if lit > 0:
                    pos.add(lit)
    return status, pos


def assignment_to_Q(map_path: str | Path, positive_vars: set[int]) -> np.ndarray:
    mapping = read_json(map_path)
    stats = mapping["stats"]
    m = int(stats["num_unknown_perms"])
    n = int(stats["sheet_size"])
    Q = -np.ones((m, n), dtype=np.int16)
    for var_id in positive_vars:
        if var_id <= 0 or var_id >= len(mapping["vars"]):
            continue
        rec = mapping["vars"][var_id]
        if rec is None:
            continue
        vi, a, b = int(rec["vi"]), int(rec["a"]), int(rec["b"])
        if Q[vi, a] != -1 and Q[vi, a] != b:
            raise ValueError(f"duplicate assignment for vi={vi}, a={a}: {Q[vi,a]} and {b}")
        Q[vi, a] = b
    missing = np.argwhere(Q < 0)
    if len(missing):
        raise ValueError(f"assignment missing {len(missing)} row values; first={missing[0].tolist()}")
    return Q
