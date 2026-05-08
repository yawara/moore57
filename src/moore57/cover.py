from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Optional
import numpy as np

from .io import read_json, write_json
from .perms import identity, inverse, translation, is_perm


@dataclass(frozen=True)
class CoverPaths:
    star_factors: Path
    seed14: Path


class PartialCover:
    """Permutation cover on fibers {0,...,N-1}.

    P[i][j] maps sheets in fiber i to sheets in fiber j.
    Missing entries are None.
    """

    def __init__(self, n: int, N: int):
        self.n = int(n)
        self.N = int(N)
        self.P: list[list[Optional[np.ndarray]]] = [[None for _ in range(N)] for _ in range(N)]
        I = identity(n)
        for i in range(N):
            self.P[i][i] = I.copy()

    def add(self, i: int, j: int, p) -> None:
        p = np.asarray(p, dtype=np.int16)
        if not is_perm(p, self.n):
            raise ValueError(f"not a permutation for edge {i}-{j}")
        self.P[i][j] = p
        self.P[j][i] = inverse(p)

    def get(self, i: int, j: int) -> np.ndarray:
        p = self.P[i][j]
        if p is None:
            raise KeyError(f"missing permutation P[{i}][{j}]")
        return p

    def has(self, i: int, j: int) -> bool:
        return self.P[i][j] is not None

    def copy(self) -> "PartialCover":
        q = PartialCover(self.n, self.N)
        q.P = [[None if p is None else p.copy() for p in row] for row in self.P]
        return q

    def to_solution_dict(self, meta: dict | None = None, outside_count: int | None = None, idxs: list[int] | None = None) -> dict:
        if outside_count is None:
            outside_count = self.N - 4
        out = {
            "n": self.n,
            "fibers": self.N,
            "outside_count": outside_count,
            "idxs": list(range(outside_count)) if idxs is None else idxs,
            "meta": {} if meta is None else meta,
            "candidate_candidate": {},
        }
        for i in range(4, self.N):
            for j in range(i + 1, self.N):
                if self.P[i][j] is not None:
                    out["candidate_candidate"][f"{i}-{j}"] = self.P[i][j].astype(int).tolist()
        return out


def load_star_factors(path: str | Path) -> list[list[np.ndarray]]:
    data = read_json(path)
    return [[np.asarray(p, dtype=np.int16) for p in factor] for factor in data["factors"]]


def build_anchor_star(star_path: str | Path, outside_count: int, idxs: list[int] | None = None) -> tuple[PartialCover, list[int]]:
    """Build anchors 0,1,2,3 plus outside_count star factors.

    Anchor convention:
    - P[0,r]=I for anchors and outside vertices.
    - P[1,2]=+1, P[1,3]=+2, P[2,3]=+3 on Z/56Z.
    - For outside block 4+pos, the star factor stores P[outside,1], P[outside,2], P[outside,3].
    """
    factors = load_star_factors(star_path)
    if idxs is None:
        idxs = list(range(outside_count))
    if len(idxs) != outside_count:
        raise ValueError("idxs length must match outside_count")
    n = len(factors[0][0])
    cover = PartialCover(n, 4 + outside_count)
    I = identity(n)
    for r in (1, 2, 3):
        cover.add(0, r, I)
    cover.add(1, 2, translation(n, 1))
    cover.add(1, 3, translation(n, 2))
    cover.add(2, 3, translation(n, 3))
    for pos, factor_index in enumerate(idxs):
        block = 4 + pos
        cover.add(0, block, I)
        for anchor, q in zip((1, 2, 3), factors[factor_index]):
            cover.add(block, anchor, q)
    return cover, idxs


def load_seed14(star_path: str | Path, seed_path: str | Path) -> tuple[PartialCover, list[int]]:
    seed = read_json(seed_path)
    idxs = seed.get("idxs", list(range(seed["outside_count"])))
    cover, idxs = build_anchor_star(star_path, int(seed["outside_count"]), idxs)
    if "candidate_candidate" in seed:
        for key, p in seed["candidate_candidate"].items():
            i, j = map(int, key.split("-"))
            cover.add(i, j, p)
    elif "P" in seed:
        P = seed["P"]
        for i in range(4, min(len(P), cover.N)):
            for j in range(i + 1, min(len(P), cover.N)):
                cover.add(i, j, P[i][j])
    else:
        raise ValueError("seed file has neither candidate_candidate nor P")
    return cover, idxs


def extend_with_new_star_factor(base: PartialCover, star_path: str | Path, new_factor_index: int) -> PartialCover:
    factors = load_star_factors(star_path)
    if new_factor_index < 0 or new_factor_index >= len(factors):
        raise ValueError("new_factor_index out of range")
    out = PartialCover(base.n, base.N + 1)
    for i in range(base.N):
        for j in range(i + 1, base.N):
            if base.P[i][j] is not None:
                out.add(i, j, base.P[i][j])
    new = base.N
    I = identity(base.n)
    out.add(0, new, I)
    for anchor, q in zip((1, 2, 3), factors[new_factor_index]):
        out.add(new, anchor, q)
    return out


def save_solution(cover: PartialCover, path: str | Path, meta: dict | None = None, idxs: list[int] | None = None) -> None:
    write_json(cover.to_solution_dict(meta=meta, idxs=idxs), path)
