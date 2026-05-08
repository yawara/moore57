from __future__ import annotations

from dataclasses import dataclass
import numpy as np

from .cover import PartialCover


@dataclass
class ExtensionInstance:
    """One-new-block extension instance.

    `cover` contains existing fibers and fixed edges from the new fiber to anchors.
    Unknown edges are P[new][v] for v in `vars`.
    """

    cover: PartialCover
    new: int
    vars: list[int]
    unary_allowed: np.ndarray
    pair_allowed: np.ndarray

    @property
    def n(self) -> int:
        return self.cover.n

    @property
    def m(self) -> int:
        return len(self.vars)


def compute_unary_allowed(cover: PartialCover, new: int, vars: list[int]) -> np.ndarray:
    """Allowed cells for P[new][v](a)=b.

    A cell is forbidden if it coincides with an already-fixed path of length 2 or 3
    from new to v. Such a direct edge would create a triangle or square.
    """
    n, N = cover.n, cover.N
    xs = np.arange(n, dtype=np.int16)
    allowed = np.ones((len(vars), n, n), dtype=bool)
    for vi, v in enumerate(vars):
        forbidden = np.zeros((n, n), dtype=bool)
        for w in range(N):
            if w in (new, v):
                continue
            if cover.has(new, w) and cover.has(w, v):
                forbidden[xs, cover.get(w, v)[cover.get(new, w)]] = True
        for w in range(N):
            if w in (new, v) or not cover.has(new, w):
                continue
            nw = cover.get(new, w)
            for z in range(N):
                if z in (new, v, w):
                    continue
                if cover.has(w, z) and cover.has(z, v):
                    forbidden[xs, cover.get(z, v)[cover.get(w, z)[nw]]] = True
        allowed[vi] = ~forbidden
    return allowed


def compute_pair_allowed(cover: PartialCover, vars: list[int]) -> np.ndarray:
    """Compatibility for pairs P[new][i](a)=b and P[new][j](a)=c.

    For i<j among unknown existing fibers, values b,c on the same new-row a
    are incompatible if b -> c is already realized by a fixed path of length 1
    or 2 from i to j. This would close a triangle or square through new.
    """
    n, N = cover.n, cover.N
    m = len(vars)
    pair_allowed = np.ones((m, m, n, n), dtype=bool)
    xs = np.arange(n, dtype=np.int16)
    for ai, i in enumerate(vars):
        for aj, j in enumerate(vars):
            if ai == aj:
                continue
            forbidden = np.zeros((n, n), dtype=bool)
            if cover.has(i, j):
                forbidden[xs, cover.get(i, j)] = True
            for k in range(N):
                if k in (i, j):
                    continue
                if cover.has(i, k) and cover.has(k, j):
                    forbidden[xs, cover.get(k, j)[cover.get(i, k)]] = True
            pair_allowed[ai, aj] = ~forbidden
    return pair_allowed


def build_extension_instance(cover: PartialCover, new: int | None = None, vars: list[int] | None = None) -> ExtensionInstance:
    if new is None:
        new = cover.N - 1
    if vars is None:
        vars = list(range(4, new))
    unary = compute_unary_allowed(cover, new, vars)
    pair = compute_pair_allowed(cover, vars)
    return ExtensionInstance(cover=cover, new=new, vars=vars, unary_allowed=unary, pair_allowed=pair)


def assignment_conflict_count(Q: np.ndarray, inst: ExtensionInstance) -> int:
    m, n = Q.shape
    bad = 0
    for vi in range(m):
        p = Q[vi]
        if sorted(map(int, p)) != list(range(n)):
            bad += 10_000
        for a, b in enumerate(p):
            if not inst.unary_allowed[vi, a, int(b)]:
                bad += 100
    for vi in range(m):
        for vj in range(vi + 1, m):
            for a in range(n):
                b = int(Q[vi, a]); c = int(Q[vj, a])
                if not inst.pair_allowed[vi, vj, b, c]:
                    bad += 1
    return bad


def complete_cover_from_assignment(inst: ExtensionInstance, Q: np.ndarray) -> PartialCover:
    cover = inst.cover.copy()
    for vi, v in enumerate(inst.vars):
        cover.add(inst.new, v, Q[vi])
    return cover


def verify_extension_assignment(inst: ExtensionInstance, Q: np.ndarray) -> dict:
    m, n = Q.shape
    unary_bad = []
    pair_bad = []
    perm_bad = []
    for vi in range(m):
        p = np.asarray(Q[vi], dtype=np.int16)
        if not np.array_equal(np.sort(p), np.arange(n)):
            perm_bad.append(inst.vars[vi])
        for a, b in enumerate(p):
            if not inst.unary_allowed[vi, a, int(b)]:
                unary_bad.append((inst.vars[vi], int(a), int(b)))
                if len(unary_bad) >= 10:
                    break
    for vi in range(m):
        for vj in range(vi + 1, m):
            for a in range(n):
                b = int(Q[vi, a]); c = int(Q[vj, a])
                if not inst.pair_allowed[vi, vj, b, c]:
                    pair_bad.append((inst.vars[vi], inst.vars[vj], int(a), b, c))
                    if len(pair_bad) >= 10:
                        break
            if len(pair_bad) >= 10:
                break
        if len(pair_bad) >= 10:
            break
    return {
        "ok": not perm_bad and not unary_bad and not pair_bad,
        "perm_bad": perm_bad,
        "unary_bad_count_reported": len(unary_bad),
        "unary_bad_examples": unary_bad,
        "pair_bad_count_reported": len(pair_bad),
        "pair_bad_examples": pair_bad,
        "conflict_count_weighted": assignment_conflict_count(Q, inst),
    }
