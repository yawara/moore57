from __future__ import annotations

import itertools
import time
import numpy as np

from .cover import PartialCover
from .perms import is_perm
from .spectrum import W_spectral_extremes


def verify_permutations(cover: PartialCover) -> dict:
    bad = []
    inv_bad = []
    for i in range(cover.N):
        for j in range(cover.N):
            p = cover.P[i][j]
            if p is None:
                bad.append([i, j, "missing"])
            elif not is_perm(p, cover.n):
                bad.append([i, j, "not_perm"])
            elif cover.P[j][i] is not None and not np.array_equal(cover.P[j][i][p], np.arange(cover.n)):
                inv_bad.append([i, j])
    return {
        "ok": not bad and not inv_bad,
        "bad": bad[:20],
        "inverse_bad": inv_bad[:20],
        "bad_count": len(bad),
        "inverse_bad_count": len(inv_bad),
    }


def verify_girth_voltage(cover: PartialCover) -> dict:
    """Check that all triangle and square voltage products are derangements."""
    N, n = cover.N, cover.n
    xs = np.arange(n, dtype=np.int16)
    tri_bad = []
    sq_bad = []
    for i, j, k in itertools.combinations(range(N), 3):
        prod = cover.get(k, i)[cover.get(j, k)[cover.get(i, j)]]
        f = int(np.sum(prod == xs))
        if f:
            tri_bad.append({"cycle": [i, j, k], "fixed_points": f})
    for i, j, k, l in itertools.combinations(range(N), 4):
        for cyc in ((i, j, k, l), (i, j, l, k), (i, k, j, l)):
            a, b, c, d = cyc
            prod = cover.get(d, a)[cover.get(c, d)[cover.get(b, c)[cover.get(a, b)]]]
            f = int(np.sum(prod == xs))
            if f:
                sq_bad.append({"cycle": list(cyc), "fixed_points": f})
    return {
        "triangles_checked": N * (N - 1) * (N - 2) // 6,
        "squares_checked": 3 * (N * (N - 1) * (N - 2) * (N - 3) // 24),
        "tri_bad_count": len(tri_bad),
        "square_bad_count": len(sq_bad),
        "tri_bad_examples": tri_bad[:10],
        "square_bad_examples": sq_bad[:10],
    }


def verify_c1_at_most_one(cover: PartialCover, *, full: bool = True, sample_cases: int = 100000, seed: int = 0) -> dict:
    """Check the partial-cover C1 consequence: at most one internal closer.

    For each ordered quadruple (i,h,ell,j) and sheet a, count fibers m in the
    current partial cover such that i-h-m-ell-j-i closes. In a full Moore cover
    the count over all external candidates is exactly one; in a partial cover
    the safe necessary condition is at most one.
    """
    N, n = cover.N, cover.n
    rng = np.random.default_rng(seed)
    bad = []
    hist = {0: 0, 1: 0}
    checked = 0

    def one_case(i, h, ell, j, a):
        x = int(cover.get(i, h)[a])
        y = int(cover.get(j, ell)[cover.get(i, j)[a]])
        closers = []
        for m in range(N):
            if m in (i, h, ell, j):
                continue
            if int(cover.get(m, ell)[cover.get(h, m)[x]]) == y:
                closers.append(m)
        return closers

    if full:
        iterator = ((i, h, ell, j, a) for i, h, ell, j in itertools.permutations(range(N), 4) for a in range(n))
    else:
        iterator = []
        for _ in range(sample_cases):
            i, h, ell, j = rng.choice(N, size=4, replace=False)
            a = int(rng.integers(n))
            iterator.append((int(i), int(h), int(ell), int(j), a))

    for i, h, ell, j, a in iterator:
        closers = one_case(i, h, ell, j, a)
        checked += 1
        c = len(closers)
        if c <= 1:
            hist[c] = hist.get(c, 0) + 1
        else:
            hist[c] = hist.get(c, 0) + 1
            bad.append({"quad": [i, h, ell, j], "a": a, "closers": closers})
            if len(bad) >= 20 and full:
                break
    return {
        "full": full,
        "cases_checked": checked,
        "bad_gt1": len(bad),
        "histogram": {str(k): int(v) for k, v in sorted(hist.items())},
        "bad_examples": bad[:20],
    }


def verify_cover(cover: PartialCover, *, spectrum: bool = True, c1_full: bool = True) -> dict:
    t0 = time.time()
    perm = verify_permutations(cover)
    girth = verify_girth_voltage(cover)
    c1 = verify_c1_at_most_one(cover, full=c1_full)
    spec = W_spectral_extremes(cover) if spectrum else None
    ok = (
        perm["ok"]
        and girth["tri_bad_count"] == 0
        and girth["square_bad_count"] == 0
        and c1["bad_gt1"] == 0
        and (spec is None or not spec["violates_Moore_window"])
    )
    return {
        "ok": ok,
        "fibers": cover.N,
        "sheet_size": cover.n,
        "permutations": perm,
        "girth_voltage": girth,
        "c1_at_most_one": c1,
        "spectrum": spec,
        "runtime_seconds": time.time() - t0,
    }
