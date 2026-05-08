from __future__ import annotations

from typing import Iterable, Sequence
import numpy as np


def identity(n: int) -> np.ndarray:
    return np.arange(n, dtype=np.int16)


def translation(n: int, d: int) -> np.ndarray:
    return ((np.arange(n, dtype=np.int16) + d) % n).astype(np.int16)


def inverse(p: Sequence[int]) -> np.ndarray:
    p = np.asarray(p, dtype=np.int16)
    inv = np.empty_like(p)
    inv[p] = np.arange(len(p), dtype=np.int16)
    return inv


def compose(p: Sequence[int], q: Sequence[int]) -> np.ndarray:
    """Return p∘q, i.e. x -> p[q[x]]."""
    p = np.asarray(p, dtype=np.int16)
    q = np.asarray(q, dtype=np.int16)
    return p[q]


def apply_chain(perms: Iterable[Sequence[int]], x: np.ndarray | int) -> np.ndarray | int:
    """Apply a chain p_r∘...∘p_1 to x.

    The iterable order is the path order: first permutation first.
    """
    y = x
    for p in perms:
        y = np.asarray(p, dtype=np.int16)[y]
    return y


def is_perm(p: Sequence[int], n: int | None = None) -> bool:
    p = np.asarray(p)
    if n is None:
        n = len(p)
    return len(p) == n and np.array_equal(np.sort(p), np.arange(n))


def fixed_points(p: Sequence[int]) -> int:
    p = np.asarray(p)
    return int(np.sum(p == np.arange(len(p))))
