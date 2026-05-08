from __future__ import annotations

import numpy as np

from .cover import PartialCover


def adjacency_matrix(cover: PartialCover) -> np.ndarray:
    """Build the adjacency matrix of the fiber cover graph."""
    N, n = cover.N, cover.n
    A = np.zeros((N * n, N * n), dtype=float)
    for i in range(N):
        for j in range(i + 1, N):
            p = cover.P[i][j]
            if p is None:
                raise ValueError(f"missing edge {i}-{j}")
            for a, b in enumerate(p):
                u = i * n + a
                v = j * n + int(b)
                A[u, v] = 1.0
                A[v, u] = 1.0
    return A


def quotient_basis(N: int, n: int) -> np.ndarray:
    """Orthonormal basis for vectors constant on each fiber."""
    Q = np.zeros((N * n, N), dtype=float)
    scale = 1.0 / np.sqrt(n)
    for i in range(N):
        Q[i * n:(i + 1) * n, i] = scale
    return Q


def W_spectral_extremes(cover: PartialCover) -> dict:
    """Compute eigenvalue extremes on the block-sum-zero space W.

    For an N-fiber partial cover, the full adjacency has a quotient subspace
    of dimension N. The non-quotient spectrum is obtained by projecting away
    the fiber-constant subspace.
    """
    A = adjacency_matrix(cover)
    N, n = cover.N, cover.n
    Q = quotient_basis(N, n)
    P = np.eye(N * n) - Q @ Q.T
    B = P @ A @ P
    vals = np.linalg.eigvalsh(B)
    vals = vals[np.abs(vals) > 1e-8]
    if len(vals) == 0:
        mn = mx = 0.0
    else:
        mn = float(vals[0])
        mx = float(vals[-1])
    return {
        "W_dimension": N * (n - 1),
        "W_spectrum_min": mn,
        "W_spectrum_max": mx,
        "violates_Moore_window": bool(mn < -8 - 1e-8 or mx > 7 + 1e-8),
        "margin_lower_min_plus_8": mn + 8,
        "margin_upper_7_minus_max": 7 - mx,
    }
