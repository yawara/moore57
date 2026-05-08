# /// script
# requires-python = ">=3.11"
# dependencies = [
#   "ortools>=9.10",
# ]
# ///
"""
D38-equivariant CP-SAT prototype for the hypothetical Moore graph
of degree 57 and diameter 2.

Run examples:

    uv run moore_d38_ortools.py
    uv run moore_d38_ortools.py --level equiv --timeout 60
    uv run moore_d38_ortools.py --level triangle --timeout 3600 --workers 8 --log
    uv run moore_d38_ortools.py --level core --timeout 86400 --workers 8

This is an experimental UNSAT-without-certificate model.

Mathematical model, in brief
----------------------------

We fix a root vertex u. Its 57 neighbors are called "branches".
Each branch has 56 distance-2 vertices, called leaves.

A Moore graph of degree 57 and diameter 2 has parameters

    (v, k, lambda, mu) = (3250, 57, 0, 1)

so between any two distinct branches i,j, the leaf-leaf edges form
a perfect matching. We write that matching as a permutation

    pi[i,j] : {0,...,55} -> {0,...,55}

where

    leaf (i,a) is adjacent to leaf (j, pi[i,j][a]).

This script imposes a specific D38 action normal form:

    D38 = < r, tau | r^19 = tau^2 = 1, tau r tau = r^-1 >

on the 57 branches.

Branch set:

    O0 = 19 branches
    O1 = 19 branches
    O2 = 19 branches

C19=<r> acts regularly on each orbit.

The involution tau:

    - reflects O0 and fixes exactly one branch in O0,
    - swaps O1 and O2,
    - hence root u has exactly one tau-fixed neighbor.

This corresponds to the case where u is a leaf of Fix(tau) ~= K_{1,55}.
The unique tau-fixed branch is the center of that fixed star.

On leaves, we choose labels so that:

    - r preserves the leaf label;
    - tau on the fixed branch-orbit O0 fixes 54 labels and swaps 2 labels;
    - tau between O1 and O2 preserves the label.

This gives total tau-fixed vertices:

    root u                 : 1
    fixed branch            : 1
    fixed leaves in branch  : 54
    total                   : 56

matching the known involution fixed-subgraph size.

Important:
    This is a computational experiment under this D38 normal form.
    INFEASIBLE from OR-Tools here is not a formal proof certificate.
"""

from __future__ import annotations

import argparse
import sys
import time
from collections import deque
from dataclasses import dataclass
from typing import Iterable

from ortools.sat.python import cp_model


P_ORDER = 19
N_BRANCH_ORBITS = 3
N_BRANCHES = P_ORDER * N_BRANCH_ORBITS  # 57
N_LABELS = 56


# ---------------------------------------------------------------------------
# Branch indexing
# ---------------------------------------------------------------------------
#
# Branch b is encoded as
#
#     b = orbit * 19 + position
#
# where orbit in {0,1,2}, position in Z/19Z.
#
# O0 is the tau-stable orbit.
# O1 and O2 are swapped by tau.


def branch(orbit: int, pos: int) -> int:
    return orbit * P_ORDER + (pos % P_ORDER)


def branch_orbit(b: int) -> int:
    return b // P_ORDER


def branch_pos(b: int) -> int:
    return b % P_ORDER


def branch_str(b: int) -> str:
    return f"O{branch_orbit(b)}[{branch_pos(b)}]"


# ---------------------------------------------------------------------------
# D38 action on branches
# ---------------------------------------------------------------------------


def r_branch(b: int) -> int:
    """Rotation r on branches."""
    return branch(branch_orbit(b), branch_pos(b) + 1)


def tau_branch(b: int) -> int:
    """Reflection tau on branches."""
    q = branch_orbit(b)
    t = branch_pos(b)

    if q == 0:
        # O0 is reflected and preserved.
        return branch(0, -t)
    if q == 1:
        # O1 and O2 are swapped.
        return branch(2, -t)
    if q == 2:
        return branch(1, -t)

    raise AssertionError("unreachable")


# ---------------------------------------------------------------------------
# D38 action on leaf labels
# ---------------------------------------------------------------------------
#
# r keeps labels unchanged.
#
# tau:
#   - on O0, use cycle type 1^54 2^1:
#         0,...,53 fixed, 54 <-> 55
#   - on O1/O2, use identity label transfer between swapped branches.
#
# This is a normal form chosen by relabeling leaves within branch orbits.


IDENTITY_LABEL = list(range(N_LABELS))
TAU_O0_LABEL = list(range(N_LABELS))
TAU_O0_LABEL[54], TAU_O0_LABEL[55] = 55, 54


def tau_label_map_for_source_branch(b: int) -> list[int]:
    """Return the label permutation induced by tau on leaves of source branch b."""
    if branch_orbit(b) == 0:
        return TAU_O0_LABEL
    return IDENTITY_LABEL


def tau_label_value(source_branch: int, a: int) -> int:
    return tau_label_map_for_source_branch(source_branch)[a]


def r_vertex(i: int, a: int) -> tuple[int, int]:
    """Action of r on a leaf vertex (branch, label)."""
    return r_branch(i), a


def tau_vertex(i: int, a: int) -> tuple[int, int]:
    """Action of tau on a leaf vertex (branch, label)."""
    return tau_branch(i), tau_label_value(i, a)


# ---------------------------------------------------------------------------
# Orbit representatives for constraints
# ---------------------------------------------------------------------------


def orbit_of_ordered_pair_label(i: int, j: int, a: int) -> set[tuple[int, int, int]]:
    """
    Orbit of (i,j,a) under D38, where a is a label in source branch i.

    This is used for constraints indexed by:
        ordered branch pair (i,j), i != j,
        source label a.

    The target label is not part of the index; target-side label maps appear
    in the pi variables and equivariance constraints.
    """
    start = (i, j, a)
    seen: set[tuple[int, int, int]] = {start}
    q: deque[tuple[int, int, int]] = deque([start])

    while q:
        x_i, x_j, x_a = q.popleft()

        # Apply r.
        y_i, y_a = r_vertex(x_i, x_a)
        y_j = r_branch(x_j)
        y = (y_i, y_j, y_a)
        if y not in seen:
            seen.add(y)
            q.append(y)

        # Apply tau.
        y_i, y_a = tau_vertex(x_i, x_a)
        y_j = tau_branch(x_j)
        y = (y_i, y_j, y_a)
        if y not in seen:
            seen.add(y)
            q.append(y)

    return seen


def ordered_pair_label_representatives() -> list[tuple[int, int, int]]:
    """
    Return lexicographic representatives for D38-orbits of (i,j,a),
    with i != j.
    """
    reps: list[tuple[int, int, int]] = []
    global_seen: set[tuple[int, int, int]] = set()

    for i in range(N_BRANCHES):
        for j in range(N_BRANCHES):
            if i == j:
                continue
            for a in range(N_LABELS):
                x = (i, j, a)
                if x in global_seen:
                    continue
                orb = orbit_of_ordered_pair_label(i, j, a)
                global_seen.update(orb)
                reps.append(min(orb))

    reps.sort()
    return reps


# ---------------------------------------------------------------------------
# CP-SAT model construction
# ---------------------------------------------------------------------------


@dataclass
class ModelObjects:
    model: cp_model.CpModel
    pi: dict[tuple[int, int], list[cp_model.IntVar]]
    core_reps: list[tuple[int, int, int]]
    aux_count: int = 0


def new_aux(obj: ModelObjects, prefix: str = "aux") -> cp_model.IntVar:
    obj.aux_count += 1
    return obj.model.NewIntVar(0, N_LABELS - 1, f"{prefix}_{obj.aux_count}")


def perm_image(
    obj: ModelObjects,
    x: cp_model.IntVar,
    perm: list[int],
    prefix: str,
) -> cp_model.IntVar | cp_model.LinearExpr:
    """
    Return y = perm[x].

    If perm is identity, return x directly.
    Otherwise create y and add Element(x, perm, y).
    """
    if perm == IDENTITY_LABEL:
        return x

    y = new_aux(obj, prefix)
    obj.model.AddElement(x, perm, y)
    return y


def build_base_model() -> ModelObjects:
    model = cp_model.CpModel()

    # pi[(i,j)][a] is pi_{ij}(a), for i != j.
    #
    # This is an ordered matching variable:
    #   leaf (i,a) -- leaf (j, pi[(i,j)][a]).
    #
    # We define both directions pi[(i,j)] and pi[(j,i)], then enforce inverse
    # consistency.
    pi: dict[tuple[int, int], list[cp_model.IntVar]] = {}

    for i in range(N_BRANCHES):
        for j in range(N_BRANCHES):
            if i == j:
                continue
            pi[(i, j)] = [
                model.NewIntVar(0, N_LABELS - 1, f"pi_{i}_{j}_{a}")
                for a in range(N_LABELS)
            ]

    obj = ModelObjects(model=model, pi=pi, core_reps=[])

    # -----------------------------------------------------------------------
    # Perfect matching constraints.
    #
    # For every ordered pair i != j, pi_{ij} is a permutation of 0..55.
    # -----------------------------------------------------------------------
    for i in range(N_BRANCHES):
        for j in range(N_BRANCHES):
            if i == j:
                continue
            model.AddAllDifferent(pi[(i, j)])

    # -----------------------------------------------------------------------
    # Inverse consistency.
    #
    # If pi_{ij}(a) = b, then pi_{ji}(b) = a.
    #
    # Encoded as:
    #     Element(pi_{ij}[a], pi_{ji}, a)
    #
    # Only add for i < j, because the reverse is implied by permutation +
    # these inverse constraints.
    # -----------------------------------------------------------------------
    for i in range(N_BRANCHES):
        for j in range(i + 1, N_BRANCHES):
            for a in range(N_LABELS):
                model.AddElement(pi[(i, j)][a], pi[(j, i)], a)

    # -----------------------------------------------------------------------
    # Equivariance under r.
    #
    # If
    #     pi_{ij}(a) = b,
    # then applying r gives
    #     pi_{r(i),r(j)}(a) = b.
    #
    # r preserves labels in this normal form.
    # -----------------------------------------------------------------------
    for i in range(N_BRANCHES):
        ri = r_branch(i)
        for j in range(N_BRANCHES):
            if i == j:
                continue
            rj = r_branch(j)
            for a in range(N_LABELS):
                model.Add(pi[(ri, rj)][a] == pi[(i, j)][a])

    # -----------------------------------------------------------------------
    # Equivariance under tau.
    #
    # If
    #     pi_{ij}(a) = b,
    # then tau sends the edge to
    #     (tau(i), tau_i(a)) -- (tau(j), tau_j(b)).
    #
    # Hence
    #     pi_{tau(i),tau(j)}( tau_i(a) ) = tau_j( pi_{ij}(a) ).
    #
    # tau_i on labels depends on source branch i:
    #     O0: swap labels 54 and 55, fix 0..53
    #     O1/O2: identity transfer.
    # -----------------------------------------------------------------------
    for i in range(N_BRANCHES):
        ti = tau_branch(i)
        for j in range(N_BRANCHES):
            if i == j:
                continue
            tj = tau_branch(j)
            tau_j_perm = tau_label_map_for_source_branch(j)

            for a in range(N_LABELS):
                ta = tau_label_value(i, a)
                lhs = pi[(ti, tj)][ta]
                rhs = perm_image(obj, pi[(i, j)][a], tau_j_perm, "tau_img")
                model.Add(lhs == rhs)

    return obj


def add_triangle_constraints(obj: ModelObjects, reps: list[tuple[int, int, int]]) -> None:
    """
    Add triangle-forbidding constraints for orbit representatives.

    For distinct branches i,j,h and source label a:

        leaf (i,a) is adjacent to leaf (j, pi_{ij}(a)).
        leaf (i,a) is adjacent to leaf (h, pi_{ih}(a)).

    A triangle would occur if those two target leaves are adjacent, i.e.

        pi_{hj}( pi_{ih}(a) ) == pi_{ij}(a).

    Therefore require

        pi_{hj}( pi_{ih}(a) ) != pi_{ij}(a)

    for all h != i,j.

    Because equivariance constraints are present, it is enough to add these
    only for D38-orbit representatives of (i,j,a).
    """
    model = obj.model
    pi = obj.pi

    for rep_idx, (i, j, a) in enumerate(reps):
        edge_ij = pi[(i, j)][a]

        for h in range(N_BRANCHES):
            if h == i or h == j:
                continue

            # t = pi_{hj}( pi_{ih}(a) )
            #
            # This is the label b in branch j such that the leaf (j,b)
            # has common neighbor (h, pi_{ih}(a)) with leaf (i,a).
            t = new_aux(obj, "tri")
            model.AddElement(pi[(i, h)][a], pi[(h, j)], t)

            # Triangle prohibition:
            #   this common-neighbor position cannot equal the direct neighbor.
            model.Add(t != edge_ij)

        if rep_idx > 0 and rep_idx % 500 == 0:
            print(f"[build] triangle reps processed: {rep_idx}/{len(reps)}", flush=True)


def add_core_all_different_constraints(
    obj: ModelObjects,
    reps: list[tuple[int, int, int]],
    limit: int | None = None,
) -> None:
    """
    Add the main Moore-graph / Latin-square-style constraint.

    Fix an ordered branch pair (i,j) and source leaf label a.

    The leaf x=(i,a) has:
        - direct neighbor in branch j:
              b0 = pi_{ij}(a)

        - for every h != i,j, a unique leaf in branch j that shares
          a common neighbor with x through branch h:
              bh = pi_{hj}( pi_{ih}(a) )

    In a Moore graph, as b ranges over labels in branch j:

        - b0 is the unique adjacent leaf in branch j;
        - every other b has exactly one common neighbor with x.

    Therefore the 56 labels

        { pi_{ij}(a) } union { pi_{hj}( pi_{ih}(a) ) : h != i,j }

    must be all different. Since they are 56 values in a 56-element domain,
    they automatically cover all labels 0..55.

    This single AllDifferent constraint simultaneously enforces:
        - no triangles through a third branch,
        - no 4-cycles from two distinct common-neighbor branches,
        - diameter-2 coverage for leaves in different branches.

    Because D38-equivariance is already imposed, we add this only for
    orbit representatives of (i,j,a).
    """
    model = obj.model
    pi = obj.pi

    selected_reps = reps if limit is None else reps[:limit]

    for rep_idx, (i, j, a) in enumerate(selected_reps):
        vals: list[cp_model.IntVar | cp_model.LinearExpr] = []

        # Direct neighbor label in branch j.
        vals.append(pi[(i, j)][a])

        # Common-neighbor labels in branch j, one candidate for each h.
        for h in range(N_BRANCHES):
            if h == i or h == j:
                continue

            t = new_aux(obj, "core")
            model.AddElement(pi[(i, h)][a], pi[(h, j)], t)
            vals.append(t)

        assert len(vals) == N_LABELS
        model.AddAllDifferent(vals)

        if rep_idx > 0 and rep_idx % 250 == 0:
            print(
                f"[build] core reps processed: {rep_idx}/{len(selected_reps)}",
                flush=True,
            )


# ---------------------------------------------------------------------------
# Diagnostics
# ---------------------------------------------------------------------------


def count_tau_fixed_vertices_under_normal_form() -> int:
    """
    Count fixed vertices of tau in the selected normal form.

    Vertices:
      - root u
      - 57 branch vertices
      - 57*56 leaves

    Expected:
      1 root + 1 branch + 54 leaves = 56.
    """
    count = 1  # root u

    for b in range(N_BRANCHES):
        if tau_branch(b) == b:
            count += 1

    for b in range(N_BRANCHES):
        tb = tau_branch(b)
        for a in range(N_LABELS):
            ta = tau_label_value(b, a)
            if tb == b and ta == a:
                count += 1

    return count


def print_group_sanity() -> None:
    print("[sanity] D38 branch/label normal form")
    print(f"  branches: {N_BRANCHES}")
    print(f"  labels per branch: {N_LABELS}")
    print(f"  tau-fixed vertices count: {count_tau_fixed_vertices_under_normal_form()}")
    print(f"  fixed branch under tau: {branch_str(branch(0, 0))}")

    # Check r^19 = identity on branches.
    for b in range(N_BRANCHES):
        x = b
        for _ in range(P_ORDER):
            x = r_branch(x)
        assert x == b

    # Check tau^2 = identity on branch-label pairs.
    for b in range(N_BRANCHES):
        for a in range(N_LABELS):
            tb, ta = tau_vertex(b, a)
            ttb, tta = tau_vertex(tb, ta)
            assert (ttb, tta) == (b, a)

    # Check tau r tau = r^-1 on branch-label pairs.
    for b in range(N_BRANCHES):
        for a in range(N_LABELS):
            # tau r tau
            x_b, x_a = tau_vertex(b, a)
            x_b, x_a = r_vertex(x_b, x_a)
            x_b, x_a = tau_vertex(x_b, x_a)

            # r^-1
            y_b = branch(branch_orbit(b), branch_pos(b) - 1)
            y_a = a

            assert (x_b, x_a) == (y_b, y_a)

    print("  group relations checked: r^19=1, tau^2=1, tau*r*tau=r^-1")


def print_model_stats(obj: ModelObjects, started_at: float) -> None:
    proto = obj.model.Proto()
    elapsed = time.perf_counter() - started_at
    print("[model]")
    print(f"  variables: {len(proto.variables):,}")
    print(f"  constraints: {len(proto.constraints):,}")
    print(f"  aux vars created by script: {obj.aux_count:,}")
    print(f"  build time: {elapsed:.2f}s")


def print_solution_sample(
    solver: cp_model.CpSolver,
    obj: ModelObjects,
    pairs: Iterable[tuple[int, int]] = ((0, 1), (0, 19), (0, 38), (1, 2)),
) -> None:
    print("[solution sample]")
    for i, j in pairs:
        if i == j:
            continue
        vals = [solver.Value(x) for x in obj.pi[(i, j)]]
        head = vals[:20]
        print(f"  pi[{branch_str(i)} -> {branch_str(j)}][0:20] = {head}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="D38-equivariant OR-Tools CP-SAT prototype for degree-57 Moore graph."
    )

    parser.add_argument(
        "--level",
        choices=["equiv", "triangle", "core"],
        default="core",
        help=(
            "Constraint level. "
            "'equiv' = permutations + inverse + D38-equivariance only; "
            "'triangle' = also forbid leaf triangles; "
            "'core' = full AllDifferent common-neighbor constraints."
        ),
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=3600.0,
        help="CP-SAT time limit in seconds.",
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=8,
        help="Number of CP-SAT search workers.",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=1,
        help="CP-SAT random seed.",
    )
    parser.add_argument(
        "--log",
        action="store_true",
        help="Enable OR-Tools search progress logging.",
    )
    parser.add_argument(
        "--core-limit",
        type=int,
        default=None,
        help=(
            "Debug option: only add the first N core representative constraints. "
            "Ignored unless --level core."
        ),
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Build the model and exit without solving.",
    )

    return parser.parse_args()


def main() -> int:
    args = parse_args()
    started_at = time.perf_counter()

    print_group_sanity()

    print("[build] creating base model: permutations + inverse + D38-equivariance")
    obj = build_base_model()

    reps: list[tuple[int, int, int]] = []
    if args.level in {"triangle", "core"}:
        print("[build] computing D38 orbit representatives for (i,j,a)")
        reps = ordered_pair_label_representatives()
        obj.core_reps = reps
        print(f"[build] orbit representatives: {len(reps):,}")

    if args.level == "triangle":
        print("[build] adding triangle-forbidding constraints")
        add_triangle_constraints(obj, reps)

    if args.level == "core":
        print("[build] adding core AllDifferent common-neighbor constraints")
        if args.core_limit is not None:
            print(f"[build] core-limit enabled: {args.core_limit}")
        add_core_all_different_constraints(obj, reps, limit=args.core_limit)

    print_model_stats(obj, started_at)

    if args.dry_run:
        print("[dry-run] model built; not solving")
        return 0

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.timeout
    solver.parameters.num_search_workers = args.workers
    solver.parameters.random_seed = args.seed
    solver.parameters.log_search_progress = args.log
    solver.parameters.symmetry_level = 2

    print("[solve]")
    print(f"  level: {args.level}")
    print(f"  timeout: {args.timeout}s")
    print(f"  workers: {args.workers}")
    print(f"  seed: {args.seed}")
    print("  note: INFEASIBLE here is experimental; no UNSAT certificate is emitted")

    solve_started = time.perf_counter()
    status = solver.Solve(obj.model)
    solve_elapsed = time.perf_counter() - solve_started

    print("[result]")
    print(f"  status: {solver.StatusName(status)}")
    print(f"  solve time: {solve_elapsed:.2f}s")
    print(f"  wall time reported by solver: {solver.WallTime():.2f}s")
    print(f"  conflicts: {solver.NumConflicts():,}")
    print(f"  branches: {solver.NumBranches():,}")

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        print("  interpretation: SAT/FEASIBLE candidate under the selected constraint level")
        print_solution_sample(solver, obj)
    elif status == cp_model.INFEASIBLE:
        print("  interpretation: experimentally UNSAT for this model/level")
    elif status == cp_model.UNKNOWN:
        print("  interpretation: timeout or search stopped before SAT/UNSAT was decided")
    elif status == cp_model.MODEL_INVALID:
        print("  interpretation: OR-Tools rejected the model as invalid")
    else:
        print("  interpretation: unexpected solver status")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())