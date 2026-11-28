"""Exact, small-graph prototype for a future Reusable matching-root atlas.

This computes and cross-checks polynomial data. It is not a Lean certificate:
the graph-to-polynomial adapter and Sturm replay remain to be formalized.
"""

from __future__ import annotations

import itertools
import json
import argparse
from functools import lru_cache
from pathlib import Path

import sympy as sp


X = sp.Symbol("x")
DEFAULT_THRESHOLD = sp.Rational(7, 5)


def matchings_by_size(vertices: tuple[int, ...], edges: tuple[tuple[int, int], ...]) -> list[int]:
    counts = [1]
    for k in range(1, len(vertices) // 2 + 1):
        counts.append(sum(
            len({v for edge in chosen for v in edge}) == 2 * k
            for chosen in itertools.combinations(edges, k)
        ))
    return counts


def matching_poly_from_counts(n: int, counts: list[int]) -> sp.Poly:
    return sp.Poly(sum((-1) ** k * m * X ** (n - 2 * k)
                       for k, m in enumerate(counts)), X, domain="ZZ")


@lru_cache(maxsize=None)
def matching_poly_by_deletion(vertices: tuple[int, ...],
                              edges: tuple[tuple[int, int], ...]) -> sp.Poly:
    """Independent recurrence: μ(G) = μ(G−e) − μ(G−u−v)."""
    if not edges:
        return sp.Poly(X ** len(vertices), X, domain="ZZ")
    u, v = edges[0]
    deleted_edge = matching_poly_by_deletion(vertices, edges[1:])
    kept_vertices = tuple(w for w in vertices if w not in (u, v))
    kept_edges = tuple(e for e in edges if u not in e and v not in e)
    return deleted_edge - matching_poly_by_deletion(kept_vertices, kept_edges)


def inspect_graph(name: str, n: int, edge_list: list[tuple[int, int]],
                  threshold: sp.Rational = DEFAULT_THRESHOLD) -> dict:
    if not 0 <= n <= 12 or len(edge_list) > 18 or any(len(e) != 2 for e in edge_list):
        raise ValueError("Prototype accepts up to 12 vertices and 18 simple edges")
    edges = tuple(sorted(tuple(sorted(e)) for e in edge_list))
    if any(u == v or u < 0 or v >= n for u, v in edges) or len(set(edges)) != len(edges):
        raise ValueError("Expected a simple graph on vertices 0,...,n-1")
    vertices = tuple(range(n))
    counts = matchings_by_size(vertices, edges)
    poly = matching_poly_from_counts(n, counts)
    if poly != matching_poly_by_deletion(vertices, edges):
        raise AssertionError("Matching enumeration and deletion recurrence disagree")

    unit, factors = poly.sqf_list()
    if unit not in (1, -1):
        raise AssertionError("Unexpected squarefree factorization unit")
    above = 0
    real = 0
    factor_data = []
    for factor, multiplicity in factors:
        strict_above = int(factor.count_roots(threshold, sp.oo)) - int(factor.eval(threshold) == 0)
        all_real = int(factor.count_roots(-sp.oo, sp.oo))
        above += multiplicity * strict_above
        real += multiplicity * all_real
        factor_data.append({"factor": str(factor.as_expr()), "multiplicity": multiplicity,
                            "distinct_roots_above": strict_above})
    if real != n:
        raise AssertionError("Exact root count did not cover the polynomial degree")
    return {"graph": name, "vertices": n, "edges": edges,
            "matching_counts": counts, "matching_polynomial": str(poly.as_expr()),
            "threshold": str(threshold), "roots_above_with_multiplicity": above,
            "squarefree_factors": factor_data,
            "checks": {"deletion_recurrence": True, "all_roots_real_exact": True}}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--threshold", default="7/5", help="exact rational threshold, e.g. 7/5")
    parser.add_argument("--input", type=Path, help="JSON graph with name, vertices, edges")
    args = parser.parse_args()
    threshold = sp.Rational(args.threshold)
    if args.input:
        graph = json.loads(args.input.read_text(encoding="utf-8"))
        results = [inspect_graph(graph.get("name", args.input.stem), graph["vertices"],
                                 graph["edges"], threshold)]
    else:
        results = [inspect_graph("P4", 4, [(0, 1), (1, 2), (2, 3)], threshold),
                   inspect_graph("2K2", 4, [(0, 1), (2, 3)], threshold)]
    # A changed coefficient must fail the independent graph-to-polynomial check.
    p4 = matching_poly_from_counts(4, [1, 4, 1])
    assert p4 != matching_poly_by_deletion(tuple(range(4)), ((0, 1), (1, 2), (2, 3)))
    print(json.dumps({"results": results, "mutated_coefficient_rejected": True},
                     ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
