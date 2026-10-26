"""Exact prime graphs of A_12 and A_13 from all permutation cycle types.

No GAP, literature theorem, or Goldbach assumption is used by the computation.
An independent edge criterion is checked against the complete cycle-type list.
"""
import hashlib
from itertools import combinations
import json
from math import isqrt, lcm
from pathlib import Path

BASE = Path(__file__).resolve().parent


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def partitions(n, least=1):
    if n == 0:
        yield ()
    for first in range(least, n + 1):
        for tail in partitions(n - first, first):
            yield (first,) + tail


def graph_from_cycles(n):
    types = list(partitions(n))
    # A cycle of length m has sign (-1)^(m-1). Thus a permutation
    # with these cycle lengths belongs to A_n iff n - #cycles is even.
    even_types = [parts for parts in types if (n - len(parts)) % 2 == 0]
    orders = {lcm(*parts) for parts in even_types}
    vertices = sorted(order for order in orders if prime(order))
    edges = [pair for pair in combinations(vertices, 2) if lcm(*pair) in orders]
    return dict(degree=n, cycle_types=len(types), even_cycle_types=len(even_types),
                element_orders=sorted(orders), vertices=vertices, edges=edges)


def graph_from_support(n):
    vertices = [p for p in range(2, n + 1) if prime(p)]
    edges = [(p, q) for p, q in combinations(vertices, 2)
             if (q + 4 <= n if p == 2 else p + q <= n)]
    return vertices, edges


def main():
    graphs = [graph_from_cycles(n) for n in (12, 13)]
    for graph in graphs:
        vertices, edges = graph_from_support(graph['degree'])
        assert graph['vertices'] == vertices
        assert graph['edges'] == edges
    g12, g13 = graphs
    assert g12['cycle_types'] == 77 and g13['cycle_types'] == 101
    assert set(g13['vertices']) - set(g12['vertices']) == {13}
    assert g12['edges'] == g13['edges'] == [
        (2, 3), (2, 5), (2, 7), (3, 5), (3, 7), (5, 7)]
    assert all(13 not in edge for edge in g13['edges'])
    # The paper defines strict graph inclusion to allow a new vertex alone.
    strict_subgraph = (set(g12['vertices']) < set(g13['vertices'])
                      and set(g12['edges']) <= set(g13['edges']))
    assert strict_subgraph
    # Theorem 2.9 would require 2n=3+p with p prime. For n=6, p=9.
    assert 2 * 6 >= 8 and not prime(2 * 6 - 3)
    assert prime(5) and prime(7) and 5 + 7 == 12
    result = dict(all_checks_passed=True, alternating_group_graphs=graphs,
                  strict_subgraph=True, added_vertices=[13], added_edges=[],
                  theorem_2_9_counterexample=dict(n=6, even_number=12,
                                                 forced_p=9, forced_p_is_prime=False),
                  actual_goldbach_representation=[5, 7],
                  scope='Complete cycle-type enumeration for A_12 and A_13, cross-checked with the support-size edge criterion. Refutes the cited Theorem 2.9 as stated; does not refute its Goldbach corollary or prove Goldbach generally.',
                  sha256={name: hashlib.sha256((BASE / name).read_bytes()).hexdigest()
                          for name in ('REPORT.md', 'verify.py')})
    (BASE / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'sha256'}, indent=2))


if __name__ == '__main__':
    main()
