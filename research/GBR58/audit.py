"""Audit newly located delta sources without modifying or copying them.

This is a small, independent finite reproduction, not a Goldbach proof or a
reproduction of the historical billion-scale experiments.
"""
from fractions import Fraction
import hashlib
import json
from math import isqrt
from pathlib import Path
import re
import subprocess
import tempfile

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
DATA = ROOT.parent / 'data'
SOURCE_NAMES = (
    'segmented_sieve_delta.c',
    'DeltaMod3.lean',
    'delta_toolkit/delta_toolkit_v2/delta_scan.cpp',
    'delta_toolkit/delta_toolkit_v2/analyze_patterns.py',
    'under_weak_conjecture_topic/delta_min_cousin_centers.py',
)
DELTAS = tuple(range(3, 46, 6))


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def hits(p, d):
    return prime(p + 1 - d) and prime(p + 1 + d)


def offsets(d):
    return sorted({0, d - 1, 2 * d, d + 3})


def local_factor(d, ell):
    pattern = offsets(d)
    nu = len({h % ell for h in pattern})
    return (1 - Fraction(nu, ell)) / (1 - Fraction(1, ell)) ** len(pattern)


def main():
    sources = {name: {'bytes': (DATA / name).stat().st_size,
                      'sha256': digest(DATA / name)} for name in SOURCE_NAMES}
    runs = []
    with tempfile.TemporaryDirectory(prefix='gbr58-') as temp:
        binary = Path(temp) / 'historical-sieve'
        subprocess.run(['gcc', '-O2', '-std=c11',
                        str(DATA / 'segmented_sieve_delta.c'), '-lm', '-o', str(binary)],
                       check=True, capture_output=True, text=True)
        for limit in (100, 1000, 10000):
            output = subprocess.run([str(binary), str(limit)], check=True,
                                    capture_output=True, text=True).stdout
            actual_pairs = int(re.search(r'cousin pairs found: (\d+)', output)[1])
            actual_counts = {int(d): int(count) for d, count in
                             re.findall(r'^\s*(\d+)\s+(\d+)\s+[\d.]+\s*$', output, re.M)}
            # Include p=3 here because the historical program's specification
            # does. Report it separately from the intended p>3 cousin problem.
            pairs = [p for p in range(3, limit - 3, 2)
                     if prime(p) and prime(p + 4)]
            root = isqrt(limit) + 1
            surviving = [p for p in pairs if p > root]
            expected_counts = {d: sum(hits(p, d) for p in pairs) for d in DELTAS}
            predicted_legacy = {d: sum(hits(p, d) for p in surviving) for d in DELTAS}
            assert actual_pairs == len(surviving)
            assert actual_counts == predicted_legacy
            assert actual_pairs < len(pairs)
            assert any(actual_counts[d] != expected_counts[d] for d in DELTAS)
            runs.append(dict(limit=limit, small_prime_table_limit=root,
                             expected_pairs_including_p3=len(pairs),
                             expected_pairs_with_p_gt_3=sum(p > 3 for p in pairs),
                             historical_pairs=actual_pairs,
                             missing_pairs=[p for p in pairs if p <= root],
                             expected_counts=expected_counts,
                             historical_counts=actual_counts))

    # A source-specific quantifier check: every column has hits, while one
    # particular centre can still be missed by their union.
    pairs_100 = [p for p in range(7, 97, 2) if prime(p) and prime(p + 4)]
    column_counts = {d: sum(hits(p, d) for p in pairs_100) for d in (3, 9)}
    assert all(column_counts.values())
    assert prime(67) and prime(71)
    assert not hits(67, 3) and not hits(67, 9) and hits(67, 15)

    # d=3 has a repeated shift, hence only three distinct prime conditions.
    assert offsets(3) == [0, 2, 6]
    assert all(len(offsets(d)) == 4 for d in range(9, 1000, 6))
    factors = []
    for ell in (2, 3, 5, 7, 11, 13):
        corrected = local_factor(3, ell)
        nu = len({h % ell for h in offsets(3)})
        historical = (1 - Fraction(nu, ell)) / (1 - Fraction(1, ell)) ** 4
        assert historical / corrected == Fraction(ell, ell - 1)
        factors.append(dict(prime=ell, corrected=str(corrected),
                            historical=str(historical),
                            historical_over_corrected=str(historical / corrected)))

    legacy_lean = subprocess.run(['lake', 'env', 'lean', str(DATA / 'DeltaMod3.lean')],
                                 cwd=ROOT, capture_output=True, text=True)
    assert legacy_lean.returncode == 1 and 'error: unsolved goals' in legacy_lean.stdout

    assert all(digest(DATA / name) == info['sha256'] for name, info in sources.items())
    result = dict(all_checks_passed=True, source_root=str(DATA), source_files=sources,
                  historical_segmented_sieve_runs=runs,
                  quantifier_example=dict(p_bound=100, deltas=[3, 9],
                                          column_counts=column_counts,
                                          missed_p=67, successful_later_delta=15),
                  delta_3_pattern=offsets(3), delta_3_distinct_conditions=3,
                  delta_3_local_factors=factors,
                  historical_lean=dict(exit_code=legacy_lean.returncode,
                                       diagnostic=legacy_lean.stdout.strip()),
                  scope='Three small historical-C executions checked by independent trial division; exact listed local factors and quantifier example; historical Lean module failure reproduced. No full historical data reproduction, EH implication, asymptotic prediction, or general Goldbach proof.')
    (BASE / 'verification.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
