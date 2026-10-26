"""Classify the existing R68 selected sources, without extending its search."""
from collections import Counter
from math import isqrt
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def main():
    original = json.loads((ROOT.parent / 'GBR68/results.json').read_text())
    assert len(original['successes']) == 113
    assert [row['N'] for row in original['failures']] == [148]
    rows = []
    for cert in original['successes']:
        n, m = cert['N'], cert['M']
        c = m // 2
        assert m % 2 == 0
        if prime(c):
            kind, pair = 'prime_center', [c, c]
            source_level = 0
        else:
            p = next(x for x in range(c - 1, 1, -1) if prime(x))
            q = next(x for x in range(c + 1, 2 * c) if prime(x))
            source_level = (q - p) // 2
            kind = 'adjacent_center' if p + q == m else 'noncentral_window'
            pair = [p, q] if kind == 'adjacent_center' else None
        assert source_level == cert['source_level'] < cert['target_level']
        actual = [[a, m - a] for a in range(3, m // 2 + 1, 2)
                  if prime(a) and prime(m - a)]
        assert actual == cert['all_source_pairs'] and actual
        assert all(prime(n - a) or prime(n - b) for a, b in actual)
        row = {'N': n, 'M': m, 'kind': kind, 'source_level': source_level}
        if pair is not None:
            assert pair in actual
            a = next(a for a in pair if prime(n - a))
            row['automatic_source_pair'] = pair
            row['direct_target_pair'] = [a, n - a]
            assert prime(a) and prime(n - a)
        rows.append(row)
    counts = dict(Counter(row['kind'] for row in rows))
    assert counts == {'noncentral_window': 50, 'adjacent_center': 17, 'prime_center': 46}
    summary = {'all_checks_passed': True, 'selected_certificates': len(rows),
               'counts': counts,
               'scope': 'Only the existing 113 selected R68 safe-source certificates; '
                        'no claim that other sources are unavailable, and no new search range.'}
    (ROOT / 'results.json').write_text(json.dumps({**summary, 'rows': rows}, indent=2) + '\n')
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
