"""Check witness-independent transfers on the existing fixed target domain."""
from bisect import bisect_left
from math import isqrt
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
TARGET_FILE = ROOT.parent/'GBR67/results.json'


def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


def main():
    targets = json.loads(TARGET_FILE.read_text())['targets']
    assert len(targets) == 114 and max(targets) <= 500
    bound = 4*max(targets)
    mask = bytearray([1])*(bound+1)
    mask[:2] = bytes(2)
    for p in range(2, isqrt(bound)+1):
        if mask[p]:
            mask[p*p::p] = bytes((bound-p*p)//p+1)
    primes = [p for p in range(3, bound+1) if mask[p]]
    prime_set = set(primes)

    def level(m):
        c = m//2
        i = bisect_left(primes, c)
        return 0 if primes[i] == c else (primes[i]-primes[i-1])//2

    pairs = {m: [(a, m-a) for a in primes if a <= m-a and m-a in prime_set]
             for m in range(6, 2*max(targets)+1, 2)}
    successes, failures = [], []
    for n in targets:
        sources = [m for m in range(6, 2*n+1, 2) if level(m) < level(n)]
        good = []
        blockers = []
        for m in sources:
            assert pairs[m]
            bad = next(((a,b) for a,b in pairs[m]
                        if n-a not in prime_set and n-b not in prime_set), None)
            if bad is None:
                good.append(m)
            else:
                blockers.append({'M': m, 'unsafe_pair': list(bad)})
        if good:
            m = min(good, key=lambda x: (abs(n-x), x))
            successes.append({'N': n, 'M': m, 'source_level': level(m),
                              'target_level': level(n),
                              'all_source_pairs': [list(p) for p in pairs[m]]})
        else:
            failures.append({'N': n, 'source_cap': 2*n, 'all_sources': blockers})

    # Independent trial-division check of each positive universal statement.
    def direct_level(m):
        c = m//2
        if trial_prime(c):
            return 0
        p = next(x for x in range(c-1, 1, -1) if trial_prime(x))
        q = next(x for x in range(c+1, bound+1) if trial_prime(x))
        return (q-p)//2

    for cert in successes:
        n, m = cert['N'], cert['M']
        assert direct_level(m) < direct_level(n)
        actual = [[a,m-a] for a in range(3,m//2+1,2)
                  if trial_prime(a) and trial_prime(m-a)]
        assert actual == cert['all_source_pairs'] and actual
        assert all(trial_prime(n-a) or trial_prime(n-b) for a,b in actual)
    for failure in failures:
        n = failure['N']
        expected = [m for m in range(6,2*n+1,2) if direct_level(m) < direct_level(n)]
        assert expected == [c['M'] for c in failure['all_sources']]
        for row in failure['all_sources']:
            a,b = row['unsafe_pair']
            assert a+b == row['M'] and trial_prime(a) and trial_prime(b)
            assert not trial_prime(n-a) and not trial_prime(n-b)

    result = {'all_finite_checks_passed': True,
              'scope': 'Existing 114 noncentral targets with center<=250; '
                       'sources 6<=M<=2N with strictly lower gap level only. '
                       'A failure says nothing about sources above 2N or other proof rules.',
              'successes': successes, 'failures': failures}
    (ROOT/'results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'all_finite_checks_passed': True, 'targets': len(targets),
                      'universally_safe_source_certificates': len(successes),
                      'no_source_in_declared_pool': [r['N'] for r in failures]}))


if __name__ == '__main__':
    main()
