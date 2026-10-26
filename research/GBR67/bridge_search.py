"""Bounded source-compatible rectangles; finite evidence, not an induction proof."""
from bisect import bisect_left
from math import isqrt
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
MAX_CENTER = 250


def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def main():
    bound = 4 * MAX_CENTER
    sieve = bytearray([1]) * (bound + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(bound) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((bound - p*p) // p + 1)
    primes = [p for p in range(3, bound + 1) if sieve[p]]

    def enclosing(center):
        index = bisect_left(primes, center)
        if primes[index] == center:
            return center, center
        return primes[index - 1], primes[index]

    def level(total):
        p, q = enclosing(total // 2)
        return (q - p) // 2

    bases = [(p, q) for p, q in zip(primes, primes[1:]) if q - p == 4]
    def base_window(total):
        return next(((p, q) for p, q in bases if 2*p <= total <= 2*q), None)

    endpoints = {n: [a for a in primes if a < n - 2 and sieve[n-a]]
                 for n in range(6, 2*MAX_CENTER + 1, 2)}
    endpoint_sets = {n: set(a) for n, a in endpoints.items()}
    certificates = []
    symmetric_failures = []
    asymmetric_failures = []
    targets = []
    for center in range(3, MAX_CENTER + 1):
        p, q = enclosing(center)
        k = (q - p) // 2
        if k < 3 or center == (p + q) // 2:
            continue
        n = 2 * center
        targets.append(n)
        ls = [l for l in range(14, n, 2) if base_window(l)]
        symmetric = None
        rows = []
        for l in ls:
            if (n + l) % 4:
                continue
            m = (n + l) // 2
            if level(m) >= k:
                continue
            shared = endpoint_sets[l] & endpoint_sets[m]
            rows.append({'L': l, 'M': m, 'shared': sorted(shared),
                         'reflection_hits': [a for a in sorted(shared) if l-a in shared]})
            if rows[-1]['reflection_hits'] and symmetric is None:
                symmetric = l, m
        if symmetric is None:
            symmetric_failures.append({'N': n, 'p': p, 'q': q, 'k': k,
                                       'all_eligible_sources': rows})
        found = None
        for l in ls:
            for m1 in range(l + 2, n, 2):
                m2 = n + l - m1
                if level(m1) >= k or level(m2) >= k:
                    continue
                for a in endpoints[l]:
                    b = l - a
                    c, d = m2 - b, m1 - a
                    if c >= 3 and d >= 3 and sieve[c] and sieve[d]:
                        found = {'N': n, 'p': p, 'q': q, 'k': k,
                                 'L': l, 'M1': m1, 'M2': m2,
                                 'a': a, 'b': b, 'c': c, 'd': d,
                                 'base_window': list(base_window(l))}
                        break
                if found:
                    break
            if found:
                break
        if found:
            certificates.append(found)
        else:
            asymmetric_failures.append(n)

    # Check every claimed positive certificate by trial division, independent
    # of the sieve used to find it. Check source levels by direct interval scans.
    def direct_level(total):
        center = total // 2
        if trial_prime(center):
            return 0
        left = next(x for x in range(center-1, 1, -1) if trial_prime(x))
        right = next(x for x in range(center+1, bound+1) if trial_prime(x))
        return (right-left)//2

    def direct_base(total):
        return any(2*s <= total <= 2*(s+4) and trial_prime(s) and trial_prime(s+4)
                   and not any(trial_prime(x) for x in range(s+1, s+4))
                   for s in range(3, total//2+1, 2))

    for cert in certificates:
        n, p, q, k = (cert[key] for key in ('N', 'p', 'q', 'k'))
        a, b, c, d = (cert[key] for key in ('a', 'b', 'c', 'd'))
        l, m1, m2 = (cert[key] for key in ('L', 'M1', 'M2'))
        assert all(trial_prime(x) for x in (a, b, c, d, p, q))
        assert q-p == 2*k and not any(trial_prime(x) for x in range(p+1, q))
        assert 2*p < n < 2*q and n != p+q
        assert a+b == l and a+d == m1 and c+b == m2 and c+d == n
        assert m1+m2-l == n and l < m1 < n and l < m2 < n
        assert direct_level(m1) < k and direct_level(m2) < k
        s, t = cert['base_window']
        assert t-s == 4 and all(trial_prime(x) for x in (s, t))
        assert not any(trial_prime(x) for x in range(s+1, t))
        assert 2*s <= l <= 2*t
    for failure in symmetric_failures:
        n, k = failure['N'], failure['k']
        eligible = []
        for l in range(14, n, 2):
            if not direct_base(l) or (n+l) % 4:
                continue
            m = (n+l)//2
            if direct_level(m) >= k:
                continue
            eligible.append(l)
            shared = {a for a in range(3, l-2, 2)
                      if all(trial_prime(x) for x in (a, l-a, m-a))}
            assert not any(l-a in shared for a in shared)
        assert eligible == [r['L'] for r in failure['all_eligible_sources']]

    result = {'all_finite_checks_passed': True,
              'scope': 'Every noncentral target with center<=250 and k>=3. '
                       'Compatible witnesses are checked as arithmetic facts; '
                       'they are NOT inferred from Boolean Goldbach premises.',
              'max_center': MAX_CENTER, 'targets': targets,
              'symmetric_failures': symmetric_failures,
              'asymmetric_failures': asymmetric_failures,
              'certificates': certificates}
    (ROOT/'results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'all_finite_checks_passed': True, 'targets': len(targets),
                      'symmetric_failures': [r['N'] for r in symmetric_failures],
                      'asymmetric_failures': asymmetric_failures,
                      'independently_checked_certificates': len(certificates)}))


if __name__ == '__main__':
    main()
