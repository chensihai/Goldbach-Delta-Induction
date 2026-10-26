"""Independent reconstruction of GB-R43--52 and bounded-anchor audit.

Python standard library only. All primality decisions use a complete sieve.
This is finite evidence, not an asymptotic theorem or a Lean certificate.
"""
from itertools import combinations
from math import isqrt
from pathlib import Path
import json


def sieve(n):
    flag = bytearray(b'\x01') * (n + 1)
    flag[:2] = b'\x00\x00'
    for r in range(2, isqrt(n) + 1):
        if flag[r]:
            flag[r*r:n+1:r] = b'\x00' * ((n-r*r)//r + 1)
    return flag


def labels(mask):
    return [j+1 for j in range(mask.bit_length()) if mask >> j & 1]


def qpass(n, small):
    return n >= 2 and all(n == r or n % r for r in small)


def crt_capacity(p, js, z, primes):
    # The maximum is a maximum admissible subset, not a product of densities.
    for h in range(len(js), -1, -1):
        for sub in combinations(js, h):
            if all(len({0, *((2*p+2*j) % r for j in sub)}) < r
                   for r in primes if r <= z):
                return h
    raise AssertionError('empty subset always admissible')


def reconstruct(limit=1000):
    flag = sieve(5*limit + 100)
    primes = [n for n in range(2, len(flag)) if flag[n]]
    bad = []
    interval_count = 0
    for p, q in zip(primes, primes[1:]):
        if p > limit:
            break
        if p < 5 or q-p < 4:
            continue
        interval_count += 1
        m = q-p-1
        J = (1 << m)-1
        anchors = [a for a in primes if 3 <= a <= p]
        cover = {a: sum(1 << (j-1) for j in range(1, m+1)
                        if flag[2*p+2*j-a]) for a in anchors}
        union = 0
        for mask in cover.values():
            union |= mask
        assert union == J, (p, 'uncovered label; classification needs revision')
        edges = {(i, j) for i, j in combinations(range(1, m+1), 2)
                 if any(mask & (1 << (i-1)) and mask & (1 << (j-1))
                        for mask in cover.values())}
        for sub in combinations(range(1, m+1), 4):
            i, j, u, v = sub
            matching = (((i,j) in edges and (u,v) in edges)
                        or ((i,u) in edges and (j,v) in edges)
                        or ((i,v) in edges and (j,u) in edges))
            R = sum(1 << (j-1) for j in sub)
            triple = any((mask & R).bit_count() >= 3 for mask in cover.values())
            if matching or triple:
                continue
            # Independent exact check of the structural shortcut.
            assert max(((x | y) & R).bit_count()
                       for x, y in combinations(cover.values(), 2)) < 4
            seen = {J}
            todo = [(J, [])]
            frontiers = []
            while todo:
                S, path = todo.pop()
                assert S != R, ('target reachable', p, sub)
                g = max((mask & S).bit_count() for mask in cover.values())
                safe = [a for a, mask in cover.items()
                        if not mask & R and (mask & S).bit_count() == g]
                if not safe:
                    frontiers.append((S, path, g))
                for a in safe:
                    nxt = S & ~cover[a]
                    assert nxt != R, ('one-step arrival', p, sub)
                    if nxt not in seen:
                        seen.add(nxt)
                        todo.append((nxt, path + [a]))
            assert len(frontiers) == 1, (p, sub, 'multiple frontiers')
            S, path, g = frontiers[0]
            b = min(a for a, mask in cover.items() if (mask & S).bit_count() == g)
            T = S & ~R
            row = dict(p=p, q=q, R=list(sub), S=labels(S), T=labels(T),
                       protected_path=path, witness=b, h=g,
                       witness_primes=[2*p+2*j-b for j in labels(S & cover[b])],
                       levels=[])
            for z in (3,5,7,11,13,17,19,23,31,47):
                small = [r for r in primes if r <= z]
                js = labels(T)
                cap = lambda a: sum(qpass(2*p+2*j-a, small) for j in js)
                prime_cap = max(cap(a) for a in anchors)
                raw_high = [a for a in range(3, p+1, 2) if cap(a) >= g]
                bounded = [a for a in range(3, p+1, 2) if qpass(a, small)]
                high = [a for a in bounded if cap(a) >= g]
                bounded_cap = max(map(cap, bounded), default=0)
                composite_high = []
                for a in high:
                    if prime_cap < g:
                        assert not flag[a], (p, sub, z, 'prime high anchor')
                    factor = next((r for r in primes if r <= isqrt(a) and a % r == 0), None)
                    composite_high.append(dict(a=a, factor=factor, is_prime=bool(flag[a])))
                Aplus = [a for a in anchors if not any(
                    2*p+2*j-a <= z*z and qpass(2*p+2*j-a, small) for j in sub)]
                safe_cap = max(map(cap, Aplus), default=0)
                pure = crt_capacity(p, js, z, primes)
                # Exact small-prime anchors are needed for a valid CRT bound.
                small_exact = max(((cover[a] & T).bit_count()
                                   for a in anchors if a <= z), default=0)
                small_sift = max((cap(a) for a in anchors if a <= z), default=0)
                crt_exact_small = max(pure, small_exact)
                crt_sift_small = max(pure, small_sift)
                assert prime_cap <= bounded_cap
                assert safe_cap <= prime_cap
                assert prime_cap <= crt_sift_small
                row['levels'].append(dict(z=z, prime_capacity=prime_cap,
                    safe_outer_capacity=safe_cap, pure_crt=pure,
                    crt_exact_small=crt_exact_small, crt_sift_small=crt_sift_small,
                    bounded_sieve_capacity=bounded_cap,
                    raw_high_count=len(raw_high), raw_high=raw_high,
                    sifted_high=composite_high,
                    anchor_sieve_exact=p < next(r for r in primes if r > z)**2))
            bad.append(row)
    return interval_count, bad


def main():
    count, rows = reconstruct()
    summary = []
    for i, z in enumerate((3,5,7,11,13,17,19,23,31,47)):
        summary.append(dict(z=z, **{
            key: sum(row['levels'][i][key] < row['h'] for row in rows)
            for key in ('prime_capacity','safe_outer_capacity','pure_crt',
                        'crt_exact_small','crt_sift_small','bounded_sieve_capacity')},
            no_raw_high=sum(not row['levels'][i]['raw_high'] for row in rows),
            no_sifted_high=sum(not row['levels'][i]['sifted_high'] for row in rows),
            sifted_high_total=sum(len(row['levels'][i]['sifted_high']) for row in rows)))
    result = dict(scope='p <= 1000, q the next prime, q-p >= 4',
                  interval_count=count, bad_four_count=len(rows),
                  protected_depths={str(n):sum(len(row['protected_path']) == n
                                              for row in rows) for n in (0,1)},
                  summary=summary, cases=rows)
    out = Path(__file__).with_name('results.json')
    out.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k != 'cases'}, indent=2))


if __name__ == '__main__':
    main()
