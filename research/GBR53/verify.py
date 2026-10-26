"""Independent arithmetic checker: does not import audit.py or its sieve.

Checks every branch of the modular proof, and the explicit prime witness.
It certifies blocking at the supplied frontier, not universal reachability.
"""
from math import isqrt
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).parent


def prime(n):
    return n >= 2 and all(n%d for d in range(2,isqrt(n)+1))


def main():
    certs = json.loads((BASE/'certificates.json').read_text())
    sieve_primes = [n for n in range(3,24,2) if prime(n)]
    verified_nodes = 0
    protected_state_count = 0
    for c in certs:
        p,q,h = c['p'],c['q'],c['h']
        assert prime(p) and prime(q) and all(not prime(n) for n in range(p+1,q))
        assert set(c['R']) <= set(c['S']) <= set(range(1,q-p))
        assert set(c['T']) == set(c['S'])-set(c['R'])
        assert p+2 > 23
        # This separate reachability check DOES enumerate actual prime anchors.
        # The modular capacity proof below does not need this list.
        anchors = [a for a in range(3,p+1,2) if prime(a)]
        covers = {a:{j for j in range(1,q-p) if prime(2*p+2*j-a)} for a in anchors}
        R = set(c['R'])
        assert max(len((covers[a] | covers[b]) & R)
                   for a in anchors for b in anchors if a != b) < 4
        seen = {frozenset(range(1,q-p))}
        todo = list(seen)
        frontiers = set()
        while todo:
            S = todo.pop()
            assert set(S) != R
            g = max(len(mask & S) for mask in covers.values())
            safe = [a for a in anchors if not covers[a] & R and len(covers[a] & S) == g]
            if not safe:
                frontiers.add(S)
            for a in safe:
                nxt = frozenset(set(S)-covers[a])
                assert set(nxt) != R
                if nxt not in seen:
                    seen.add(nxt)
                    todo.append(nxt)
        assert frontiers == {frozenset(c['S'])}
        protected_state_count += len(seen)
        assert max(len(mask & set(c['S'])) for mask in covers.values()) == h
        a = c['witness']
        assert prime(a) and 3 <= a <= p
        assert len(set(c['witness_primes'])) == h
        assert all(prime(n) and (n+a-2*p)//2 in c['S'] and (n+a-2*p)%2 == 0
                   for n in c['witness_primes'])
        assert {x['a'] for x in c['small_anchor_checks']} == set(sieve_primes)
        for check in c['small_anchor_checks']:
            assert set(map(int,check['divisors'])) == set(c['T'])
            surviving = 0
            for j_s,ell in check['divisors'].items():
                if ell is None:
                    surviving += 1
                else:
                    n = 2*p+2*int(j_s)-check['a']
                    assert prime(ell) and ell <=23 and n > ell and n%ell == 0
            assert surviving < h

        def verify(node, r, M, active, depth):
            nonlocal verified_nodes
            verified_nodes += 1
            if node['kind'] == 'capacity':
                assert len(active) < h
                return
            assert node['kind'] == 'split' and depth < len(sieve_primes)
            ell = sieve_primes[depth]
            expected = set()
            for k in range(ell):
                rr,mm = r+M*k,M*ell
                # Derive the occupied subclasses independently, by interval quotients.
                lo = (24-rr+mm-1)//mm
                hi = (p-rr)//mm
                if lo > hi:
                    continue
                expected.add(str(k))
                child = node['children'][str(k)]
                if child['kind'] == 'anchor_factor':
                    verified_nodes += 1
                    assert rr%ell == 0 and 24 > ell
                else:
                    nxt = [j for j in active if (2*p+2*j-rr)%ell != 0]
                    verify(child, rr, mm, nxt, depth+1)
            assert set(node['children']) == expected

        verify(c['large_anchor_tree'],1,2,c['T'],0)
        # Independently verify the stronger raw-odd-anchor attribution claim.
        high = [a for a in range(3,p+1,2) if sum(
            all((2*p+2*j-a)%ell for ell in sieve_primes) for j in c['T']) >= h]
        assert high == c['raw_high']
        for a in high:
            d = c['raw_high_factors'][str(a)]
            assert 1 < d < a and a%d == 0
    hashes = {name:hashlib.sha256((BASE/name).read_bytes()).hexdigest()
              for name in ('audit.py','certificates.py','verify.py','results.json','certificates.json')}
    result = dict(all_checks_passed=True,cases=len(certs),verified_tree_nodes=verified_nodes,
                  protected_states=protected_state_count,
                  scope='16 supplied frontiers only; no claim for all prime gaps',sha256=hashes)
    (BASE/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
