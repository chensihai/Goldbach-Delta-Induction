"""Generate bounded CRT exclusion trees, without listing prime anchors."""
import json
from pathlib import Path

BASE = Path(__file__).parent
ODD_SIEVE_PRIMES = (3, 5, 7, 11, 13, 17, 19, 23)


def first_in_class(r, modulus, lower):
    return r + max(0, (lower-r+modulus-1)//modulus)*modulus


def exclusion_tree(p, T, h, lower, sieve_anchor):
    stats = {'nodes': 0, 'capacity_leaves': 0, 'anchor_factor_leaves': 0}

    def visit(r, modulus, active, depth):
        stats['nodes'] += 1
        if len(active) < h:
            stats['capacity_leaves'] += 1
            return {'kind': 'capacity'}
        if depth == len(ODD_SIEVE_PRIMES):
            raise AssertionError(('high-capacity candidate survives', p, r, active))
        ell = ODD_SIEVE_PRIMES[depth]
        children = {}
        for k in range(ell):
            rr, mm = r+modulus*k, modulus*ell
            if first_in_class(rr, mm, lower) > p:
                continue
            if sieve_anchor and rr % ell == 0:
                assert lower > ell
                stats['nodes'] += 1
                stats['anchor_factor_leaves'] += 1
                children[str(k)] = {'kind': 'anchor_factor'}
            else:
                nxt = [j for j in active if (2*p+2*j-rr) % ell]
                children[str(k)] = visit(rr, mm, nxt, depth+1)
        return {'kind': 'split', 'children': children}

    return visit(1, 2, T, 0), stats


def main():
    data = json.loads((BASE/'results.json').read_text())
    certs = []
    for row in data['cases']:
        # Separate small prime anchors so anchor==sieving_prime stays allowed.
        small_checks = []
        for a in ODD_SIEVE_PRIMES:
            if a <= row['p']:
                # All complement numbers exceed p >= 113 > 23 in this dataset.
                eliminated = {str(j): next((ell for ell in ODD_SIEVE_PRIMES
                                            if (2*row['p']+2*j-a) % ell == 0), None)
                              for j in row['T']}
                assert sum(ell is None for ell in eliminated.values()) < row['h']
                small_checks.append({'a': a, 'divisors': eliminated})
        tree, stats = exclusion_tree(row['p'], row['T'], row['h'], 24, True)
        raw_level = next(x for x in row['levels'] if x['z'] == 23)
        certs.append({k: row[k] for k in ('p','q','R','S','T','h','witness','witness_primes','protected_path')} |
                     {'z':23, 'small_anchor_checks':small_checks,
                      'large_anchor_tree':tree, 'tree_statistics':stats,
                      'raw_high': raw_level['raw_high'],
                      'raw_high_factors': {str(a):next(d for d in range(3,a,2) if a%d==0)
                                           for a in raw_level['raw_high']}})
    (BASE/'certificates.json').write_text(json.dumps(certs,indent=2)+'\n')
    print(json.dumps({'case_count':len(certs),
                      'total_tree_nodes':sum(c['tree_statistics']['nodes'] for c in certs),
                      'largest_tree_nodes':max(c['tree_statistics']['nodes'] for c in certs),
                      'raw_high_exceptions':[
                          {'p':c['p'],'R':c['R'],'high':c['raw_high'],
                           'factors':c['raw_high_factors']} for c in certs if c['raw_high']]},indent=2))


if __name__ == '__main__':
    main()
