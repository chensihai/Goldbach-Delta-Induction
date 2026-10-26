"""Independent trial-division/set-based checks of selected search intervals.

The full 100000 search is not rerun here. Verification scope is explicit.
"""
from collections import deque
from functools import lru_cache
from math import isqrt
from pathlib import Path
import hashlib
import json

BASE=Path(__file__).parent


@lru_cache(None)
def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def independent_interval(p,q):
    assert prime(p) and prime(q)
    assert all(not prime(a) for a in range(p+1,q))
    J=frozenset(range(1,q-p))
    covers={frozenset(j for j in J if prime(2*p+2*j-a))
            for a in range(3,p+1,2) if prime(a)}
    assert frozenset().union(*covers)==J
    seen={J}
    todo=deque([J])
    while todo:
        S=todo.popleft()
        if not S:
            continue
        pieces={c&S for c in covers}
        size=max(map(len,pieces))
        goal=min(4,len(S))
        best=next(c for c in pieces if len(c)==size)
        assert len(best)>=goal or any(len(best|d)>=goal for d in pieces) or any(
            len(c|d)>=goal for c in pieces for d in pieces)
        for c in pieces:
            if len(c)==size:
                nxt=S-c
                if nxt not in seen:
                    seen.add(nxt)
                    todo.append(nxt)
    return len(seen)


def main():
    calibration=json.loads((BASE/'calibration.json').read_text())
    search=json.loads((BASE/'search_results.json').read_text())
    assert calibration['checked_intervals']==241 and calibration['checked_states']==1953
    assert search['kind']=='no_counterexample_in_finite_scope'
    rows=search['intervals']
    assert len(rows)==search['checked_intervals']
    assert sum(r['states'] for r in rows)==search['checked_states']
    chosen={r['p']:r for r in rows if r['p']<=2000}
    for i in range(13):
        r=rows[i*(len(rows)-1)//12]
        chosen[r['p']]=r
    for r in (max(rows,key=lambda r:r['states']),max(rows,key=lambda r:r['q']-r['p'])):
        chosen[r['p']]=r
    independent=[]
    for p,r in sorted(chosen.items()):
        n=independent_interval(p,r['q'])
        assert n==r['states'],(p,n,r['states'])
        independent.append(dict(p=p,q=r['q'],states=n))
    bounds=json.loads((BASE/'interval_bounds.json').read_text())
    assert bounds['all_checks_passed']
    result=dict(all_checks_passed=True,
                full_search_scope=dict(max_p=search['bound'],intervals=search['checked_intervals'],
                                       reachable_states=search['checked_states']),
                independently_recomputed_intervals=len(independent),
                independently_recomputed_states=sum(r['states'] for r in independent),
                checked_forbidden_systems=bounds['forbidden_systems'],
                checked_counting_intervals=bounds['checked_intervals'],
                independent_samples=independent,
                scope='All ties in full search; independent recomputation only for listed intervals; no asymptotic conclusion',
                sha256={name:hashlib.sha256((BASE/name).read_bytes()).hexdigest() for name in
                        ('search.py','search_results.json','calibration.json',
                         'interval_counting.py','interval_bounds.json','verify.py')})
    (BASE/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('independent_samples','sha256')},indent=2))


if __name__=='__main__':
    main()
