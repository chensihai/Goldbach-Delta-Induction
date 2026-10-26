"""Independent finite checks of the Astra note, with explicit limited scope."""
from itertools import product
from math import isqrt
from pathlib import Path
import hashlib
import json

BASE=Path(__file__).parent


def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def reps(n):
    return [(a,n-a) for a in range(2,n//2+1) if prime(a) and prime(n-a)]


def main():
    r38=reps(38)
    r40=reps(40)
    assert r38==[(7,31),(19,19)]
    assert r40==[(3,37),(11,29),(17,23)]
    lifts=lambda old,new:[(s,t) for s in old for t in new if s[0]<=t[0] and s[1]<=t[1]]
    assert lifts(r38,r40)==[]
    earlier=lifts(reps(36),r40)
    assert earlier==[((7,29),(11,29)),((13,23),(17,23)),((17,19),(17,23))]
    assert prime(19) and prime(23) and all(not prime(n) for n in range(20,23))
    odds=[n for n in range(3,38,2) if prime(n)]
    gap={a:a-max([r for r in odds if r<a],default=a) for a in odds}
    gap[3]=None
    checks=0
    strict_checks=0
    for a,b in product(odds,repeat=2):
        n=a+b
        for lower in range(6,n,2):
            width=n-lower
            criterion=any(gap[t] is not None and gap[t]<=width for t in (a,b))
            actual=any(lower<=r+s<n and r<=a and s<=b for r,s in product(odds,repeat=2))
            assert criterion==actual,(a,b,lower)
            strict=(gap[a] is not None and gap[b] is not None and gap[a]+gap[b]<=width)
            strict_actual=any(lower<=r+s<n and r<a and s<b for r,s in product(odds,repeat=2))
            assert strict==strict_actual,(a,b,lower)
            checks+=1
            strict_checks+=1
    result=dict(all_checks_passed=True,representations_38=r38,representations_40=r40,
                monotone_lifts_from_38=[],monotone_lifts_from_36=earlier,
                finite_predecessor_checks=checks,finite_strict_predecessor_checks=strict_checks,
                scope='Exact listed counterexample and finite criterion checks through endpoint 37; general criterion has a paper proof; no new prime-existence input.',
                sha256={name:hashlib.sha256((BASE/name).read_bytes()).hexdigest()
                        for name in ('AstraNotes.md','verify.py')})
    (BASE/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='sha256'},indent=2))


if __name__=='__main__':
    main()
