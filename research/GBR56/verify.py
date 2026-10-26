"""Independent full recomputation using trial division and descending prime anchors.

This deliberately does not import the scanner or use its gap-offset lower bound.
"""
from bisect import bisect_right
from collections import Counter
from functools import lru_cache
from math import isqrt
from pathlib import Path
import hashlib
import json

BASE=Path(__file__).parent


@lru_cache(None)
def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def main():
    expected=json.loads((BASE/'noncentral_results.json').read_text())
    limit=expected['scope']['max_p']
    primes=[n for n in range(2,2*limit+200) if prime(n)]
    first={}
    histogram=Counter()
    max_by_k={}
    max_delta=None
    max_ratio=None
    sharp=0
    intervals=0
    targets=0
    for p,q in zip(primes,primes[1:]):
        if p>limit:
            break
        if p==2:
            continue
        k=(q-p)//2
        intervals+=1
        for j in range(1,q-p):
            if j==k:
                continue
            c=p+j
            i=bisect_right(primes,c)-1
            # Search from the midpoint through all smaller prime anchors.
            while i>=0 and not prime(2*c-primes[i]):
                i-=1
            assert i>=0,(p,q,j,'no representation')
            d=c-primes[i]
            lower=max(j,2*k-j)
            assert d>=lower and d>k
            rec=dict(p=p,q=q,k=k,j=j,c=c,lower=lower,delta=d,pair=[c-d,c+d])
            histogram[k]+=1
            targets+=1
            sharp+=d==lower
            if max_delta is None or d>max_delta['delta']:
                max_delta=rec
            if max_ratio is None or d*max_ratio['k']>max_ratio['delta']*k:
                max_ratio=rec
            if k not in max_by_k or d>max_by_k[k]['delta']:
                max_by_k[k]=rec
            for C in (2,4,8,16,32,64,128,256,512):
                if str(C) not in first and d>C*k:
                    first[str(C)]=rec
    assert expected['scope']==dict(max_p=limit,adjacent_intervals=intervals,noncentral_targets=targets)
    assert expected['sharp_at_gap_lower_bound']==sharp
    assert expected['max_delta']==max_delta
    assert expected['max_delta_over_k']==max_ratio
    assert expected['first_counterexamples_to_delta_le_Ck']==first
    assert expected['targets_by_k']=={str(k):v for k,v in histogram.items()}
    assert expected['max_delta_by_k']=={str(k):v for k,v in max_by_k.items()}
    certificates=json.loads((BASE/'factor_certificates.json').read_text())
    excluded=0
    for cert in certificates:
        ref=first[str(cert['C'])]
        assert all(cert[key]==value for key,value in ref.items())
        c,d=cert['c'],cert['delta']
        assert len(cert['factors'])==d
        for e,f in enumerate(cert['factors']):
            assert 1<f and ((f<c-e and (c-e)%f==0) or (f<c+e and (c+e)%f==0))
            excluded+=1
    result=dict(all_checks_passed=True,independently_recomputed_targets=targets,
                independently_recomputed_intervals=intervals,
                factor_certificates=len(certificates),excluded_offsets=excluded,
                scope='Full independent recomputation of the stated finite scope; no universal Goldbach or unbounded-ratio conclusion.',
                sha256={name:hashlib.sha256((BASE/name).read_bytes()).hexdigest()
                        for name in ('noncentral_scan.py','noncentral_results.json','verify.py',
                                     'generate_lean.py','factor_certificates.json')})
    (BASE/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
