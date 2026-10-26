"""Correctly scan noncentral centers in adjacent-prime gaps, with exact minima."""
from collections import Counter
from math import isqrt
from pathlib import Path
import argparse
import json


def sieve(n):
    flag=bytearray(b'\x01')*(n+1)
    flag[:2]=b'\x00\x00'
    for r in range(2,isqrt(n)+1):
        if flag[r]:
            flag[r*r:n+1:r]=b'\x00'*((n-r*r)//r+1)
    return flag


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--max-p',type=int,default=100000)
    args=ap.parse_args()
    flag=sieve(4*args.max_p+100)
    primes=[p for p in range(3,len(flag),2) if flag[p]]
    constants=(2,4,8,16,32,64,128,256,512)
    first={}
    target_count=0
    max_by_k={}
    max_delta=None
    max_ratio=None
    sharp=0
    histogram=Counter()
    intervals=0
    for p,q in zip(primes,primes[1:]):
        if p>args.max_p:
            break
        k=(q-p)//2
        intervals+=1
        for j in range(1,2*k):
            if j==k:
                continue
            c=p+j
            lower=max(j,2*k-j)
            d=next((d for d in range(lower,c-2,2) if flag[c-d] and flag[c+d]),None)
            if d is None:
                result=dict(kind='noncentral_goldbach_failure',p=p,q=q,k=k,j=j,c=c)
                raise RuntimeError(json.dumps(result))
            assert d>k and d%2==j%2
            rec=dict(p=p,q=q,k=k,j=j,c=c,lower=lower,delta=d,pair=[c-d,c+d])
            target_count+=1
            histogram[k]+=1
            sharp+=d==lower
            if max_delta is None or d>max_delta['delta']:
                max_delta=rec
            if max_ratio is None or d*max_ratio['k']>max_ratio['delta']*k:
                max_ratio=rec
            if k not in max_by_k or d>max_by_k[k]['delta']:
                max_by_k[k]=rec
            for C in constants:
                if str(C) not in first and d>C*k:
                    first[str(C)]=rec
    out=Path(__file__).parent
    result=dict(scope=dict(max_p=args.max_p,adjacent_intervals=intervals,
                           noncentral_targets=target_count),
                all_targets_represented=True,sharp_at_gap_lower_bound=sharp,
                max_delta=max_delta,max_delta_over_k=max_ratio,
                first_counterexamples_to_delta_le_Ck=first,
                targets_by_k=dict(histogram),max_delta_by_k=max_by_k)
    (out/'noncentral_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('targets_by_k','max_delta_by_k')},indent=2))


if __name__=='__main__':
    main()
