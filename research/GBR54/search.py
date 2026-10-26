"""Adversarial search for a real-prime greedy four-coverage counterexample.

Uses exact Eratosthenes primality and bit slices, and explores ALL tied maximum
single-anchor successors. Stops at the first failing reachable state.
"""
from bisect import bisect_right
from collections import deque
from math import isqrt
from pathlib import Path
import argparse
import json
import time


def sieve(n):
    flag=bytearray(b'\x01')*(n+1)
    flag[:2]=b'\x00\x00'
    for a in range(2,isqrt(n)+1):
        if flag[a]:
            flag[a*a:n+1:a]=b'\x00'*((n-a*a)//a+1)
    return flag


def labels(mask):
    return [j+1 for j in range(mask.bit_length()) if mask>>j&1]


def four_failure(R, patterns, g):
    n=R.bit_count()
    if n <= 2 or g >= 3:
        return False
    if n == 3:
        return g < 2
    pairs=[c for c in patterns if c.bit_count()==2]
    return not any(not a&b for i,a in enumerate(pairs) for b in pairs[i+1:])


def search(limit, state_cap):
    start=time.monotonic()
    flag=sieve(4*limit+200)
    primes=[a for a in range(3,len(flag),2) if flag[a]]
    packed=bytearray((len(flag)//2+8)//8)
    for n in primes:
        i=(n-1)//2
        packed[i//8] |= 1 << (i%8)
    bits=int.from_bytes(packed,'little')
    intervals=0
    total_states=0
    counts=[]
    for p,q in zip(primes,primes[1:]):
        if p>limit:
            break
        if p<5 or q-p<4:
            continue
        intervals+=1
        m=q-p-1
        J=(1<<m)-1
        covers={}
        for i in range(bisect_right(primes,p)):
            a=primes[i]
            mask=(bits >> (p+1-(a+1)//2)) & J
            covers.setdefault(mask,a)
        union=0
        for mask in covers:
            union |= mask
        if union != J:
            return dict(kind='uncovered_label',p=p,q=q,labels=labels(J&~union))
        parents={J:None}
        todo=deque([J])
        while todo:
            R=todo.popleft()
            total_states+=1
            if not R:
                continue
            patterns={mask&R:a for mask,a in covers.items()}
            g=max(c.bit_count() for c in patterns)
            if four_failure(R,patterns,g):
                path=[]
                cur=R
                while parents[cur] is not None:
                    prev,a=parents[cur]
                    path.append(a)
                    cur=prev
                path.reverse()
                H=max((a|b).bit_count() for a in patterns for b in patterns)
                assert H < min(4,R.bit_count())
                return dict(kind='greedy_four_failure',p=p,q=q,k=(q-p)//2,
                            R=labels(R),g=g,H=H,greedy_path=path,
                            checked_intervals=intervals,checked_states=total_states,
                            bound=limit,elapsed_seconds=time.monotonic()-start)
            for mask,a in patterns.items():
                if mask.bit_count()==g:
                    nxt=R&~mask
                    if nxt not in parents:
                        parents[nxt]=(R,a)
                        todo.append(nxt)
            if len(parents)>state_cap:
                return dict(kind='state_cap',p=p,q=q,states=len(parents),cap=state_cap)
        counts.append(dict(p=p,q=q,states=len(parents)))
        if intervals%500==0:
            print(json.dumps(dict(progress_p=p,intervals=intervals,states=total_states,
                                  seconds=round(time.monotonic()-start,2))),flush=True)
    return dict(kind='no_counterexample_in_finite_scope',bound=limit,
                checked_intervals=intervals,checked_states=total_states,
                elapsed_seconds=time.monotonic()-start,intervals=counts)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-p',type=int,default=100000)
    parser.add_argument('--state-cap',type=int,default=100000)
    parser.add_argument('--out',type=Path,default=Path(__file__).with_name('search_results.json'))
    args=parser.parse_args()
    result=search(args.max_p,args.state_cap)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='intervals'},indent=2),flush=True)


if __name__=='__main__':
    main()
