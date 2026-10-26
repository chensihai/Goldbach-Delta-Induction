"""Read-only audit of the old central-offset scan, including full primality checks.

Uses a fresh Eratosthenes table through the historical 10^8 bound. The large
reference CSV is read in place and hashed, not copied or modified.
"""
from collections import Counter,defaultdict
from math import isqrt
from pathlib import Path
import csv
import hashlib
import json
import time

BASE=Path(__file__).parent
REFERENCE=BASE.parents[2]/'delta_scan_for_p_k'
DELTA_REFERENCE=BASE.parents[2]/'Delta'


def sha256(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1<<20),b''):
            h.update(block)
    return h.hexdigest()


def main():
    started=time.monotonic()
    cap=100000020
    flag=bytearray(b'\x01')*(cap+1)
    flag[:2]=b'\x00\x00'
    for a in range(2,isqrt(cap)+1):
        if flag[a]:
            flag[a*a:cap+1:a]=b'\x00'*((cap-a*a)//a+1)
    print(json.dumps({'phase':'fresh_prime_sieve_ready','bound':cap,
                      'seconds':round(time.monotonic()-started,2)}),flush=True)
    stats=defaultdict(Counter)
    adjacency=Counter()
    nonadjacency=Counter()
    bounds={}
    short=0
    zero_cases=[]
    samples={}
    rows=0
    with (REFERENCE/'out.csv').open(newline='') as f:
        for x in csv.DictReader(f):
            k,p,c,d=(int(x[key]) for key in ('k','p','c','delta_min'))
            assert k in (2,3,5) and 3<=p<=100000000
            q=p+2*k
            assert c==p+k and 1<=d<=k
            assert all(int(x[key])==c%mod for key,mod in
                       (('c_mod3',3),('c_mod5',5),('c_mod7',7),('c_modQ',1155)))
            assert flag[p] and flag[q]
            assert flag[c-d] and flag[c+d]
            # The field is a positive-offset minimum, not a minimum over delta>=0.
            assert all(not(flag[c-e] and flag[c+e]) for e in range(1,d))
            isadj=not any(flag[n] for n in range(p+1,q))
            (adjacency if isadj else nonadjacency)[k]+=1
            if isadj:
                assert d==k
            if d<k:
                short+=1
                assert p<c-d<c+d<q and not isadj
            if flag[c]:
                zero_cases.append(dict(k=k,p=p,c=c,reported_positive_delta=d))
            stats[k][d]+=1
            bounds[k]=(min(p,bounds.get(k,(p,p))[0]),max(p,bounds.get(k,(p,p))[1]))
            samples.setdefault((k,d,isadj),dict(k=k,p=p,q=q,c=c,delta=d,
                                                adjacent=isadj,pair=[c-d,c+d]))
            rows+=1
    refs=[REFERENCE/'scan_center_pk.cpp',REFERENCE/'out.csv',
          DELTA_REFERENCE/'Delta.lean',DELTA_REFERENCE/'Basic.lean']
    reference_dir=BASE/'reference'
    reference_dir.mkdir(exist_ok=True)
    for path in (refs[0],refs[2],refs[3]):
        dest=reference_dir/(path.parent.name+'_'+path.name)
        dest.write_bytes(path.read_bytes())
    result=dict(all_checks_passed=True,rows=rows,
                delta_histograms={str(k):dict(counts) for k,counts in sorted(stats.items())},
                adjacent_rows={str(k):adjacency[k] for k in sorted(stats)},
                nonadjacent_rows={str(k):nonadjacency[k] for k in sorted(stats)},
                rows_with_delta_below_k=short,
                zero_offset_cases=zero_cases,
                p_bounds={str(k):v for k,v in sorted(bounds.items())},
                samples=list(samples.values()),
                fresh_sieve_bound=cap,elapsed_seconds=time.monotonic()-started,
                scope='All stored rows independently checked for endpoint and output-pair primality, positive minimum and adjacency; no noncentral existence theorem.',
                references={str(path):dict(bytes=path.stat().st_size,sha256=sha256(path)) for path in refs})
    (BASE/'historical_scan_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('references','samples')},indent=2))


if __name__=='__main__':
    main()
