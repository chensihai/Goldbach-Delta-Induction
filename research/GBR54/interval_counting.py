"""Exact-rational checks for the elementary multi-residue interval bound.

The general argument is in REPORT.md. Finite checks do not replace that proof.
"""
from fractions import Fraction
from itertools import product
from math import prod, isqrt
from pathlib import Path
import json

BASE=Path(__file__).parent


def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def threshold(P, counts):
    density=prod((Fraction(ell-v,ell) for ell,v in zip(P,counts)),start=Fraction(1))
    error=prod(1+v for v in counts)-1
    least_length=(error*density.denominator)//density.numerator+1
    return dict(density=str(density),error=error,length=least_length)


def main():
    rows=[]
    for z in (7,13,23,47,97):
        P=[ell for ell in range(2,z+1) if prime(ell)]
        M=prod(P)
        for h in (1,2,4,8):
            counts=[min(h+1,ell-1) for ell in P]
            row=threshold(P,counts)
            rows.append(dict(z=z,h=h,period=M,**row,
                             stronger_than_period=row['length']<M))
    # Independently enumerate all proper forbidden sets modulo 2,3,5.
    # This includes empty forbidden sets, sparse and nearly full residue sets.
    P=(2,3,5)
    families=[[{r for r in range(ell) if mask>>r&1}
               for mask in range((1<<ell)-1)] for ell in P]
    checked=0
    for forb in product(*families):
        density=prod((Fraction(ell-len(F),ell) for ell,F in zip(P,forb)),start=Fraction(1))
        error=prod(1+len(F) for F in forb)-1
        period=prod(P)
        actual_period=sum(all(a%ell not in F for ell,F in zip(P,forb)) for a in range(period))
        assert actual_period == period*density
        for start in (0,1,7,29,30):
            for length in (0,1,2,7,29,30,31,61):
                count=sum(all(a%ell not in F for ell,F in zip(P,forb))
                          for a in range(start,start+length))
                assert abs(count-length*density) <= error
                if length*density>error:
                    assert count>0
                checked+=1
    output=dict(all_checks_passed=True,checked_intervals=checked,
                forbidden_systems=prod(len(f) for f in families),thresholds=rows,
                scope='Exact-rational finite checks; general counting proof is in REPORT.md')
    (BASE/'interval_bounds.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k!='thresholds'},indent=2))
    for row in rows:
        print(f"z={row['z']:2d} h={row['h']} length={row['length']} period={row['period']} improved={row['stronger_than_period']}")


if __name__=='__main__':
    main()
