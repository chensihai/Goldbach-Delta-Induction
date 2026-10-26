"""Check stored audit consistency and exact reference identity, not rerun its sieve."""
from pathlib import Path
import hashlib
import json

BASE=Path(__file__).parent


def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1<<20),b''):
            h.update(block)
    return h.hexdigest()


def main():
    data=json.loads((BASE/'historical_scan_audit.json').read_text())
    assert data['all_checks_passed'] and data['rows']==1906977
    assert sum(sum(hist.values()) for hist in data['delta_histograms'].values())==data['rows']
    assert sum(data['adjacent_rows'].values())==1639025
    assert sum(data['nonadjacent_rows'].values())==267952
    assert data['rows_with_delta_below_k']==9268
    for original,info in data['references'].items():
        path=Path(original)
        assert path.stat().st_size==info['bytes'] and digest(path)==info['sha256']
        if path.suffix!='.csv':
            copy=BASE/'reference'/(path.parent.name+'_'+path.name)
            assert digest(copy)==info['sha256']
    own_files=[BASE/'audit_historical_scan.py',BASE/'verify.py',BASE/'historical_scan_audit.json',
               *sorted((BASE/'reference').glob('*'))]
    result=dict(all_checks_passed=True,historical_rows=data['rows'],
                adjacent_rows=sum(data['adjacent_rows'].values()),
                scope='Consistency and source hashes; does not rerun the full prime sieve',
                sha256={str(p.relative_to(BASE)):digest(p) for p in own_files})
    (BASE/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='sha256'},indent=2))


if __name__=='__main__':
    main()
