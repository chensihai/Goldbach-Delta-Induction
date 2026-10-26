"""Verify current Lean targets, axiom dependencies and the copied finite baseline."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(args):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f'{args}:\n{result.stdout}\n{result.stderr}')
    return result.stdout + result.stderr


def main():
    build = run(['lake', 'build'])
    axioms = run(['lake', 'env', 'lean', 'Checks.lean'])
    entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axioms)
    expected = re.findall(r'^#print axioms (\S+)', (ROOT/'Checks.lean').read_text(), re.M)
    assert [name for name, _ in entries] == expected
    assert entries
    allowed = {'propext','Classical.choice','Quot.sound'}
    for _, entry in entries:
        assert {x.strip() for x in entry.split(',') if x.strip()} <= allowed
    sources = list((ROOT/'GoldbachDeltaInduction').glob('*.lean')) + [ROOT/'GoldbachDeltaInduction.lean']
    for path in sources:
        text = path.read_text()
        assert not re.search(r'\b(sorry|admit|native_decide)\b', text), path
        assert not re.search(r'^\s*(axiom|opaque)\s', text, re.M), path
    finite_output = run([sys.executable,'research/GBR53/verify.py'])
    finite = json.loads(finite_output)
    assert finite['all_checks_passed'] and finite['cases'] == 16
    new_output = run([sys.executable,'research/GBR54/verify.py'])
    new_finite = json.loads(new_output)
    assert new_finite['all_checks_passed']
    historical_output = run([sys.executable,'research/GBR55/verify.py'])
    historical = json.loads(historical_output)
    assert historical['all_checks_passed']
    offset_output = run([sys.executable,'research/GBR56/verify.py'])
    offsets = json.loads(offset_output)
    assert offsets['all_checks_passed']
    files = sources + [ROOT/'Checks.lean',ROOT/'lakefile.toml',ROOT/'lean-toolchain',ROOT/'lake-manifest.json',ROOT/'verify_project.py']
    result = {'all_checks_passed':True,'lean_build':build.strip(),
              'checked_theorems':[name for name,_ in entries],
              'axiom_output':axioms.strip(),'finite_cases':finite['cases'],
              'finite_protected_states':finite['protected_states'],
              'finite_tree_nodes':finite['verified_tree_nodes'],
              'gbr54_search':new_finite['full_search_scope'],
              'gbr54_independent_intervals':new_finite['independently_recomputed_intervals'],
              'gbr54_counting_intervals':new_finite['checked_counting_intervals'],
              'gbr55_historical_rows':historical['historical_rows'],
              'gbr56_independent_targets':offsets['independently_recomputed_targets'],
              'gbr56_factor_certificates':offsets['factor_certificates'],
              'scope':'Listed Lean theorems and explicitly scoped GB-R53–56 checks; Goldbach remains open.',
              'sha256':{str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest()
                        for path in sorted(files)}}
    (ROOT/'verification.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('sha256','axiom_output')},indent=2))


if __name__ == '__main__':
    main()
