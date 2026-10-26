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
    transport_output = run([sys.executable,'research/GBR57/verify.py'])
    transport = json.loads(transport_output)
    assert transport['all_checks_passed']
    source_output = run([sys.executable,'research/GBR58/audit.py'])
    source_audit = json.loads(source_output)
    assert source_audit['all_checks_passed']
    literature_output = run([sys.executable,'research/GBR59/verify.py'])
    literature = json.loads(literature_output)
    assert literature['all_checks_passed']
    cluster_output = run([sys.executable,'research/GBR60/verify.py'])
    cluster = json.loads(cluster_output)
    assert cluster['all_checks_passed']
    bridge_output = run([sys.executable,'research/GBR67/bridge_search.py'])
    bridge_summary = json.loads(bridge_output)
    assert bridge_summary['all_finite_checks_passed']
    assert bridge_summary['targets'] == bridge_summary['independently_checked_certificates'] == 114
    assert bridge_summary['symmetric_failures'] == [174, 336]
    assert bridge_summary['asymmetric_failures'] == []
    transfer_output = run([sys.executable,'research/GBR68/source_transfer.py'])
    transfer_summary = json.loads(transfer_output)
    assert transfer_summary['all_finite_checks_passed']
    assert transfer_summary['targets'] == 114
    assert transfer_summary['universally_safe_source_certificates'] == 113
    assert transfer_summary['no_source_in_declared_pool'] == [148]
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
              'gbr57_finite_predecessor_checks':transport['finite_predecessor_checks'],
              'gbr58_historical_c_runs':len(source_audit['historical_segmented_sieve_runs']),
              'gbr59_group_degrees':[g['degree'] for g in literature['alternating_group_graphs']],
              'gbr60_crt_demonstrations':len(cluster['finite_crt_demonstrations']),
              'gbr60_infinite_result':'Paper proof using published Maynard theorem; not part of Lean proof coverage.',
              'gbr62_infinite_result':'Paper proof using published Maynard and Montgomery–Vaughan theorems; only finite exception counting is in Lean proof coverage.',
              'gbr63_infinite_result':'Conditional paper extraction from PrimeGaps186 commit 61340d0b74163003b32756bb16e91d9209a5e330, retaining its three inputs; external project not independently compiled here. Only finite weighted detection is in local Lean coverage.',
              'gbr64_infinite_result':'Conditional paper extension using uniform presieve residue estimates from the same PrimeGaps186 source and its three inputs; local Lean checks only the isolation-to-offset interface, not the full infinite construction.',
              'gbr65_infinite_result':'Unconditional paper deduction from published Maynard 2015 and Montgomery–Vaughan results, with some fixed even k between 2 and 600. Local Lean verifies the finite 105-tuple shape and admissibility, not the full analytic infinitude proof.',
              'gbr66_scope':'Finite parameter extraction and exact-minimum logical interface are in Lean; the conditional universal induction compatibility bridge is open and is not an axiom.',
              'gbr67_bridge_checks':bridge_summary,
              'gbr67_scope':'Finite restricted rectangle certificates for noncentral centers<=250; compatible prime endpoints are tested directly, not deduced from induction. Higher-valued lower-k sources are a paper interface observation only.',
              'gbr68_transfer_checks':transfer_summary,
              'gbr68_scope':'Lean verifies a generic universal-witness transfer interface, B2 implies the single window 23..29, and transfer 92 to 96 fails; finite source pools do not prove the general induction step.',
              'scope':'Listed Lean theorems and explicitly scoped GB-R53–60, GB-R67 and GB-R68 finite checks; no general Goldbach induction step or full analytic infinitude proof in Lean. Universal Goldbach and infinitude for individually preassigned gaps remain open.',
              'sha256':{str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest()
                        for path in sorted(files)}}
    (ROOT/'verification.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('sha256','axiom_output')},indent=2))


if __name__ == '__main__':
    main()
