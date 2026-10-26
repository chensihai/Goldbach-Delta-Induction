"""Finite checks of the CRT construction, not a computation of Maynard primes."""
from itertools import combinations
import hashlib
import json
from math import factorial, gcd, isqrt
from pathlib import Path

BASE = Path(__file__).resolve().parent


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def next_prime(n):
    n += 1
    while not prime(n):
        n += 1
    return n


def crt_extend(a, modulus, residue, ell):
    assert gcd(modulus, ell) == 1
    step = (residue - a) * pow(modulus, -1, ell) % ell
    return a + modulus * step, modulus * ell


def example(k, radius):
    b = 6 * factorial(k)
    positions = list(range(0, k * b, b))
    diameter = positions[-1]
    buffer = range(-radius - 2, diameter + radius + 3)
    excluded = [t for t in buffer if t not in positions]
    blockers = {}
    last = b + diameter + 2 * radius + 10
    a, modulus = 1, b
    for t in excluded:
        ell = next_prime(last)
        last = ell
        blockers[t] = ell
        a, modulus = crt_extend(a, modulus, -t % ell, ell)
    assert 0 <= a < modulus and a % b == 1
    for t, ell in blockers.items():
        assert (a + t) % ell == 0
        assert all((a + h) % ell != 0 for h in positions)
    # Direct finite admissibility checks, with the proof for larger primes
    # supplied by the paper: primes > k forbid at most k parameter residues.
    checked_primes = [ell for ell in range(2, last + 2) if prime(ell)]
    for ell in checked_primes:
        assert any(all((modulus * n + a + h) % ell != 0 for h in positions)
                   for n in range(ell))
    true_factor_checks = 0
    for n in (1, 2, 3):
        translation = modulus * n + a
        for t, ell in blockers.items():
            value = translation + t
            assert value > ell > 1 and value % ell == 0
            true_factor_checks += 1
    support_checks = 0
    for h in positions:
        for delta in range(radius + 1):
            left, right = h + 1 - delta, h + 1 + delta
            assert left in buffer and right in buffer
            assert not (left in positions and right in positions)
            support_checks += 1
    # Any two selected positions differ by an even multiple of b and are
    # separated by at least six, so j=1 cannot be a central label.
    assert all(6 <= v - u <= diameter and (v - u) % 2 == 0
               for u, v in combinations(positions, 2))
    return dict(demonstration_k=k, radius=radius, b=b, diameter=diameter,
                blocked_shifts=len(excluded), modulus_bits=modulus.bit_length(),
                checked_local_primes=len(checked_primes),
                true_factor_checks=true_factor_checks,
                symmetric_support_checks=support_checks)


def main():
    examples = [example(k, radius) for k in (2, 3) for radius in (0, 1, 7, 16)]
    old_family = sorted({0, 4} | {1 + sign * (6 * j - 3)
                                for j in range(1, 4) for sign in (-1, 1)})
    assert old_family == [-14, -8, -2, 0, 4, 10, 16]
    assert sorted({h % 5 for h in old_family}) == list(range(5))
    result = dict(all_checks_passed=True, finite_crt_demonstrations=examples,
                  old_three_pair_family=old_family,
                  old_family_residues_mod_5=list(range(5)),
                  scope='Toy finite CRT, proper factors, local admissibility and symmetric-support checks only. Toy K is not certified to meet Maynard threshold; no computed infinite prime family or full analytic Lean proof.',
                  sha256={name: hashlib.sha256((BASE / name).read_bytes()).hexdigest()
                          for name in ('REPORT.md', 'verify.py')})
    (BASE / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'sha256'}, indent=2))


if __name__ == '__main__':
    main()
