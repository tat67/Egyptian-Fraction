"""verify_a9.py -- independent exact verification that a(9) = 8498 (OEIS A101877).

Uses only Python integers and fractions.Fraction (no floating point) and shares no code with
the C++ solvers.  It checks:

 1. witnesses/witness_n9_max8498.txt lists distinct positive integers with maximum 8498 whose
    reciprocals sum to exactly 9 (two ways: Fraction sum, and the integer identity
    sum_{x in S} L/x = 9 L with L = lcm(S)).
 2. certificates/cert_n9_K8496_v2.txt and certificates/cert_n9_K8496.txt: no set S of distinct
    integers in [1..8496] has sum 9   (verify_cert.py; recomputes everything from scratch).
 3. certificates/cert_n9_K8497w.txt: no such S with max(S) = 8497   (verify_cert.py --forced-in 8497).

 2 and 3 give a(9) >= 8498, and 1 gives a(9) <= 8498.
"""
import os, sys
os.chdir(os.path.dirname(os.path.abspath(__file__)))   # paths below are relative to a101877/
sys.path.insert(0, ".")
from fractions import Fraction
from math import lcm
import verify_cert

def check_witness(path, n, K):
    toks = open(path).read().strip().split(',')
    assert all(t.strip().isdigit() for t in toks), "non-integer token"
    S = [int(t) for t in toks]
    assert len(set(S)) == len(S), "duplicates"
    assert min(S) >= 1 and max(S) == K, "range / maximum"
    s = sum(Fraction(1, x) for x in S)
    L = 1
    for x in S: L = lcm(L, x)
    t = sum(L // x for x in S)
    ok = (s == n) and (t == n * L)
    print(f"witness {path}: |S|={len(S)} min={min(S)} max={max(S)} Fraction sum={s} "
          f"lcm has {len(str(L))} digits, sum L/x == {n}L: {t == n*L}  -> {'VALID' if ok else 'INVALID'}")
    return ok

def header(path):
    with open(path) as fh:
        lines = [l for l in fh if not l.startswith("#")]
    return tuple(map(int, lines[0].split()))

if __name__ == "__main__":
    assert header("certificates/cert_n9_K8496_v2.txt")[:2] == (9, 8496)
    assert header("certificates/cert_n9_K8496.txt")[:2] == (9, 8496)
    assert header("certificates/cert_n9_K8497w.txt")[:2] == (9, 8497)
    ok = check_witness("witnesses/witness_n9_max8498.txt", 9, 8498)
    ok &= verify_cert.main("certificates/cert_n9_K8496_v2.txt")
    ok &= verify_cert.main("certificates/cert_n9_K8496.txt")
    ok &= verify_cert.main("certificates/cert_n9_K8497w.txt", 8497)
    print("RESULT: a(9) = 8498 verified" if ok else "RESULT: verification FAILED")
    sys.exit(0 if ok else 1)
