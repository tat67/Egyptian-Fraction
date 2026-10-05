"""verify_bounds.py -- independent exact verification of the bounds for n = 9, 10, 11 obtained with
a101877_v2 on this branch (OEIS A101877).

Uses only Python integers, fractions.Fraction and verify_cert.py (integer numpy); no floating point
and no code shared with the C++ solvers.  It checks:

  n = 9 :  certificates/cert_n9_K8497.txt    no S in [1..8497]  has sum 9   -> a(9)  >= 8498
           witnesses/witness_n9_max8498.txt  exact witness, max 8498        -> a(9)  <= 8498
  n = 10:  certificates/cert_n10_K22791.txt  no S in [1..22791] has sum 10  -> a(10) >= 22792
           witnesses/witness_n10_max22820.txt exact witness, max 22820      -> a(10) <= 22820
  n = 11:  certificates/cert_n11_K60589.txt  no S in [1..60589] has sum 11  -> a(11) >= 60590

(verify_a9.py checks a(9) = 8498 with the two certificates of the original report instead.)
Run time: about 30 seconds.
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
    print(f"witness {path}: |S|={len(S)} max={max(S)} Fraction sum={s}  lcm has {len(str(L))} digits, "
          f"sum L/x == {n}L: {t == n*L}  -> {'VALID' if ok else 'INVALID'}")
    return ok

def header(path):
    with open(path) as fh:
        lines = [l for l in fh if not l.startswith("#")]
    return tuple(map(int, lines[0].split()))

if __name__ == "__main__":
    claims = [
        ("n = 9:  a(9) = 8498",            [("cert", "certificates/cert_n9_K8497.txt", 9, 8497),
                                            ("wit", "witnesses/witness_n9_max8498.txt", 9, 8498)]),
        ("n = 10: 22792 <= a(10) <= 22820", [("cert", "certificates/cert_n10_K22791.txt", 10, 22791),
                                            ("wit", "witnesses/witness_n10_max22820.txt", 10, 22820)]),
        ("n = 11: a(11) >= 60590",          [("cert", "certificates/cert_n11_K60589.txt", 11, 60589)]),
    ]
    allok = True
    for claim, parts in claims:
        ok = True
        for kind, path, n, K in parts:
            if kind == "cert":
                assert header(path)[:2] == (n, K), f"{path}: header is not ({n}, {K})"
                ok &= bool(verify_cert.main(path))          # prove form: no S in [1..K] has sum n
            else:
                ok &= check_witness(path, n, K)
        print(f"  {claim}: {'verified' if ok else 'FAILED'}")
        allok &= ok
    print("RESULT: all bounds verified" if allok else "RESULT: verification FAILED")
    sys.exit(0 if allok else 1)
