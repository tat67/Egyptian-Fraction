"""verify_witnesses.py -- exact check of every witness file witnesses/witness_n<n>_max<K>.txt.

For each file it checks, with Python integers and fractions.Fraction only (no floating point,
no code shared with the C++ solvers), that the comma-separated entries are distinct positive
integers with maximum exactly K and that sum 1/x = n exactly, both as a Fraction and through the
integer identity sum_{x in S} L/x = n*L with L = lcm(S).
Usage: python3 verify_witnesses.py            (all files in witnesses/)
"""
import os, re, sys
from fractions import Fraction
from math import lcm

os.chdir(os.path.dirname(os.path.abspath(__file__)))
allok = True
pat = re.compile(r"witness_n(\d+)_max(\d+)\.txt$")
files = sorted((int(m.group(1)), int(m.group(2)), f) for f in os.listdir("witnesses") if (m := pat.match(f)))
for n, K, f in files:
    toks = open(os.path.join("witnesses", f)).read().strip().split(",")
    S = [int(t) for t in toks if t.strip().isdigit()]
    ok = len(S) == len(toks) and len(set(S)) == len(S) and min(S) >= 1 and max(S) == K
    s = sum(Fraction(1, x) for x in S)
    L = 1
    for x in S: L = lcm(L, x)
    ok = ok and s == n and sum(L // x for x in S) == n * L
    allok &= ok
    print(f"n={n:2d} K={K:6d} {f:28s} |S|={len(S):6d} max={max(S):6d} sum 1/x = {s}  -> {'VALID' if ok else 'INVALID'}")
print("RESULT: all witness files valid" if allok else "RESULT: some witness file is INVALID")
sys.exit(0 if allok else 1)
