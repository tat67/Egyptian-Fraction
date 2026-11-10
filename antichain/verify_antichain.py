#!/usr/bin/env python3
"""Exact check of antichain Egyptian-fraction representations of 1.

Each non-empty line of the input file is a set T of positive integers.
For every line the script checks, with exact rational arithmetic only:
  (1) the elements are distinct integers >= 2,
  (2) sum_{n in T} 1/n == 1,
  (3) no element divides another one.
Usage: python3 verify_antichain.py solutions43.txt
"""
import sys
from fractions import Fraction

def check(T):
    if len(set(T)) != len(T) or min(T) < 2:
        return False, "not distinct integers >= 2"
    s = sum(Fraction(1, n) for n in T)
    if s != 1:
        return False, "sum = %s" % s
    S = sorted(T)
    for i, a in enumerate(S):
        for b in S[i + 1:]:
            if b % a == 0:
                return False, "%d divides %d" % (a, b)
    return True, "ok"

def main():
    ok_all = True
    with open(sys.argv[1]) as f:
        for ln, line in enumerate(f, 1):
            T = [int(x) for x in line.split()]
            if not T:
                continue
            ok, msg = check(T)
            ok_all &= ok
            print("line %d: |T| = %d, max = %d, sum == 1 and antichain: %s (%s)"
                  % (ln, len(T), max(T), ok, msg))
    print("ALL OK" if ok_all else "FAILURE")
    return 0 if ok_all else 1

if __name__ == "__main__":
    sys.exit(main())
