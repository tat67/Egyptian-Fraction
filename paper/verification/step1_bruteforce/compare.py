"""Compare DFS dumps D(K) against brute force: require SEG ⊆ D ⊆ FIN and no duplicate cores in D."""
import sys
def primes_upto(n): return [p for p in range(2, n + 1) if all(p % d for d in range(2, int(p ** .5) + 1))]
def main(sb, K, dumpfile):
    pr = primes_upto(sb); idx = {}
    e = 0
    for a in range(len(pr)):
        for b in range(a + 1, len(pr)):
            idx[pr[a] * pr[b]] = e; e += 1
    D = []
    for line in open(dumpfile):
        parts = line.split()
        if not parts or parts[0] != 'E': continue
        j = parts.index('C'); mask = 0
        for n in parts[j + 1:]: mask |= 1 << idx[int(n)]
        D.append(mask)
    Dset = set(D)
    seg = set(int(x) for x in open('bf_seg_%d_%d.txt' % (sb, K)))
    fin = set(int(x) for x in open('bf_fin_%d_%d.txt' % (sb, K)))
    print("SB %d K %d: |D|=%d distinct=%d |SEG|=%d |FIN|=%d  SEG<=D: %s  D<=FIN: %s  |FIN\\SEG|=%d |D\\SEG|=%d"
          % (sb, K, len(D), len(Dset), len(seg), len(fin), seg <= Dset, Dset <= fin, len(fin - seg), len(Dset - seg)))
    ok = len(D) == len(Dset) and seg <= Dset and Dset <= fin
    print("RESULT", "PASS" if ok else "FAIL")
main(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3])
