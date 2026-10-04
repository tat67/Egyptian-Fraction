// complete_ind.cpp -- independent exact completion of core dumps for any h >= 2 (cross-check of
// complete_dump / compl.h; shares only the GMP binding gmpz.h).
//
// For a core C (elements <= Y) with delta = 1 - sum_C 1/n = a/b (recomputed exactly and compared with the
// dump) it finds every H = {x_1 < ... < x_h}, x_1 > Y, with sum_H 1/x = a/b, such that C u H is primitive.
//   h = 2 : ind2::solve (AP or divisor meet-in-the-middle, see ind2.h).
//   h >= 3: the smallest element satisfies b/a < x_1 <= h*b/a.  Every such x_1 (> Y, > previous element)
//           is tried unless
//             (i)   an element of C or of the already chosen part of H divides x_1,
//             (ii)  x_1 is a prime power (Lemma 1: T has no prime powers),
//             (iii) the primes U' of the new denominator b' (remainder a'/b' = a/b - 1/x_1) cannot be
//                   coloured with h-1 colours, where p, q in U' conflict if an element of C u H_chosen u {x_1}
//                   divides p^{e_p} q^{e_q} (Lemma 4 applied to the core C u H_chosen u {x_1}: each remaining
//                   element avoids being a multiple of those elements, and every p in U' needs a remaining
//                   element divisible by p^{e_p});
//           and the remaining h-1 elements are found recursively.
// Every candidate is checked for primitivity of C u H and the exact sum 1.
// Build: g++ -O2 -march=native -o complete_ind complete_ind.cpp /usr/lib/x86_64-linux-gnu/libgmp.so.10
// Usage: ./complete_ind DUMP Y [onlyH (0 = all)] [apLimit]
//        (a line with an empty core, "| h=H a/b", is a raw test of sum_H 1/x = a/b, x > Y)
#include <bits/stdc++.h>
#include "gmpz.h"
#include "ind2.h"
using namespace std; using namespace ind2;

static u64 Y, apLimit;
static u64 x1Tried = 0, x1Filtered = 0;
static Counters cnt;

struct Ctx {
  vector<u64> core;
  map<pair<u64,u64>, vector<pair<int,int>>> twoPrime;   // elements p^i q^j (p < q) of C and of chosen H
  vector<vector<Z>> found;
};

static void addTwoPrime(Ctx& c, u64 n, vector<tuple<u64,u64,int,int>>* undo) {
  auto f = factor64(n); if (f.size() != 2) return;
  c.twoPrime[{f[0].first, f[1].first}].push_back({f[0].second, f[1].second});
  if (undo) undo->push_back({f[0].first, f[1].first, f[0].second, f[1].second});
}
// min(chi, cap+1) of the conflict graph on the primes fd
static int chromatic(const Ctx& c, const vector<pair<u64,int>>& fd, int cap) {
  int n = fd.size(); if (n == 0) return 0;
  if (n > 64) return 1;   // never happens for the cores here; conservative: no pruning
  vector<u64> adj(n, 0); bool anyEdge = false;
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) {
    u64 p = fd[i].first, q = fd[j].first; int ep = fd[i].second, eq = fd[j].second;
    if (p > q) { swap(p, q); swap(ep, eq); }
    auto it = c.twoPrime.find({p, q}); bool cf = false;
    if (it != c.twoPrime.end()) for (auto& e : it->second) if (e.first <= ep && e.second <= eq) cf = true;
    if (cf) { adj[i] |= 1ULL << j; adj[j] |= 1ULL << i; anyEdge = true; }
  }
  if (!anyEdge) return 1;
  vector<int> order(n); iota(order.begin(), order.end(), 0);
  sort(order.begin(), order.end(), [&](int x, int y) { return __builtin_popcountll(adj[x]) > __builtin_popcountll(adj[y]); });
  for (int k = 2; k <= cap; k++) {
    vector<u64> cls(k, 0);
    function<bool(int,int)> go = [&](int i, int used) {
      if (i == n) return true; int v = order[i];
      for (int col = 0; col < k && col <= used; col++) if (!(adj[v] & cls[col])) { cls[col] |= 1ULL << v; if (go(i + 1, max(used, col + 1))) return true; cls[col] &= ~(1ULL << v); }
      return false; };
    if (go(0, 0)) return k;
  }
  return cap + 1;
}

// all completions of a/b by h elements > L, appended to c.found (prefixed by `chosen`)
static void rec(Ctx& c, int h, const Z& a, const Z& b, const vector<pair<u64,int>>& fb, const Z& L, vector<Z>& chosen) {
  if (h == 1) { if (divisible(b, a)) { Z x = divexact(b, a); if (cmp(x, L) > 0) { auto H = chosen; H.push_back(x); c.found.push_back(H); } } return; }
  if (h == 2) {
    vector<pair<Z,Z>> v; solve(a, b, fb, L, apLimit, v, cnt);
    for (auto& s : v) { auto H = chosen; H.push_back(s.first); H.push_back(s.second); c.found.push_back(H); }
    return;
  }
  Z lo = fdiv(b, a) + Z(1UL), hi = fdiv(b * (unsigned long)h, a);
  if (cmp(lo, L) <= 0) lo = L + Z(1UL);
  if (cmp(hi, lo) < 0) return;
  if (!hi.fitsU64()) { printf("RANGE-TOO-LARGE h=%d hi=%s\n", h, hi.str().c_str()); fflush(stdout); exit(5); }
  for (u64 x1 = lo.u64v(); x1 <= hi.u64v(); x1++) {
    x1Tried++;
    bool bad = false; for (u64 cc : c.core) if (x1 % cc == 0) { bad = true; break; }
    for (auto& z : chosen) if (!bad && z.fitsU64() && x1 % z.u64v() == 0) bad = true;
    if (bad || primeOfPower(x1)) { x1Filtered++; continue; }
    Z X1((unsigned long)x1), num = a * X1 - b, den = b * X1;
    if (num.sgn() <= 0) { x1Filtered++; continue; }
    Z g = gcd(num, den); num = divexact(num, g); den = divexact(den, g);
    map<u64,int> fe; for (auto& p : fb) fe[p.first] += p.second; auto f1 = factor64(x1); for (auto& p : f1) fe[p.first] += p.second;
    vector<pair<u64,int>> fd; Z r = den;
    for (auto& p : fe) { int e = 0; while (divisibleU(r, p.first)) { __gmpz_divexact_ui(r.v, r.v, p.first); e++; } if (e) fd.push_back({p.first, e}); }
    if (cmpu(r, 1) != 0) { printf("INTERNAL factor\n"); exit(6); }
    vector<tuple<u64,u64,int,int>> undo; addTwoPrime(c, x1, &undo);
    bool ok = chromatic(c, fd, h - 1) <= h - 1;
    if (!ok) x1Filtered++;
    else { chosen.push_back(X1); rec(c, h - 1, num, den, fd, X1, chosen); chosen.pop_back(); }
    for (auto& u : undo) { auto& v = c.twoPrime[{get<0>(u), get<1>(u)}]; v.pop_back(); if (v.empty()) c.twoPrime.erase({get<0>(u), get<1>(u)}); }
  }
}

int main(int argc, char** argv) {
  if (argc < 3) { fprintf(stderr, "usage: complete_ind DUMP Y [onlyH] [apLimit]\n"); return 1; }
  ifstream in(argv[1]); Y = strtoull(argv[2], 0, 10);
  int onlyH = argc > 3 ? atoi(argv[3]) : 0; apLimit = argc > 4 ? strtoull(argv[4], 0, 10) : 200000ULL;
  vector<unsigned> primes; { int N = 1000000; vector<char> s(N + 1, 1); for (int i = 2; i <= N; i++) if (s[i]) { primes.push_back(i); for (long long j = (long long)i * i; j <= N; j += i) s[j] = 0; } }
  u64 cores[16] = {0}, solutions = 0, rejected = 0; double worst = 0; string worstLine;
  string line; auto T0 = chrono::steady_clock::now();
  while (getline(in, line)) {
    size_t bar = line.find('|'); if (bar == string::npos) continue;
    istringstream rs(line.substr(bar + 1)); string hs, fr; rs >> hs >> fr; int h = atoi(hs.c_str() + 2);
    if (h < 2 || h > 15 || (onlyH && h != onlyH)) continue;
    Ctx c; { istringstream ls(line.substr(0, bar)); u64 x; while (ls >> x) c.core.push_back(x); }
    size_t sl = fr.find('/'); Z a = fromStr(fr.substr(0, sl)), b = fromStr(fr.substr(sl + 1));
    auto t0 = chrono::steady_clock::now(); cores[h]++;
    vector<Z> CZ; for (u64 x : c.core) CZ.push_back(Z((unsigned long)x));
    Z sn, sd; sumExact(CZ, sn, sd);
    bool raw = c.core.empty();
    if (!raw && (cmp(sd - sn, a) != 0 || cmp(sd, b) != 0)) { printf("MISMATCH remainder: %s\n", line.c_str()); return 2; }
    vector<pair<u64,int>> fb; if (!factorTD(b, primes, fb)) { printf("UNFACTORED %s\n", line.c_str()); return 3; }
    for (u64 x : c.core) addTwoPrime(c, x, nullptr);
    vector<Z> chosen; rec(c, h, a, b, fb, Z((unsigned long)Y), chosen);
    for (auto& H : c.found) {
      bool ok = true;
      for (auto& x : H) { if (cmpu(x, Y) <= 0) ok = false; for (u64 cc : c.core) if (ok && divisibleU(x, cc)) ok = false; }
      for (size_t i = 0; i < H.size() && ok; i++) for (size_t j = 0; j < H.size() && ok; j++) if (i != j && divisible(H[j], H[i])) ok = false;
      if (!ok) { rejected++; continue; }
      vector<Z> all = CZ; for (auto& x : H) all.push_back(x); Z n2, d2; sumExact(all, n2, d2);
      if (raw) { Z hn, hd; sumExact(H, hn, hd); if (cmp(hn, a) != 0 || cmp(hd, b) != 0) { printf("INTERNAL raw sum\n"); return 4; }
                 solutions++; printf("SOLUTION"); for (auto& x : H) printf(" %s", x.str().c_str()); printf("\n"); continue; }
      if (cmp(n2, d2) != 0) { printf("INTERNAL sum\n"); return 4; }
      solutions++; printf("SOLUTION |T|=%zu  %s", all.size(), line.substr(0, bar).c_str()); for (auto& x : H) printf(" %s", x.str().c_str()); printf("\n"); fflush(stdout);
    }
    double dt = chrono::duration<double>(chrono::steady_clock::now() - t0).count(); if (dt > worst) { worst = dt; worstLine = line.substr(bar); }
  }
  double secs = chrono::duration<double>(chrono::steady_clock::now() - T0).count();
  printf("complete_ind: cores"); for (int h = 2; h < 16; h++) if (cores[h]) printf(" h%d=%llu", h, (unsigned long long)cores[h]);
  printf("  x1Tried=%llu x1Filtered=%llu  twoTermAP=%llu twoTermDiv=%llu apSteps=%llu divEntries=%llu rejected=%llu solutions=%llu time=%.1fs worst=%.2fs (%s)\n",
         (unsigned long long)x1Tried, (unsigned long long)x1Filtered, (unsigned long long)cnt.ap, (unsigned long long)cnt.dv,
         (unsigned long long)cnt.apSteps, (unsigned long long)cnt.divEntries, (unsigned long long)rejected, (unsigned long long)solutions, secs, worst, worstLine.c_str());
}
