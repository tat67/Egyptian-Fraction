// q2k.cpp -- FIRST DESIGN, kept as an independent cross-check of the core enumeration (prime-by-prime).
// No bound on the elements.  Lagrangian threshold A, Y = the bound above which at most hmax
// elements of T can lie.  Core C = T cap [2, Y] (prime-by-prime search, exact residues),
// huge part H = T cap (Y, oo), |H| = h <= hmax, found by exact Egyptian-fraction completion.
#include <bits/stdc++.h>
#include "gmpz.h"
using namespace std;
typedef unsigned long long u64; typedef long long i64; typedef __int128 i128; typedef unsigned __int128 u128;

static int K = 40; static u64 A = 134; static u64 Y = 0; static int hmaxArg = -1;
static const u128 S = (u128)1 << 96;
static vector<int> spf; static vector<char> isPP;

static u64 inv_mod(u64 a, u64 m) { i128 t = 0, nt = 1, r = m, nr = a % m;
  while (nr) { i128 q = r / nr, tmp = t - q * nt; t = nt; nt = tmp; tmp = r - q * nr; r = nr; nr = tmp; }
  if (t < 0) t += m; return (u64)t; }
static vector<pair<u64,int>> factorSmall(u64 n) { vector<pair<u64,int>> f; while (n > 1) { u64 p = spf[n]; int k = 0; while (n % p == 0) { n /= p; k++; } f.push_back({p, k}); } return f; }

struct Dinic {
  struct E { int to; u64 cap; int rev; };
  vector<vector<E>> G; vector<int> lvl, it;
  explicit Dinic(int n) : G(n) {}
  void addEdge(int a, int b, u64 c) { G[a].push_back({b, c, (int)G[b].size()}); G[b].push_back({a, 0, (int)G[a].size() - 1}); }
  bool bfs(int s, int t) { lvl.assign(G.size(), -1); queue<int> q; q.push(s); lvl[s] = 0;
    while (!q.empty()) { int v = q.front(); q.pop(); for (auto& e : G[v]) if (e.cap && lvl[e.to] < 0) { lvl[e.to] = lvl[v] + 1; q.push(e.to); } } return lvl[t] >= 0; }
  u64 dfs(int v, int t, u64 f) { if (v == t) return f;
    for (int& i = it[v]; i < (int)G[v].size(); i++) { E& e = G[v][i];
      if (e.cap && lvl[e.to] == lvl[v] + 1) { u64 d = dfs(e.to, t, min(f, e.cap)); if (d) { e.cap -= d; G[e.to][e.rev].cap += d; return d; } } }
    return 0; }
  u64 run(int s, int t) { u64 F = 0; while (bfs(s, t)) { it.assign(G.size(), 0); while (u64 f = dfs(s, t, ~0ULL)) F += f; } return F; }
};

struct Elem { u64 n; u64 P; vector<pair<int,u64>> res; vector<pair<u64,int>> fac; u128 rLow, rUp; i128 wUp, costLow; };
static vector<Elem> el; static vector<vector<int>> conf;
static vector<u64> primes; static unordered_map<u64,int> pidx; static vector<u64> Mq; static vector<int> Eq;
static vector<vector<int>> chains; static vector<u128> cy; static vector<vector<int>> chainsOf;
static u128 Wup = 0, lamLow, lamUp; static i128 cexpLow; static int HMAX;
struct Group { u64 p; vector<int> elems; }; static vector<Group> groups;

static void buildChains() {
  int m = 0; while (m < (int)el.size() && el[m].n < A) m++;
  const int SH = 40; vector<u64> wk(m); for (int i = 0; i < m; i++) wk[i] = (u64)(el[i].wUp >> SH) + 1;
  Dinic g(2 * m + 2); int s = 2 * m, t = 2 * m + 1;
  for (int i = 0; i < m; i++) { g.addEdge(s, i, wk[i]); g.addEdge(m + i, t, wk[i]); }
  for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) if (el[j].n % el[i].n == 0) g.addEdge(i, m + j, ~0ULL >> 2);
  g.run(s, t);
  vector<vector<pair<int,u64>>> out(m);
  for (int i = 0; i < m; i++) for (auto& e : g.G[i]) if (e.to >= m && e.to < 2 * m) { u64 f = g.G[e.to][e.rev].cap; if (f) out[i].push_back({e.to - m, f}); }
  vector<vector<pair<int,u64>>> arriving(m); vector<vector<int>> pref; vector<u64> amount;
  for (int j = 0; j < m; j++) {
    vector<pair<int,u64>> streams = arriving[j]; u64 have = 0; for (auto& x : streams) have += x.second;
    if (have < wk[j]) { pref.push_back({}); streams.push_back({(int)pref.size() - 1, wk[j] - have}); }
    vector<pair<int,u64>> dest; u64 outsum = 0; for (auto& o : out[j]) { dest.push_back(o); outsum += o.second; }
    if (wk[j] > outsum) dest.push_back({-1, wk[j] - outsum});
    size_t si = 0, di = 0; u64 sr = streams[0].second, dr = dest[0].second;
    while (si < streams.size() && di < dest.size()) {
      u64 dd = min(sr, dr);
      if (dd) { vector<int> p = pref[streams[si].first]; p.push_back(j);
        if (dest[di].first < 0) { chains.push_back(p); amount.push_back(dd); } else { pref.push_back(p); arriving[dest[di].first].push_back({(int)pref.size() - 1, dd}); } }
      sr -= dd; dr -= dd;
      if (sr == 0) { si++; if (si < streams.size()) sr = streams[si].second; }
      if (dr == 0) { di++; if (di < dest.size()) dr = dest[di].second; }
    }
  }
  chainsOf.assign(el.size(), {});
  for (size_t c = 0; c < chains.size(); c++) { cy.push_back((u128)amount[c] << SH); Wup += cy.back(); for (int e : chains[c]) chainsOf[e].push_back((int)c); }
  for (int e = 0; e < m; e++) { u128 cov = 0; for (int c : chainsOf[e]) cov += cy[c]; if ((i128)cov < el[e].wUp) { fprintf(stderr, "cover fails\n"); exit(1); } }
  for (auto& c : chains) for (size_t k = 1; k < c.size(); k++) if (el[c[k]].n % el[c[k - 1]].n) { fprintf(stderr, "not chain\n"); exit(1); }
}

static void buildInstance() {
  u64 L = Y + 2; spf.assign(L, 0);
  for (u64 i = 2; i < L; i++) if (!spf[i]) for (u64 j = i; j < L; j += i) if (!spf[j]) spf[j] = (int)i;
  isPP.assign(L, 0); for (u64 n = 2; n < L; n++) { u64 p = spf[n], m = n; while (m % p == 0) m /= p; isPP[n] = (m == 1); }
  lamLow = S / A; lamUp = (S + A - 1) / A;
  for (u64 n = 6; n <= Y; n++) if (!isPP[n]) {
    Elem e; e.n = n; e.fac = factorSmall(n); e.P = e.fac.back().first;
    e.rLow = S / n; e.rUp = (S + n - 1) / n; e.wUp = (i128)e.rUp - (i128)lamLow; e.costLow = (i128)lamLow - (i128)e.rUp;
    el.push_back(e);
  }
  set<u64> ps; for (auto& e : el) for (auto& f : e.fac) ps.insert(f.first);
  for (u64 p : ps) { pidx[p] = (int)primes.size(); primes.push_back(p); int E = 0; u64 M = 1; while (M <= Y / p) { M *= p; E++; } Mq.push_back(M); Eq.push_back(E); }
  for (auto& e : el) for (auto& f : e.fac) {
    int qi = pidx[f.first]; u64 M = Mq[qi], q = f.first; int v = f.second; u64 u = e.n; for (int k = 0; k < v; k++) u /= q;
    u64 pw = 1; for (int k = 0; k < Eq[qi] - v; k++) pw *= q;
    e.res.push_back({qi, (u64)((u128)pw * inv_mod(u % M, M) % M)});
  }
  int n = el.size(); conf.assign(n, {}); unordered_map<u64,int> id; for (int i = 0; i < n; i++) id[el[i].n] = i;
  for (int i = 0; i < n; i++) for (u64 m = 2 * el[i].n; m <= Y; m += el[i].n) { auto it = id.find(m); if (it != id.end()) { conf[i].push_back(it->second); conf[it->second].push_back(i); } }
  buildChains();
  vector<u64> pl(primes.rbegin(), primes.rend());
  for (u64 p : pl) { Group g; g.p = p; for (int i = 0; i < n; i++) if (el[i].P == p) g.elems.push_back(i); groups.push_back(g); }
}

// ---------------- exact completion ----------------
static vector<u64> coreList; static vector<char> coreMark;  // coreMark[n]=1 if n in core (n<=Y)
static long long nSol = 0; static u64 compCalls = 0, comp2pairs = 0, compN1 = 0;
static vector<string> solLines;
static bool isPrimePowerZ(const Z& n);
static bool admissibleZ(const Z& n, const vector<Z>& chosen) {
  for (u64 c : coreList) if (divisibleU(n, c)) return false;
  for (const Z& c : chosen) if (divisible(n, c) || divisible(c, n)) return false;
  return true;   // prime powers need no test: an exactly verified solution cannot contain one
}
// prime power test for possibly big n: trial division by small primes, then perfect-power + primality
extern "C" int __gmpz_probab_prime_p(mpz_srcptr, int); extern "C" int __gmpz_perfect_power_p(mpz_srcptr);
extern "C" void __gmpz_root(mpz_ptr, mpz_srcptr, unsigned long); extern "C" int __gmpz_root_rem(mpz_ptr, mpz_ptr, mpz_srcptr, unsigned long);
static bool isPrimePowerZ(const Z& n) {
  // returns true if n = p^e, e>=1.  Uses exact arithmetic: find smallest prime factor by trial division
  // up to 10^6; if found, divide it out completely and compare with 1.  Otherwise n has all prime
  // factors > 10^6; then n is a prime power iff it is a perfect power of a prime or prime; we decide
  // with exact root extraction and a strong probable-prime test only to *reject*; ambiguous cases are
  // reported (never silently accepted).
  for (u64 p = 2; p < 1000000 && cmpu(n, p) >= 0; p++) {
    if (p > 2 && p % 2 == 0) continue;
    if (p < spf.size() ? (spf[p] != (int)p) : false) continue;
    if (divisibleU(n, p)) { Z m = n; while (divisibleU(m, p)) { Z t; __gmpz_divexact_ui(t.v, m.v, p); m = t; } return cmpu(m, 1) == 0; }
    if (cmpu(n, p * p) < 0) return true;  // n has no prime factor <= sqrt(n): n prime
  }
  fprintf(stderr, "isPrimePowerZ: undecided for %s\n", n.str().c_str()); exit(5);
}
static void verifyAndReport(const vector<Z>& H) {
  vector<Z> T; for (u64 n : coreList) T.push_back(Z(n)); for (auto& h : H) T.push_back(h);
  Z num(0), den(1);
  for (auto& n : T) { num = num * n + den; den = den * n; Z g = gcd(num, den); num = divexact(num, g); den = divexact(den, g); }
  bool ok = cmp(num, den) == 0;
  for (size_t i = 0; i < T.size(); i++) for (size_t j = 0; j < T.size(); j++) if (i != j && divisible(T[j], T[i])) ok = false;
  nSol++;
  string s = "SOLUTION |T|=" + to_string(T.size()) + " verified=" + to_string((int)ok) + " :";
  for (u64 n : coreList) s += " " + to_string(n); for (auto& h : H) s += " " + h.str();
  printf("%s\n", s.c_str()); fflush(stdout); solLines.push_back(s);
}
// factorization map for denominators: prime -> exponent (primes from core universe and from chosen elements)
typedef vector<pair<Z,int>> Fac;
static void two_term(const Z& a, const Z& b, const Fac& bf, const Z& lowerExcl, const vector<Z>& chosen) {
  // all x<y with 1/x+1/y=a/b, x > lowerExcl.  x=g x', y=g y', gcd(x',y')=1, x'y'|b, a|(x'+y'), g=(b/(x'y'))(x'+y')/a.
  // meet in the middle over the prime powers of b.
  int m = bf.size(); int h1 = m / 2;
  // each prime p^e: choices (fx, fy) with fx*fy=0: x' gets p^fx or y' gets p^fy, 0<=f<=e.
  auto enumHalf = [&](int lo, int hi, vector<pair<Z,Z>>& out) {
    out.clear(); out.push_back({Z(1), Z(1)});
    for (int i = lo; i < hi; i++) {
      vector<pair<Z,Z>> nxt; const Z& p = bf[i].first; int e = bf[i].second;
      for (auto& xy : out) {
        nxt.push_back(xy);
        Z pw = p; for (int f = 1; f <= e; f++) { nxt.push_back({xy.first * pw, xy.second}); nxt.push_back({xy.first, xy.second * pw}); pw = pw * p; }
      }
      out.swap(nxt);
    }
  };
  vector<pair<Z,Z>> L1, L2; enumHalf(0, h1, L1); enumHalf(h1, m, L2);
  bool aOne = cmpu(a, 1) == 0;
  // key for half 1: x1 * y1^{-1} mod a ; for half 2: -y2 * x2^{-1} mod a
  unordered_map<string, vector<int>> idx;
  auto modinv = [&](const Z& v) { Z r; if (!__gmpz_invert(r.v, v.v, a.v)) { fprintf(stderr, "noninvertible\n"); exit(6); } return r; };
  if (!aOne) for (int i = 0; i < (int)L1.size(); i++) { Z k = mod(L1[i].first * modinv(L1[i].second), a); idx[k.str()].push_back(i); }
  for (auto& q2 : L2) {
    vector<int> cand;
    if (aOne) { cand.resize(L1.size()); iota(cand.begin(), cand.end(), 0); }
    else { Z k = mod(a - mod(q2.second * modinv(q2.first), a), a); auto it = idx.find(k.str()); if (it == idx.end()) continue; cand = it->second; }
    for (int i : cand) {
      comp2pairs++;
      Z xp = L1[i].first * q2.first, yp = L1[i].second * q2.second;
      if (cmp(xp, yp) >= 0) continue;           // x' < y'  (x' = y' only if both 1: then x=y, excluded)
      Z s = xp + yp; if (!divisible(s, a)) continue;
      Z r = divexact(b, xp * yp); Z g = divexact(r * s, a);
      Z x = g * xp, y = g * yp;
      if (cmp(x, lowerExcl) <= 0) continue;
      vector<Z> ch = chosen; if (!admissibleZ(x, ch)) continue; ch.push_back(x); if (!admissibleZ(y, ch)) continue; ch.push_back(y);
      vector<Z> H(ch.begin(), ch.end()); verifyAndReport(H);
    }
  }
}
static Fac facCombine(const Fac& bf, const Z& n, const Z& newb) {
  // factorization of newb, whose primes are among those of bf and of n (n factored by trial division)
  Fac r; vector<Z> ps; for (auto& pe : bf) ps.push_back(pe.first);
  Z m = n; for (u64 p = 2; cmpu(m, 1) > 0; p++) { if (p * p > 0 && cmpu(m, p * p) < 0) { ps.push_back(m); break; } if (divisibleU(m, p)) { ps.push_back(Z(p)); while (divisibleU(m, p)) { Z t; __gmpz_divexact_ui(t.v, m.v, p); m = t; } } }
  sort(ps.begin(), ps.end(), [](const Z& x, const Z& y) { return cmp(x, y) < 0; });
  Z rest = newb;
  for (size_t i = 0; i < ps.size(); i++) { if (i && cmp(ps[i], ps[i - 1]) == 0) continue; int e = 0; while (divisible(rest, ps[i])) { rest = divexact(rest, ps[i]); e++; } if (e) r.push_back({ps[i], e}); }
  if (cmpu(rest, 1) != 0) { fprintf(stderr, "facCombine failed\n"); exit(7); }
  return r;
}
static void complete(const Z& a, const Z& b, const Fac& bf, int h, const Z& lowerExcl, vector<Z>& chosen) {
  compCalls++;
  if (h == 1) { if (divisible(b, a)) { Z n = divexact(b, a); if (cmp(n, lowerExcl) > 0 && admissibleZ(n, chosen)) { chosen.push_back(n); verifyAndReport(chosen); chosen.pop_back(); } } return; }
  if (h == 2) { two_term(a, b, bf, lowerExcl, chosen); return; }
  // h >= 3: smallest element n in (b/a, h b/a], n > lowerExcl
  Z lo = fdiv(b, a); if (cmp(lo, lowerExcl) < 0) lo = lowerExcl; Z hi = fdiv(b * (unsigned long)h, a);
  for (Z n = lo + Z(1); cmp(n, hi) <= 0; n = n + Z(1)) {
    compN1++;
    if (!admissibleZ(n, chosen)) continue;
    Z na = a * n - b, nb = b * n; Z g = gcd(na, nb); na = divexact(na, g); nb = divexact(nb, g);
    Fac nf = facCombine(bf, n, nb);
    chosen.push_back(n); complete(na, nb, nf, h - 1, n, chosen); chosen.pop_back();
  }
}

// ---------------- core search ----------------
struct UItem { u64 q; int e; };
struct Searcher {
  vector<char> st; vector<int> live; vector<char> hitc;
  i128 UB; int count = 0; u128 sumLow = 0; i128 costLow = 0; vector<u64> R;
  vector<UItem> U; int hmin = 0; vector<int> stackEx; vector<char> inSet;
  u64 nodes = 0, leaves = 0, coresByH[16] = {0};
  Searcher() { st.assign(el.size(), 0); live.assign(chains.size(), 0); hitc.assign(chains.size(), 0);
    for (size_t c = 0; c < chains.size(); c++) live[c] = (int)chains[c].size(); UB = (i128)Wup; R.assign(primes.size(), 0); inSet.assign(Y + 1, 0); }
  void exRaw(int f) { st[f] = 2; for (int c : chainsOf[f]) if (--live[c] == 0 && !hitc[c]) UB -= (i128)cy[c]; }
  void unExRaw(int f) { for (int c : chainsOf[f]) if (live[c]++ == 0 && !hitc[c]) UB += (i128)cy[c]; st[f] = 0; }
  size_t include(int e) {
    Elem& E = el[e]; st[e] = 1; count++; sumLow += E.rLow; inSet[E.n] = 1;
    if (E.n < A) { UB += E.wUp; for (int c : chainsOf[e]) if (!hitc[c]) { if (live[c] > 0) UB -= (i128)cy[c]; hitc[c] = 1; } } else costLow += E.costLow;
    for (auto& r : E.res) R[r.first] = (R[r.first] + r.second) % Mq[r.first];
    size_t mark = stackEx.size(); for (int f : conf[e]) if (st[f] == 0) { exRaw(f); stackEx.push_back(f); } return mark;
  }
  void uninclude(int e, size_t mark) {
    while (stackEx.size() > mark) { unExRaw(stackEx.back()); stackEx.pop_back(); }
    Elem& E = el[e]; for (auto& r : E.res) R[r.first] = (R[r.first] + Mq[r.first] - r.second) % Mq[r.first];
    if (E.n < A) { UB -= E.wUp; for (int c : chainsOf[e]) { hitc[c] = 0; if (live[c] > 0) UB += (i128)cy[c]; } } else costLow -= E.costLow;
    st[e] = 0; count--; sumLow -= E.rLow; inSet[E.n] = 0;
  }
  bool pruned() {
    if (sumLow > S) return true;
    if (count + hmin > K) return true;
    i128 rhs = (i128)K * (i128)lamUp + UB - costLow - (i128)hmin * cexpLow;
    return rhs < (i128)S;
  }
  // conflict between two U-primes: an element divisible by q^eq r^er is a multiple of a core element
  bool conflictU(const UItem& a, const UItem& b) {
    u64 pa = 1; for (int i = 0; i < a.e; i++) pa *= a.q; u64 pb = 1; for (int i = 0; i < b.e; i++) pb *= b.q;
    // check every divisor d = q^i r^j (i<=ea, j<=eb, i,j>=1) of pa*pb that is <= Y and in the core
    for (u64 x = a.q; x <= pa && x <= Y; x *= a.q) for (u64 y = b.q; y <= pb && x * y <= Y; y *= b.q) if (inSet[x * y]) return true;
    return false;
  }
  int chromatic() {
    int n = U.size(); if (n == 0) return 0;
    vector<vector<char>> adj(n, vector<char>(n, 0));
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) adj[i][j] = adj[j][i] = conflictU(U[i], U[j]);
    vector<int> order(n); iota(order.begin(), order.end(), 0);
    sort(order.begin(), order.end(), [&](int x, int y) { int dx = 0, dy = 0; for (int k = 0; k < n; k++) { dx += adj[x][k]; dy += adj[y][k]; } return dx > dy; });
    int best = n + 1; vector<int> col(n, -1);
    function<void(int,int)> rec = [&](int i, int used) {
      if (used >= best) return; if (i == n) { best = used; return; }
      int v = order[i];
      for (int c = 0; c <= used && c < best; c++) {
        bool ok = true; for (int j = 0; j < i; j++) if (adj[v][order[j]] && col[order[j]] == c) { ok = false; break; }
        if (!ok) continue; col[v] = c; rec(i + 1, max(used, c + 1)); col[v] = -1;
      }
    };
    rec(0, 0); return best;
  }
  void leaf() {
    leaves++;
    coreList.clear(); for (size_t i = 0; i < el.size(); i++) if (st[i] == 1) coreList.push_back(el[i].n);
    Z num(0), den(1);
    for (u64 n : coreList) { Z nn(n); num = num * nn + den; den = den * nn; Z g = gcd(num, den); num = divexact(num, g); den = divexact(den, g); }
    int h = K - count;
    if (U.empty()) { if (h == 0 && cmp(num, den) == 0) { vector<Z> none; verifyAndReport(none); } return; }
    if (h < hmin || h > HMAX || h < 1) return;
    Z a = den - num, b = den; if (a.sgn() <= 0) return;
    // each huge element is >= Y+1:  a/b <= h/(Y+1)
    if (cmp(a * (Y + 1), b * (unsigned long)h) > 0) return;
    // consistency: b = prod q^e over U
    Z bb(1); for (auto& u : U) for (int i = 0; i < u.e; i++) bb = bb * u.q; if (cmp(bb, b) != 0) { fprintf(stderr, "residue/denominator mismatch\n"); exit(8); }
    coresByH[h]++;
    if (dumpF) { for (u64 n : coreList) fprintf(dumpF, "%llu ", (unsigned long long)n); fprintf(dumpF, "| h=%d %s/%s\n", h, a.str().c_str(), b.str().c_str()); }
    if (doComplete) { Fac bf; for (auto& u : U) bf.push_back({Z(u.q), u.e}); vector<Z> ch; complete(a, b, bf, h, Z(Y), ch); }
  }
  FILE* dumpF = nullptr; bool doComplete = true;
  void dfs(size_t gi, size_t k) {
    nodes++;
    if (pruned()) return;
    if (gi == groups.size()) { leaf(); return; }
    Group& G = groups[gi];
    if (k == G.elems.size()) {
      int qi = pidx[G.p]; u64 r = R[qi];
      if (r != 0) { u64 q = G.p; int v = 0; u64 rr = r; while (rr % q == 0) { rr /= q; v++; }
        U.push_back({q, Eq[qi] - v}); int old = hmin; hmin = chromatic();
        if (hmin <= HMAX) dfs(gi + 1, 0);
        hmin = old; U.pop_back();
      } else dfs(gi + 1, 0);
      return;
    }
    int e = G.elems[k];
    if (st[e] == 0) {
      if (count + 1 + hmin <= K) { size_t m = include(e); dfs(gi, k + 1); uninclude(e, m); }
      exRaw(e); dfs(gi, k + 1); unExRaw(e);
    } else dfs(gi, k + 1);
  }
};

int main(int argc, char** argv) {
  // usage: q2k K A [Y] [nocomplete] [dumpfile]
  K = atoi(argv[1]); A = strtoull(argv[2], 0, 10);
  if (argc > 3) Y = strtoull(argv[3], 0, 10);
  bool doComp = !(argc > 4 && string(argv[4]) == "nocomplete");
  auto t0 = chrono::steady_clock::now();
  bool autoY = (Y == 0);
  if (autoY) {
    // first pass with Y = A: the chain cover only uses elements < A
    Y = A; buildInstance();
    i128 sig = (i128)K * (i128)lamUp + (i128)Wup - (i128)S;
    int hinf = 0; while ((i128)(hinf + 1) * (i128)lamLow <= sig) hinf++;   // max # elements of cost < lambda
    // smallest Y with (hinf+1) * (lamLow - ceil(S/(Y+1))) > sig
    u64 y = A; while ((i128)(hinf + 1) * ((i128)lamLow - (i128)((S + y) / (y + 1))) <= sig) y++;
    Y = y;
    el.clear(); conf.clear(); primes.clear(); pidx.clear(); Mq.clear(); Eq.clear(); chains.clear(); cy.clear(); chainsOf.clear(); Wup = 0; groups.clear();
  }
  buildInstance();
  // sigma_up = K*lamUp + Wup - S  (upper bound for K lambda + W - 1, scaled)
  i128 sigmaUp = (i128)K * (i128)lamUp + (i128)Wup - (i128)S;
  // hmax: largest h with h * (lamLow - ceil(S/(Y+1))) <= sigmaUp
  cexpLow = (i128)lamLow - (i128)((S + Y) / (Y + 1));
  HMAX = 0; while ((i128)(HMAX + 1) * cexpLow <= sigmaUp) HMAX++;
  // check: (HMAX+1) elements > Y are impossible: (HMAX+1)*cexpLow > sigmaUp holds by construction
  printf("K=%d A=%llu Y=%llu hmax=%d universe=%zu chains=%zu groups=%zu sigmaUp*1e9/S=%lld\n", K, (unsigned long long)A, (unsigned long long)Y, HMAX, el.size(), chains.size(), groups.size(), (long long)(sigmaUp / (i128)(S / 1000000000ULL)));
  fflush(stdout);
  Searcher s; s.doComplete = doComp; if (argc > 5) s.dumpF = fopen(argv[5], "w");
  s.dfs(0, 0);
  double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
  printf("DONE K=%d A=%llu Y=%llu nodes=%llu leaves=%llu", K, (unsigned long long)A, (unsigned long long)Y, (unsigned long long)s.nodes, (unsigned long long)s.leaves);
  for (int h = 0; h <= HMAX; h++) printf(" cores[h=%d]=%llu", h, (unsigned long long)s.coresByH[h]);
  printf(" completionCalls=%llu twoTermPairs=%llu n1=%llu solutions=%lld time=%.2fs\n", (unsigned long long)compCalls, (unsigned long long)comp2pairs, (unsigned long long)compN1, nSol, secs);
  if (s.dumpF) fclose(s.dumpF);
}
