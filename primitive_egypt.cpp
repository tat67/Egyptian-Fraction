// primitive_egypt.cpp
//
// Egyptian fractions with a primitive (divisibility-antichain) set of denominators.
//
//   Find nonempty finite T ⊆ {2, 3, 4, ...} with  sum_{n in T} 1/n = 1  and  m ∤ n  for all
//   distinct m, n in T.  (T = {1} is the trivial solution; every other valid set avoids 1,
//   because 1 divides everything.)
//
//   Q1: the least possible  max T.        Answer computed here: 413 = 7 * 59.
//   Q2: the least possible  |T|.          (see README_PRIMITIVE.md)
//
// Everything is exact: machine integers and a small big-natural type.  The program contains
// no floating-point type.
//
// ---------------------------------------------------------------------------------------
// The method (Q1)
//
//  (a) No prime power p^k (k >= 1) lies in a solution T.  Every other n in T with
//      v_p(n) >= k would be a multiple of p^k, so 1/p^k is the only term of p-adic valuation
//      -k and the sum is not an integer.  (Lean: `no_primePow`.)  Hence for a bound B,
//      T ⊆ U_B = { n in [2, B] : n not a prime power }.
//  (b) Scaling.  D_B = lcm(U_B).  Sum 1/n = 1  <=>  sum_{n in T} D/n = D.
//  (c) Congruences.  For a prime p let M = p^{v_p(D)} = gcd(D, p^B).  M divides D and D/n for
//      every n with p ∤ n, so  sum_{n in T, p | n} (D/n mod M) ≡ 0 (mod M).
//  (d) Chain bound.  A family of divisibility chains C with weights y_C covering every
//      n in U_B (sum_{C ∋ n} y_C >= D/n) bounds every antichain T ⊆ U_B \ Out:
//      sum_T D/n <= sum_{C : C ⊄ Out} y_C, because an antichain meets a chain at most once.
//      The chains come from a maximum flow (weighted Dilworth), so at the start the bound is
//      the maximum weight of an antichain in U_B.
//  (e) Search / certificate.  A node is a partial assignment (in / out / undecided).
//      Putting n in T automatically puts all its multiples and divisors out.  A node is closed
//      by   hi : sum_in D/n > D,   lo : chain bound < D,   md p : the congruence at p cannot
//      be met by the undecided elements (subset sums as a residue bit set).
//  (f) Q1 scan: for m = 6, 7, ... in U the program searches U_m with m forced in; the first
//      success is min max T.  Then it searches U_{m*-1} with nothing forced and records the
//      whole tree as a certificate.  The certificate is re-checked here by an independent
//      checker with the semantics of the Lean function `check` (lean/SemiprimeEgypt/PrimCheck.lean)
//      and written as Lean files, which the Lean kernel checks.
//
// Build:  g++ -O2 -std=c++17 -o primitive_egypt primitive_egypt.cpp
// Run:    ./primitive_egypt q1 [--cert DIR]      Q1 (and the Lean certificate in DIR)
// ---------------------------------------------------------------------------------------

#include <algorithm>
#include <bitset>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <map>
#include <numeric>
#include <queue>
#include <string>
#include <vector>

using namespace std;
typedef uint64_t u64;
typedef int64_t i64;

// ------------------------------------------------------------------------------------------
// Big natural numbers (base 2^32, little endian)
// ------------------------------------------------------------------------------------------
struct BigNat {
  vector<uint32_t> d;
  BigNat() {}
  explicit BigNat(u64 x) { while (x) { d.push_back((uint32_t)x); x >>= 32; } }
  void trim() { while (!d.empty() && d.back() == 0) d.pop_back(); }
  bool isZero() const { return d.empty(); }
};
static int cmp(const BigNat& a, const BigNat& b) {
  if (a.d.size() != b.d.size()) return a.d.size() < b.d.size() ? -1 : 1;
  for (int i = (int)a.d.size() - 1; i >= 0; i--)
    if (a.d[i] != b.d[i]) return a.d[i] < b.d[i] ? -1 : 1;
  return 0;
}
static BigNat add(const BigNat& a, const BigNat& b) {
  BigNat r; u64 c = 0; size_t n = max(a.d.size(), b.d.size()); r.d.resize(n);
  for (size_t i = 0; i < n; i++) {
    u64 t = c + (i < a.d.size() ? a.d[i] : 0) + (i < b.d.size() ? b.d[i] : 0);
    r.d[i] = (uint32_t)t; c = t >> 32;
  }
  if (c) r.d.push_back((uint32_t)c);
  r.trim(); return r;
}
static BigNat sub(const BigNat& a, const BigNat& b) {  // requires a >= b
  if (cmp(a, b) < 0) { fprintf(stderr, "BigNat underflow\n"); exit(2); }
  BigNat r; r.d.resize(a.d.size()); i64 br = 0;
  for (size_t i = 0; i < a.d.size(); i++) {
    i64 t = (i64)a.d[i] - br - (i < b.d.size() ? (i64)b.d[i] : 0);
    if (t < 0) { t += ((i64)1 << 32); br = 1; } else br = 0;
    r.d[i] = (uint32_t)t;
  }
  r.trim(); return r;
}
static BigNat mulSmall(const BigNat& a, uint32_t m) {
  BigNat r; u64 c = 0;
  for (uint32_t x : a.d) { u64 t = (u64)x * m + c; r.d.push_back((uint32_t)t); c = t >> 32; }
  if (c) r.d.push_back((uint32_t)c);
  r.trim(); return r;
}
static BigNat mulU64(const BigNat& a, u64 m) {  // a * m
  BigNat lo = mulSmall(a, (uint32_t)m), hi = mulSmall(a, (uint32_t)(m >> 32));
  if (!hi.isZero()) hi.d.insert(hi.d.begin(), 0);
  return add(lo, hi);
}
static BigNat shrCeil(const BigNat& a, int bits) {  // ceil(a / 2^bits)
  BigNat r; int limbs = bits / 32, sh = bits % 32; bool rem = false;
  for (int i = 0; i < limbs && i < (int)a.d.size(); i++) if (a.d[i]) rem = true;
  if (limbs < (int)a.d.size() && sh && (a.d[limbs] & ((1u << sh) - 1))) rem = true;
  for (size_t i = limbs; i < a.d.size(); i++) {
    u64 v = a.d[i] >> sh;
    if (sh && i + 1 < a.d.size()) v |= ((u64)a.d[i + 1] << (32 - sh)) & 0xffffffffULL;
    r.d.push_back((uint32_t)v);
  }
  r.trim();
  if (rem) r = add(r, BigNat(1));
  return r;
}
static BigNat divSmall(const BigNat& a, uint32_t m, uint32_t* rem = nullptr) {
  BigNat r; r.d.assign(a.d.size(), 0); u64 rm = 0;
  for (int i = (int)a.d.size() - 1; i >= 0; i--) {
    u64 cur = (rm << 32) | a.d[i]; r.d[i] = (uint32_t)(cur / m); rm = cur % m;
  }
  r.trim(); if (rem) *rem = (uint32_t)rm; return r;
}
static u64 modSmall(const BigNat& a, u64 m) {
  unsigned __int128 rm = 0;
  for (int i = (int)a.d.size() - 1; i >= 0; i--) rm = ((rm << 32) | a.d[i]) % m;
  return (u64)rm;
}
static string toDec(BigNat a) {
  if (a.isZero()) return "0";
  vector<uint32_t> parts;
  while (!a.isZero()) { uint32_t r; a = divSmall(a, 1000000000u, &r); parts.push_back(r); }
  string s = to_string(parts.back()); char buf[16];
  for (int i = (int)parts.size() - 2; i >= 0; i--) { snprintf(buf, sizeof buf, "%09u", parts[i]); s += buf; }
  return s;
}
static BigNat bitmask(const vector<int>& bits) {
  BigNat r; int mx = 0; for (int b : bits) mx = max(mx, b);
  r.d.assign(mx / 32 + 1, 0);
  for (int b : bits) r.d[b / 32] |= (1u << (b % 32));
  r.trim(); return r;
}

// ------------------------------------------------------------------------------------------
// Elementary number theory
// ------------------------------------------------------------------------------------------
static bool isPrime(i64 n) { if (n < 2) return false; for (i64 d = 2; d * d <= n; d++) if (n % d == 0) return false; return true; }
static bool isPrimePower(i64 n) {
  if (n < 2) return false;
  for (i64 p = 2; p * p <= n; p++) if (n % p == 0) { while (n % p == 0) n /= p; return n == 1; }
  return true;  // n prime
}
static string factorStr(i64 n) {
  string s; bool first = true;
  for (i64 p = 2; p * p <= n; p++) if (n % p == 0) {
    int k = 0; while (n % p == 0) { n /= p; k++; }
    s += (first ? "" : "*") + to_string(p) + (k > 1 ? "^" + to_string(k) : ""); first = false;
  }
  if (n > 1) s += (first ? "" : "*") + to_string(n);
  return s;
}

// ------------------------------------------------------------------------------------------
// Max flow (Dinic) on u64 capacities, used only to find a good chain cover
// ------------------------------------------------------------------------------------------
struct Dinic {
  struct E { int to; u64 cap; int rev; };
  vector<vector<E>> G; vector<int> lvl, it;
  explicit Dinic(int n) : G(n) {}
  void addEdge(int a, int b, u64 c) { G[a].push_back({b, c, (int)G[b].size()}); G[b].push_back({a, 0, (int)G[a].size() - 1}); }
  bool bfs(int s, int t) {
    lvl.assign(G.size(), -1); queue<int> q; q.push(s); lvl[s] = 0;
    while (!q.empty()) { int v = q.front(); q.pop(); for (auto& e : G[v]) if (e.cap && lvl[e.to] < 0) { lvl[e.to] = lvl[v] + 1; q.push(e.to); } }
    return lvl[t] >= 0;
  }
  u64 dfs(int v, int t, u64 f) {
    if (v == t) return f;
    for (int& i = it[v]; i < (int)G[v].size(); i++) {
      E& e = G[v][i];
      if (e.cap && lvl[e.to] == lvl[v] + 1) { u64 d = dfs(e.to, t, min(f, e.cap)); if (d) { e.cap -= d; G[e.to][e.rev].cap += d; return d; } }
    }
    return 0;
  }
  u64 run(int s, int t) { u64 F = 0; while (bfs(s, t)) { it.assign(G.size(), 0); while (u64 f = dfs(s, t, ~0ULL)) F += f; } return F; }
};

// ------------------------------------------------------------------------------------------
// Instance: the candidate elements U_B, weights, congruence data, chain cover
// ------------------------------------------------------------------------------------------
size_t subSizeG = 3000;
const int KBITS = 50;               // scale 2^50 for the flow computation
const u64 KSCALE = 1ULL << KBITS;
typedef bitset<1024> BS;

struct Instance {
  int B;
  vector<int> U;                     // non-prime-powers in [2, B], ascending
  vector<int> uidx;                  // n -> index or -1
  vector<int> primes;                // primes p with 2p <= B
  BigNat D;                          // lcm(U)
  vector<int> Mp;                    // p^{v_p(D)}
  vector<vector<int>> inc;           // per prime: indices of multiples of p in U (ascending)
  vector<vector<int>> incRes;        // (D/n) mod Mp
  vector<vector<int>> pdiv;          // per element: prime indices dividing it
  vector<vector<int>> conf;          // per element: multiples and divisors in U
  vector<BigNat> w;                  // D/n
  vector<vector<int>> chains;        // element indices, ascending by n
  vector<BigNat> cy;                 // exact chain weights
  vector<vector<int>> chainsOf;      // per element: chain indices
  BigNat cb0;                        // sum of all chain weights = initial bound

  explicit Instance(int B_) : B(B_) {
    uidx.assign(B + 1, -1);
    for (int n = 2; n <= B; n++) if (!isPrimePower(n)) { uidx[n] = (int)U.size(); U.push_back(n); }
    for (int p = 2; 2 * p <= B; p++) if (isPrime(p)) primes.push_back(p);
    // D = lcm(U)
    D = BigNat(1);
    for (int p = 2; p <= B; p++) if (isPrime(p)) {
      int mx = 0;
      for (int n : U) { int k = 0, m = n; while (m % p == 0) { m /= p; k++; } mx = max(mx, k); }
      for (int j = 0; j < mx; j++) D = mulSmall(D, (uint32_t)p);
    }
    int n = (int)U.size();
    w.resize(n); for (int i = 0; i < n; i++) w[i] = divSmall(D, (uint32_t)U[i]);
    pdiv.assign(n, {});
    for (size_t pi = 0; pi < primes.size(); pi++) {
      int p = primes[pi]; u64 M = 1;
      while (modSmall(D, M * p) == 0) M *= p;
      if (M > 1024) { fprintf(stderr, "modulus %llu too large\n", (unsigned long long)M); exit(1); }
      Mp.push_back((int)M);
      inc.push_back({}); incRes.push_back({});
      for (int j = 1; j * p <= B; j++) {
        int e = uidx[j * p]; if (e < 0) continue;
        inc.back().push_back(e); incRes.back().push_back((int)modSmall(w[e], M)); pdiv[e].push_back((int)pi);
      }
    }
    conf.assign(n, {});
    for (int a = 0; a < n; a++) for (int m = 2 * U[a]; m <= B; m += U[a]) if (uidx[m] >= 0) { conf[a].push_back(uidx[m]); conf[uidx[m]].push_back(a); }
    for (auto& c : conf) sort(c.begin(), c.end());
    vector<u64> wk(U.size()); for (size_t i = 0; i < U.size(); i++) wk[i] = (KSCALE + U[i] - 1) / U[i];
    buildChains(wk, w);
  }

  // chain cover from a maximum flow on the scaled weights wk (weighted Dilworth); the exact chain
  // weights y = ceil(amount * D / 2^50) satisfy  sum_{C ∋ e} y_C >= target[e]
  void buildChains(const vector<u64>& wk, const vector<BigNat>& target) {
    int n = (int)U.size();
    Dinic g(2 * n + 2); int s = 2 * n, t = 2 * n + 1;
    for (int i = 0; i < n; i++) { g.addEdge(s, i, wk[i]); g.addEdge(n + i, t, wk[i]); }
    for (int i = 0; i < n; i++) for (int j : conf[i]) if (U[j] > U[i]) g.addEdge(i, n + j, ~0ULL >> 2);
    g.run(s, t);
    vector<vector<pair<int, u64>>> out(n);
    for (int i = 0; i < n; i++) for (auto& e : g.G[i]) if (e.to >= n && e.to < 2 * n) {
      u64 f = g.G[e.to][e.rev].cap; if (f) out[i].push_back({e.to - n, f});
    }
    // decompose the flow into weighted chains (streams through each node in increasing order)
    vector<vector<pair<int, u64>>> arriving(n);
    vector<vector<int>> pref;
    vector<u64> amount;
    for (int j = 0; j < n; j++) {  // U ascending = a topological order of divisibility
      vector<pair<int, u64>> streams = arriving[j]; u64 have = 0;
      for (auto& x : streams) have += x.second;
      if (have < wk[j]) { pref.push_back({}); streams.push_back({(int)pref.size() - 1, wk[j] - have}); }
      if (wk[j] == 0) continue;
      vector<pair<int, u64>> dest; u64 outsum = 0;
      for (auto& o : out[j]) { dest.push_back(o); outsum += o.second; }
      if (wk[j] > outsum) dest.push_back({-1, wk[j] - outsum});
      size_t si = 0, di = 0; u64 sr = streams[0].second, dr = dest[0].second;
      while (si < streams.size() && di < dest.size()) {
        u64 dd = min(sr, dr);
        if (dd) {
          vector<int> p = pref[streams[si].first]; p.push_back(j);
          if (dest[di].first < 0) { chains.push_back(p); amount.push_back(dd); }
          else { pref.push_back(p); arriving[dest[di].first].push_back({(int)pref.size() - 1, dd}); }
        }
        sr -= dd; dr -= dd;
        if (sr == 0) { si++; if (si < streams.size()) sr = streams[si].second; }
        if (dr == 0) { di++; if (di < dest.size()) dr = dest[di].second; }
      }
    }
    // exact weights: y = ceil(amount * D / 2^50); then sum_{C ∋ e} y >= D/e
    chainsOf.assign(n, {});
    for (size_t c = 0; c < chains.size(); c++) {
      cy.push_back(shrCeil(mulU64(D, amount[c]), KBITS));
      cb0 = add(cb0, cy.back());
      for (int e : chains[c]) chainsOf[e].push_back((int)c);
    }
    // verification (exact)
    for (int e = 0; e < n; e++) {
      BigNat cov; for (int c : chainsOf[e]) cov = add(cov, cy[c]);
      if (cmp(cov, target[e]) < 0) { fprintf(stderr, "chain cover fails at %d\n", U[e]); exit(1); }
    }
    for (auto& c : chains) for (size_t k = 1; k < c.size(); k++)
      if (U[c[k]] % U[c[k - 1]]) { fprintf(stderr, "not a chain\n"); exit(1); }
  }
};

// ------------------------------------------------------------------------------------------
// The search
// ------------------------------------------------------------------------------------------
enum { UND = 0, IN = 1, OUT = 2 };
struct CertNode { int type; int arg; int a, b; };  // 0 lo, 1 hi, 2 md p, 3 br n (a: in, b: out), 4 solution

struct Solver {
  const Instance& I;
  bool record = false, countAll = false;
  vector<int8_t> st;
  BigNat sIn, cb;
  vector<int> live;              // per chain: number of elements not out
  vector<vector<int>> autoOut;   // stack of automatic exclusions
  u64 nodes = 0, solutions = 0, limit = ~0ULL;
  bool stop = false;
  vector<int> firstSolution;
  vector<vector<int>> allSolutions;
  vector<CertNode> tree;

  explicit Solver(const Instance& inst) : I(inst) {
    st.assign(I.U.size(), UND); cb = I.cb0;
    live.resize(I.chains.size()); for (size_t c = 0; c < I.chains.size(); c++) live[c] = (int)I.chains[c].size();
  }
  void outRaw(int e) { st[e] = OUT; for (int c : I.chainsOf[e]) if (--live[c] == 0) cb = sub(cb, I.cy[c]); }
  void unOutRaw(int e) { st[e] = UND; for (int c : I.chainsOf[e]) if (live[c]++ == 0) cb = add(cb, I.cy[c]); }
  void setOut(int e) { outRaw(e); }
  void unOut(int e) { unOutRaw(e); }
  void setIn(int e) {
    st[e] = IN; sIn = add(sIn, I.w[e]);
    vector<int> ex;
    for (int f : I.conf[e]) if (st[f] == UND) { ex.push_back(f); outRaw(f); }
    autoOut.push_back(ex);
  }
  void unIn(int e) {
    vector<int> ex = autoOut.back(); autoOut.pop_back();
    for (int i = (int)ex.size() - 1; i >= 0; i--) unOutRaw(ex[i]);
    st[e] = UND; sIn = sub(sIn, I.w[e]);
  }
  static BS rotAdd(const BS& S, int a, int M) {
    BS mask; for (int i = 0; i < M; i++) mask[i] = 1;
    return S | (((S << a) | (S >> (M - a))) & mask);
  }
  bool mdLeaf(int pi) const {
    int M = I.Mp[pi], rho = 0; BS R; R[0] = 1;
    for (size_t t = 0; t < I.inc[pi].size(); t++) {
      int e = I.inc[pi][t], a = I.incRes[pi][t];
      if (st[e] == IN) rho = (rho + a) % M;
      else if (st[e] == UND && a) R = rotAdd(R, a, M);
    }
    return !R[(M - rho) % M];
  }
  // leaf test at the current node: 0 lo, 1 hi, 2 md (prime in *q); -1 none
  int leaf(int* q) const {
    if (cmp(sIn, I.D) > 0) return 1;
    if (cmp(cb, I.D) < 0) return 0;
    for (size_t pi = 0; pi < I.primes.size(); pi++) if (mdLeaf((int)pi)) { *q = I.primes[pi]; return 2; }
    return -1;
  }
  int mk(int type, int arg, int a = -1, int b = -1) {
    if (!record) return -1;
    tree.push_back({type, arg, a, b}); return (int)tree.size() - 1;
  }
  // forced move: returns element, *dir (0 out, 1 in), *lt/*lq the leaf closing the other side
  int forced(int* dir, int* lt, int* lq) {
    int n = (int)I.U.size();
    for (int e = 0; e < n; e++) if (st[e] == UND) {
      if (cmp(add(sIn, I.w[e]), I.D) > 0) { *dir = 0; *lt = 1; return e; }
    }
    for (int e = 0; e < n; e++) if (st[e] == UND) {
      BigNat d; for (int c : I.chainsOf[e]) if (live[c] == 1) d = add(d, I.cy[c]);
      if (cmp(cb, I.D) >= 0 && cmp(sub(cb, d), I.D) < 0) { *dir = 1; *lt = 0; return e; }
    }
    for (size_t pi = 0; pi < I.primes.size(); pi++) {
      int M = I.Mp[pi], rho = 0; vector<int> und, av;
      for (size_t t = 0; t < I.inc[pi].size(); t++) {
        int e = I.inc[pi][t], a = I.incRes[pi][t];
        if (st[e] == IN) rho = (rho + a) % M;
        else if (st[e] == UND && a) { und.push_back(e); av.push_back(a); }
      }
      int k = (int)und.size(), target = (M - rho) % M;
      vector<BS> pre(k + 1), suf(k + 1);
      pre[0][0] = 1; for (int i = 0; i < k; i++) pre[i + 1] = rotAdd(pre[i], av[i], M);
      suf[k][0] = 1; for (int i = k - 1; i >= 0; i--) suf[i] = rotAdd(suf[i + 1], av[i], M);
      for (int i = 0; i < k; i++) {
        auto reach = [&](int t) { for (int x = 0; x < M; x++) if (pre[i][x] && suf[i + 1][(t - x + M) % M]) return true; return false; };
        if (!reach(target)) { *dir = 1; *lt = 2; *lq = I.primes[pi]; return und[i]; }
        if (!reach((target - av[i] + M) % M)) { *dir = 0; *lt = 2; *lq = I.primes[pi]; return und[i]; }
      }
    }
    return -1;
  }
  u64 completions(int pi, int* first, int* k) const {
    int M = I.Mp[pi], rho = 0; vector<u64> c(M, 0), c2(M); c[0] = 1; *first = -1; *k = 0;
    for (size_t t = 0; t < I.inc[pi].size(); t++) {
      int e = I.inc[pi][t], a = I.incRes[pi][t];
      if (st[e] == IN) rho = (rho + a) % M;
      else if (st[e] == UND) {
        (*k)++; if (*first < 0) *first = e;
        c2 = c;
        for (int x = 0; x < M; x++) { u64& y = c2[(x + a) % M]; y = (y > ~0ULL - c[x]) ? ~0ULL : y + c[x]; }
        c.swap(c2);
      }
    }
    return c[(M - rho) % M];
  }
  int dfs() {
    if (stop) return -1;
    if (++nodes > limit) { stop = true; return -1; }
    int q = 0, L = leaf(&q);
    if (L >= 0) return mk(L, L == 2 ? q : 0);
    int dir, lt, lq = 0, e = forced(&dir, &lt, &lq);
    if (e >= 0) {
      int lf = mk(lt, lt == 2 ? lq : 0);
      if (dir == 0) { setOut(e); int r = dfs(); unOut(e); return mk(3, I.U[e], lf, r); }
      setIn(e); int r = dfs(); unIn(e); return mk(3, I.U[e], r, lf);
    }
    int best = -1; u64 bc = ~0ULL;
    for (size_t pi = 0; pi < I.primes.size(); pi++) { int f, k; u64 c = completions((int)pi, &f, &k); if (k > 0 && c < bc) { bc = c; best = f; } }
    if (best < 0) {
      // no undecided multiple of any prime is left, and no test closes the node: all congruences
      // hold and sum_in <= D <= chain bound; check whether the in-set is a solution
      bool anyUnd = false; for (auto x : st) if (x == UND) anyUnd = true;
      if (!anyUnd && cmp(sIn, I.D) == 0) {
        solutions++;
        vector<int> v; for (size_t i = 0; i < st.size(); i++) if (st[i] == IN) v.push_back(I.U[i]);
        if (firstSolution.empty()) firstSolution = v;
        if (countAll && allSolutions.size() < 1000) allSolutions.push_back(v);
        if (!countAll) stop = true;
        return mk(4, 0);
      }
      if (!anyUnd) { fprintf(stderr, "internal: complete assignment with sum != 1 not closed\n"); exit(3); }
      for (size_t i = 0; i < st.size(); i++) if (st[i] == UND) { best = (int)i; break; }
    }
    setIn(best); int x = dfs(); unIn(best);
    setOut(best); int y = dfs(); unOut(best);
    return mk(3, I.U[best], x, y);
  }
};

// ------------------------------------------------------------------------------------------
// Independent checker with the semantics of the Lean `check` (PrimCheck.lean).
// State: in/out bit sets indexed by n, sIn, cb.  The universe EM = U_B.
// ------------------------------------------------------------------------------------------
struct TreeChecker {
  const Instance& I; const vector<CertNode>& T;
  int B; vector<char> EM, PM, inn, out; BigNat sIn, cb;
  vector<vector<int>> chainN;     // chains as lists of n
  vector<vector<int>> chainsOfN;  // n -> chain indices
  u64 checked = 0;
  TreeChecker(const Instance& inst, const vector<CertNode>& tr) : I(inst), T(tr) {
    B = I.B; EM.assign(B + 1, 0); PM.assign(B + 1, 0); inn.assign(B + 1, 0); out.assign(B + 1, 0);
    for (int n : I.U) EM[n] = 1;
    for (int p : I.primes) PM[p] = 1;
    chainsOfN.assign(B + 1, {});
    for (size_t c = 0; c < I.chains.size(); c++) {
      vector<int> v; for (int e : I.chains[c]) { v.push_back(I.U[e]); chainsOfN[I.U[e]].push_back((int)c); }
      chainN.push_back(v);
    }
    cb = I.cb0;
  }
  bool chainDead(int c) const { for (int n : chainN[c]) if (EM[n] && !out[n]) return false; return true; }
  // exclude n: set its out bit, subtract the chains through n that are now dead
  void excl(int n, vector<pair<int, BigNat>>& undo) {
    out[n] = 1;
    for (int c : chainsOfN[n]) if (chainDead(c)) { undo.push_back({c, I.cy[c]}); cb = sub(cb, I.cy[c]); }
  }
  bool md(int p) const {
    if (p < 0 || p > B || !PM[p]) return false;
    // M = gcd(D, p^B) = p^{v_p(D)}
    u64 M = 1; while (modSmall(I.D, M * p) == 0 && M * p <= (1ULL << 40)) M *= p;
    if (M > 1024) return false;
    int rho = 0; BS R; R[0] = 1;
    for (int j = 1; j * p <= B; j++) {
      int n = j * p; if (!EM[n]) continue;
      int a = (int)modSmall(divSmall(I.D, (uint32_t)n), M);
      if (inn[n]) rho = (int)((rho + a) % M);
      else if (!out[n]) R = Solver::rotAdd(R, a, (int)M);
    }
    return !R[(M - rho) % M];
  }
  bool check(int v) {
    checked++;
    const CertNode& c = T[v];
    if (c.type == 0) return cmp(cb, I.D) < 0;
    if (c.type == 1) return cmp(I.D, sIn) < 0;
    if (c.type == 2) return md(c.arg);
    if (c.type != 3) return false;
    int n = c.arg;
    if (n < 2 || n > B || !EM[n] || inn[n] || out[n]) return false;
    // in-branch: n in T, exclude every multiple and every divisor of n in EM that is undecided
    {
      BigNat oldS = sIn, oldCb = cb; vector<pair<int, BigNat>> undo; vector<int> ex;
      inn[n] = 1; sIn = add(sIn, divSmall(I.D, (uint32_t)n));
      for (int m = 2 * n; m <= B; m += n) if (EM[m] && !inn[m] && !out[m]) { ex.push_back(m); excl(m, undo); }
      for (int dd = 2; dd < n; dd++) if (n % dd == 0 && EM[dd] && !inn[dd] && !out[dd]) { ex.push_back(dd); excl(dd, undo); }
      bool ok = check(c.a);
      for (int m : ex) out[m] = 0;
      inn[n] = 0; sIn = oldS; cb = oldCb;
      if (!ok) return false;
    }
    {
      BigNat oldCb = cb; vector<pair<int, BigNat>> undo;
      excl(n, undo);
      bool ok = check(c.b);
      out[n] = 0; cb = oldCb;
      return ok;
    }
  }
};

// ------------------------------------------------------------------------------------------
static string fracDec(BigNat num, const BigNat& den, int digits) {  // num/den < 10, truncated
  int ip = 0; while (cmp(num, den) >= 0) { num = sub(num, den); ip++; }
  string r = to_string(ip) + ".";
  for (int k = 0; k < digits; k++) { num = mulSmall(num, 10); int dg = 0; while (cmp(num, den) >= 0) { num = sub(num, den); dg++; } r += char('0' + dg); }
  return r;
}
static string nowUTC() { time_t t = time(nullptr); char buf[64]; strftime(buf, sizeof buf, "%Y-%m-%d %H:%M:%S UTC", gmtime(&t)); return buf; }

static bool verifySolution(const vector<int>& T, bool print) {
  bool ok = !T.empty();
  vector<int> s = T; sort(s.begin(), s.end());
  for (size_t i = 0; i < s.size(); i++) {
    if (s[i] < 2) ok = false;
    if (i && s[i] == s[i - 1]) ok = false;
    for (size_t j = 0; j < i; j++) if (s[i] % s[j] == 0) ok = false;
  }
  // L = lcm(T)
  BigNat L(1);
  { vector<int> mx(s.back() + 1, 0);
    for (int n : s) { int m = n; for (int p = 2; p <= m; p++) { int k = 0; while (m % p == 0) { m /= p; k++; } mx[p] = max(mx[p], k); } }
    for (int p = 2; p <= s.back(); p++) for (int j = 0; j < mx[p]; j++) L = mulSmall(L, (uint32_t)p); }
  BigNat num; for (int n : s) { uint32_t r; num = add(num, divSmall(L, (uint32_t)n, &r)); if (r) ok = false; }
  bool one = cmp(num, L) == 0;
  if (print) {
    printf("T (%zu elements):\n", s.size());
    for (size_t i = 0; i < s.size(); i++) printf("  %d = %s%s", s[i], factorStr(s[i]).c_str(), (i % 6 == 5 || i + 1 == s.size()) ? "\n" : "");
    printf("L = lcm(T) = %s\n", toDec(L).c_str());
    printf("sum_{n in T} L/n = %s\n", toDec(num).c_str());
    printf("distinct, all >= 2, no element divides another: %s\n", ok ? "yes" : "NO");
    printf("sum_{n in T} 1/n = 1 exactly: %s\n", one ? "yes" : "NO");
  }
  return ok && one;
}

// ------------------------------------------------------------------------------------------
// Lean output
// ------------------------------------------------------------------------------------------
static void writeTrie(FILE* f, const vector<string>& leaves, int depth, int key, int level) {
  // LSB-first binary trie: at level l the bit l of the key selects the branch
  if (level == depth) { fprintf(f, "(.l %s)", key < (int)leaves.size() ? leaves[key].c_str() : "default"); return; }
  fprintf(f, "(.n ");
  writeTrie(f, leaves, depth, key, level + 1);
  fprintf(f, " ");
  writeTrie(f, leaves, depth, key | (1 << level), level + 1);
  fprintf(f, ")");
}

static void writeLean(const string& dir, const Instance& I, const vector<CertNode>& T, int root, int nFiles, size_t subSize) {
  int B = I.B;
  string ns = "SemiprimeEgypt.Prim.C" + to_string(B);
  // --- data file
  {
    string path = dir + "/PrimData" + to_string(B) + ".lean";
    FILE* f = fopen(path.c_str(), "w"); if (!f) { perror(path.c_str()); exit(1); }
    fprintf(f, "/-\nGenerated by primitive_egypt.cpp.  Do not edit.\nData for the bound B = %d: the universe U_B (non-prime-powers in [2, B]), D = lcm(U_B),\n"
               "the primes, and a chain cover (%zu chains) with exact weights.\n-/\nimport SemiprimeEgypt.PrimCheck\n\nnamespace %s\n\nopen SemiprimeEgypt.Prim\n\n",
            B, I.chains.size(), ns.c_str());
    vector<int> pr; for (int p : I.primes) pr.push_back(p);
    int nc = (int)I.chains.size();
    int dC = 0; while ((1 << dC) < nc) dC++;
    int dE = 0; while ((1 << dE) < B + 1) dE++;
    fprintf(f, "/-- Chains (by index): (elements, bit mask of the elements, weight). -/\ndef chainTr : Tr (List ℕ × ℕ × ℕ) :=\n  ");
    vector<string> cl;
    for (int c = 0; c < nc; c++) {
      vector<int> ns2; for (int e : I.chains[c]) ns2.push_back(I.U[e]);
      string el = "["; for (size_t k = 0; k < ns2.size(); k++) el += (k ? ", " : "") + to_string(ns2[k]); el += "]";
      cl.push_back("(" + el + ", " + toDec(bitmask(ns2)) + ", " + toDec(I.cy[c]) + ")");
    }
    writeTrie(f, cl, dC, 0, 0); fprintf(f, "\n\n");
    fprintf(f, "/-- For each n: the chains containing n, as (index, bit mask, weight). -/\ndef chainsOfTr : Tr (List (ℕ × ℕ × ℕ)) :=\n  ");
    vector<string> co(B + 1, "[]");
    vector<string> cmaskS(nc), cwS(nc);
    for (int c = 0; c < nc; c++) { vector<int> ns2; for (int e : I.chains[c]) ns2.push_back(I.U[e]); cmaskS[c] = toDec(bitmask(ns2)); cwS[c] = toDec(I.cy[c]); }
    for (int n = 0; n <= B; n++) if (n >= 2 && I.uidx[n] >= 0) {
      string s = "[";
      for (size_t k = 0; k < I.chainsOf[I.uidx[n]].size(); k++) { int c = I.chainsOf[I.uidx[n]][k]; s += (k ? ", " : "") + string("(") + to_string(c) + ", " + cmaskS[c] + ", " + cwS[c] + ")"; }
      co[n] = s + "]";
    }
    writeTrie(f, co, dE, 0, 0); fprintf(f, "\n\n");
    fprintf(f, "/-- The data for B = %d. -/\ndef data : Data where\n", B);
    fprintf(f, "  Bd := %d\n  D := %s\n  EM := %s\n  PM := %s\n  PL := [", B, toDec(I.D).c_str(), toDec(bitmask(I.U)).c_str(), toDec(bitmask(pr)).c_str());
    for (size_t i = 0; i < pr.size(); i++) fprintf(f, "%s%d", i ? ", " : "", pr[i]);
    fprintf(f, "]\n  NC := %d\n  chains := chainTr\n  chainsOf := chainsOfTr\n  cb0 := %s\n\nend %s\n", nc, toDec(I.cb0).c_str(), ns.c_str());
    fclose(f);
  }
  // --- certificate: skeleton (top part) + subtrees, each subtree checked by its own theorem
  size_t N = T.size();
  vector<size_t> sz(N, 1);
  for (size_t v = 0; v < N; v++) if (T[v].type == 3) sz[v] = 1 + sz[T[v].a] + sz[T[v].b];
  vector<char> skel(N, 0), subroot(N, 0);
  {
    vector<int> st = {root};
    while (!st.empty()) {
      int v = st.back(); st.pop_back();
      if (T[v].type == 3 && sz[v] > subSize) { skel[v] = 1; st.push_back(T[v].a); st.push_back(T[v].b); }
      else if (T[v].type == 3) subroot[v] = 1;
    }
    if (!skel[root] && T[root].type != 3) subroot[root] = 1;
  }
  auto leafStr = [&](int v) -> string {
    if (T[v].type == 0) return ".lo";
    if (T[v].type == 1) return ".hi";
    return "(.md " + to_string(T[v].arg) + ")";
  };
  // certificate definitions in post-order
  vector<string> S(N), defs; int cnt = 0;
  for (size_t v = 0; v < N; v++) {
    const CertNode& c = T[v]; string s;
    if (c.type <= 2) s = leafStr((int)v);
    else if (skel[v]) {
      string sa = skel[c.a] || subroot[c.a] ? "t" + to_string(c.a) : S[c.a];
      string sb = skel[c.b] || subroot[c.b] ? "t" + to_string(c.b) : S[c.b];
      defs.push_back("def t" + to_string(v) + " : Cert := .br " + to_string(c.arg) + " " + sa + " " + sb + "\n");
      s = "t" + to_string(v);
    } else {
      s = "(.br " + to_string(c.arg) + " " + S[c.a] + " " + S[c.b] + ")";
      S[c.a].clear(); S[c.a].shrink_to_fit(); S[c.b].clear(); S[c.b].shrink_to_fit();
      if (subroot[v]) { defs.push_back("def t" + to_string(v) + " : Cert := " + s + "\n"); s = "t" + to_string(v); }
      else if (s.size() > 1500) { defs.push_back("def k" + to_string(cnt) + " : Cert := " + s + "\n"); s = "k" + to_string(cnt); cnt++; }
    }
    S[v] = s;
  }
  defs.push_back("/-- The certificate for B = " + to_string(B) + " (" + to_string(N) + " nodes). -/\ndef cert : Cert := " + S[root] + "\n");
  int nCertFiles = max(1, (int)((defs.size() + 1999) / 2000));
  size_t per = (defs.size() + nCertFiles - 1) / nCertFiles;
  for (int fi = 0; fi < nCertFiles; fi++) {
    string path = dir + "/PrimCert" + to_string(B) + "_" + to_string(fi) + ".lean";
    FILE* f = fopen(path.c_str(), "w"); if (!f) { perror(path.c_str()); exit(1); }
    fprintf(f, "/- Generated by primitive_egypt.cpp.  Do not edit.  Certificate part %d/%d. -/\n", fi + 1, nCertFiles);
    if (fi == 0) fprintf(f, "import SemiprimeEgypt.PrimData%d\n", B); else fprintf(f, "import SemiprimeEgypt.PrimCert%d_%d\n", B, fi - 1);
    fprintf(f, "\nnamespace %s\n\nopen SemiprimeEgypt.Prim\n\n", ns.c_str());
    for (size_t k = fi * per; k < min(defs.size(), (fi + 1) * per); k++) fprintf(f, "%s\n", defs[k].c_str());
    fprintf(f, "end %s\n", ns.c_str());
    fclose(f);
  }
  string lastCert = "SemiprimeEgypt.PrimCert" + to_string(B) + "_" + to_string(nCertFiles - 1);
  // states along the skeleton
  vector<int> skelNodes, subs;
  {
    string path = dir + "/PrimState" + to_string(B) + ".lean";
    FILE* f = fopen(path.c_str(), "w");
    fprintf(f, "/- Generated by primitive_egypt.cpp.  Do not edit.  The states at the top of the certificate. -/\nimport %s\n\nnamespace %s\n\nopen SemiprimeEgypt.Prim\n\n",
            lastCert.c_str(), ns.c_str());
    fprintf(f, "def S%d : St := st0 data\n", root);
    vector<int> st = {root};
    while (!st.empty()) {
      int v = st.back(); st.pop_back();
      if (skel[v]) {
        skelNodes.push_back(v);
        fprintf(f, "def S%d : St := inStep data %d S%d\n", T[v].a, T[v].arg, v);
        fprintf(f, "def S%d : St := excl data S%d %d\n", T[v].b, v, T[v].arg);
        st.push_back(T[v].b); st.push_back(T[v].a);
      } else if (subroot[v]) subs.push_back(v);
    }
    fprintf(f, "\nend %s\n", ns.c_str());
    fclose(f);
  }
  // subtree theorems, balanced over nFiles files
  vector<vector<int>> bins(nFiles); vector<size_t> load(nFiles, 0);
  { vector<int> order = subs; sort(order.begin(), order.end(), [&](int x, int y) { return sz[x] > sz[y]; });
    for (int v : order) { int bi = (int)(min_element(load.begin(), load.end()) - load.begin()); bins[bi].push_back(v); load[bi] += sz[v]; } }
  for (int fi = 0; fi < nFiles; fi++) {
    string path = dir + "/PrimSub" + to_string(B) + "_" + to_string(fi) + ".lean";
    FILE* f = fopen(path.c_str(), "w");
    fprintf(f, "/- Generated by primitive_egypt.cpp.  Do not edit.  Kernel checks of %zu subtrees (%zu nodes). -/\nimport SemiprimeEgypt.PrimState%d\n\nnamespace %s\n\nopen SemiprimeEgypt.Prim\n\n",
            bins[fi].size(), load[fi], B, ns.c_str());
    for (int v : bins[fi]) fprintf(f, "theorem ok%d : check data t%d S%d = true := by decide +kernel\n\n", v, v, v);
    fprintf(f, "end %s\n", ns.c_str());
    fclose(f);
  }
  // root: skeleton theorems bottom-up
  {
    string path = dir + "/PrimRoot" + to_string(B) + ".lean";
    FILE* f = fopen(path.c_str(), "w");
    fprintf(f, "/- Generated by primitive_egypt.cpp.  Do not edit.  Assembly of the subtree checks. -/\n");
    for (int fi = 0; fi < nFiles; fi++) fprintf(f, "import SemiprimeEgypt.PrimSub%d_%d\n", B, fi);
    fprintf(f, "\nnamespace %s\n\nopen SemiprimeEgypt.Prim\n\n", ns.c_str());
    auto proofOf = [&](int v) -> string {
      if (skel[v]) return "sk" + to_string(v);
      if (subroot[v]) return "ok" + to_string(v);
      return "(by decide +kernel)";
    };
    auto certOf = [&](int v) -> string { return (skel[v] || subroot[v]) ? "t" + to_string(v) : leafStr(v); };
    for (int k = (int)skelNodes.size() - 1; k >= 0; k--) {
      int v = skelNodes[k]; const CertNode& c = T[v];
      fprintf(f, "theorem sk%d : check data t%d S%d = true :=\n  check_br_of (d := data) (n := %d) (c1 := %s) (c2 := %s) (s := S%d)\n    (by decide +kernel) %s %s\n\n",
              v, v, v, c.arg, certOf(c.a).c_str(), certOf(c.b).c_str(), v, proofOf(c.a).c_str(), proofOf(c.b).c_str());
    }
    fprintf(f, "/-- The whole certificate is accepted by the checker. -/\ntheorem cert_ok : check data cert (st0 data) = true := %s\n\nend %s\n",
            skel[root] ? ("sk" + to_string(root)).c_str() : ("ok" + to_string(root)).c_str(), ns.c_str());
    fclose(f);
  }
  printf("Lean files: %d certificate parts, %zu skeleton nodes, %zu subtree theorems in %d files\n", nCertFiles, skelNodes.size(), subs.size(), nFiles);
}

// ------------------------------------------------------------------------------------------
static void runCert(int Bc, const string& certDir, int nFiles) {
  auto t1 = chrono::steady_clock::now();
  Instance IC(Bc);
  printf("|U_%d| = %zu, D = lcm(U_%d) has %zu bits, chains: %zu\n", Bc, IC.U.size(), Bc, IC.D.d.size() * 32, IC.chains.size());
  Solver S(IC); S.record = true; S.countAll = true;
  int root = S.dfs();
  size_t leaves = 0, sols = 0; for (auto& c : S.tree) { if (c.type <= 2) leaves++; if (c.type == 4) sols++; }
  printf("search tree: %zu nodes, %zu leaves, %zu solution leaves (%lld ms)\n", S.tree.size(), leaves, sols,
         (long long)chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - t1).count());
  if (sols) { printf("solutions exist inside U_%d; no certificate\n", Bc); return; }
  TreeChecker C(IC, S.tree);
  bool cok = C.check(root);
  printf("independent re-check with the semantics of the Lean checker: %s (%llu nodes)\n", cok ? "accepted" : "REJECTED", (unsigned long long)C.checked);
  if (!cok) exit(1);
  if (!certDir.empty()) { writeLean(certDir, IC, S.tree, root, nFiles, subSizeG); printf("Lean data and certificate written to %s\n", certDir.c_str()); }
}

// Lagrangian chain cover for the threshold A: weights 1/n - 1/A on the candidates n < A
static void runLag(int A, const string& dir) {
  Instance I(A - 1);
  BigNat D(1);  // lcm(U_{A-1} ∪ {A})
  for (int p = 2; p <= A; p++) if (isPrime(p)) {
    int mx = 0; vector<int> all = I.U; all.push_back(A);
    for (int m0 : all) { int k = 0, m = m0; while (m % p == 0) { m /= p; k++; } mx = max(mx, k); }
    for (int j = 0; j < mx; j++) D = mulSmall(D, (uint32_t)p);
  }
  int n = (int)I.U.size();
  vector<u64> vk(n); vector<BigNat> target(n);
  BigNat DA = divSmall(D, (uint32_t)A);
  for (int i = 0; i < n; i++) {
    u64 num = (u64)(A - I.U[i]), den = (u64)I.U[i] * A;          // K * (A - n) / (n A), rounded up
    vk[i] = (u64)(((unsigned __int128)KSCALE * num + den - 1) / den);
    target[i] = sub(divSmall(D, (uint32_t)I.U[i]), DA);
  }
  I.chains.clear(); I.cy.clear(); I.cb0 = BigNat();
  // rescale: the chain weights are computed relative to D
  I.D = D;
  I.buildChains(vk, target);
  BigNat W = I.cb0;
  printf("Lagrangian cover for A = %d: %zu candidates below A, %zu chains, D has %zu bits\n", A, I.U.size(), I.chains.size(), D.d.size() * 32);
  printf("W/D = %s...\n", fracDec(W, D, 12).c_str());
  if (!dir.empty()) {
    string path = dir + "/PrimLag" + to_string(A) + ".lean";
    FILE* f = fopen(path.c_str(), "w");
    fprintf(f, "/- Generated by primitive_egypt.cpp (lag %d).  Do not edit.  Chain cover for the Lagrangian bound. -/\n"
               "import SemiprimeEgypt.PrimCard\n\nnamespace SemiprimeEgypt.Prim\n\n/-- Chain cover of the weights `D/n - D/%d`, `n < %d`. -/\ndef lag%d : LData where\n  A := %d\n  D := %s\n  PL := [",
            A, A, A, A, A, toDec(D).c_str());
    bool first = true; for (int p = 2; p < A; p++) if (isPrime(p)) { fprintf(f, "%s%d", first ? "" : ", ", p); first = false; }
    fprintf(f, "]\n  chains := [");
    for (size_t c = 0; c < I.chains.size(); c++) {
      fprintf(f, "%s\n    ([", c ? "," : "");
      for (size_t k = 0; k < I.chains[c].size(); k++) fprintf(f, "%s%d", k ? ", " : "", I.U[I.chains[c][k]]);
      fprintf(f, "], %s)", toDec(I.cy[c]).c_str());
    }
    fprintf(f, "]\n\n/-- `W = %s`. -/\ntheorem lag%d_W : lag%d.W = %s := by decide +kernel\n\nend SemiprimeEgypt.Prim\n", toDec(W).c_str(), A, A, toDec(W).c_str());
    fclose(f);
    printf("written %s\n", path.c_str());
  }
}

// Q2: the lower bound |T| >= 39 (Lagrangian chain bound + Q1) and the upper bound 47
static void runQ2() {
  printf("=== Q2: the least possible |T| ===\n\n");
  // the squarefree semiprimes in increasing order
  vector<int> sp;
  for (int n = 6; (int)sp.size() < 60; n++) {
    int a = 0; for (int p = 2; p * p <= n; p++) if (n % p == 0) { a = p; break; }
    if (a && n / a != a && (n / a) % a && isPrime(n / a)) sp.push_back(n);
  }
  int A = sp[37];  // a_38 = 129
  printf("threshold A = a_38 = %d (the 38th squarefree semiprime)\n", A);
  Instance I(A - 1);
  BigNat D(1);
  for (int p = 2; p <= A; p++) if (isPrime(p)) {
    int mx = 0; vector<int> all = I.U; all.push_back(A);
    for (int m0 : all) { int k = 0, m = m0; while (m % p == 0) { m /= p; k++; } mx = max(mx, k); }
    for (int j = 0; j < mx; j++) D = mulSmall(D, (uint32_t)p);
  }
  int n = (int)I.U.size();
  vector<u64> vk(n); vector<BigNat> target(n);
  BigNat DA = divSmall(D, (uint32_t)A);
  for (int i = 0; i < n; i++) {
    u64 num = (u64)(A - I.U[i]), den = (u64)I.U[i] * A;
    vk[i] = (u64)(((unsigned __int128)KSCALE * num + den - 1) / den);
    target[i] = sub(divSmall(D, (uint32_t)I.U[i]), DA);
  }
  I.chains.clear(); I.cy.clear(); I.cb0 = BigNat(); I.D = D;
  I.buildChains(vk, target);
  BigNat W = I.cb0;
  printf("chain cover of the weights 1/n - 1/A on the %zu candidates below A: %zu chains, W/D = %s...\n", I.U.size(), I.chains.size(), fracDec(W, D, 12).c_str());
  // For a primitive T (no prime powers) and m in T with m >= A:
  //   sum 1/n <= |T|/A + W/D - (1/A - 1/m).
  // (i)  |T| <= 37:  37/A + W/D < 1.
  // (ii) |T| = 38 and m >= 159:  38/A + W/D - (1/A - 1/159) < 1, so T ⊆ [2, 158].
  // Exact check with common denominator E = D * 159 (A | D).
  BigNat E = mulSmall(D, 159);
  BigNat lhs1 = add(mulSmall(mulSmall(DA, 37), 159), mulSmall(W, 159));            // (37/A + W/D) * E
  bool c1 = cmp(lhs1, E) < 0;
  BigNat lhs2 = add(add(mulSmall(mulSmall(DA, 37), 159), mulSmall(W, 159)), D);      // (38/A - 1/A + W/D + 1/159) * E
  bool c2 = cmp(lhs2, E) < 0;
  printf("(i)  37/A + W/D < 1 exactly: %s   => |T| <= 37 is impossible\n", c1 ? "yes" : "NO");
  printf("(ii) 38/A + W/D - (1/A - 1/159) < 1 exactly: %s   => |T| = 38 forces max T <= 158,\n", c2 ? "yes" : "NO");
  printf("     and no primitive solution lies in [2, 412] (Q1)\n");
  printf("=> every primitive T ⊆ {2,3,...} with sum 1 has |T| >= 39\n\n");
  // upper bound: a 47-term set of squarefree semiprimes (automatically primitive)
  vector<int> T47 = {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 85,
                     87, 91, 93, 95, 111, 115, 119, 123, 133, 143, 145, 155, 203, 219, 221, 287, 299, 391, 481,
                     1299, 2117, 16021, 31609};
  printf("--- upper bound: a 47-term example ---\n");
  bool ok = verifySolution(T47, true);
  printf("\nRESULT Q2: 39 <= min |T| <= 47 %s\n\n", (ok && c1 && c2) ? "(both bounds verified)" : "(VERIFICATION FAILED)");
}

static void runQ1(const string& certDir, int nFiles) {
  printf("=== Q1: the least possible max T ===\n\n");
  auto t0 = chrono::steady_clock::now();
  int answer = -1; vector<int> sol; u64 total = 0; int refuted = 0;
  printf("Scan: for each m in U (non-prime-powers >= 6), search U_m with m forced into T.\n");
  for (int m = 6; m <= 5000; m++) {
    if (isPrimePower(m)) continue;
    Instance I(m);
    Solver S(I);
    S.setIn(I.uidx[m]);
    S.dfs();
    total += S.nodes;
    if (S.solutions) { answer = m; sol = S.firstSolution; printf("m = %d = %s: SOLUTION (%llu nodes)\n", m, factorStr(m).c_str(), (unsigned long long)S.nodes); break; }
    refuted++;
    if (S.nodes >= 1000) printf("m = %d = %s: no solution with max T = m (%llu nodes)\n", m, factorStr(m).c_str(), (unsigned long long)S.nodes);
  }
  printf("(the other values of m are refuted with fewer than 1000 nodes each)\n");
  printf("refuted m: %d, total search nodes %llu, scan time %lld ms\n\n", refuted, (unsigned long long)total,
         (long long)chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - t0).count());
  if (answer < 0) { printf("no solution found\n"); return; }
  printf("--- exact verification of the solution ---\n");
  bool ok = verifySolution(sol, true);
  printf("max T = %d\n\n", *max_element(sol.begin(), sol.end()));
  if (!ok) { printf("VERIFICATION FAILED\n"); exit(1); }

  int Bc = answer - 1;
  printf("--- certificate: no solution inside U_%d (nothing forced) ---\n", Bc);
  auto t1 = chrono::steady_clock::now();
  Instance IC(Bc);
  printf("|U_%d| = %zu, D = lcm(U_%d) has %zu bits, chains: %zu\n", Bc, IC.U.size(), Bc, IC.D.d.size() * 32, IC.chains.size());
  Solver S(IC); S.record = true; S.countAll = true;
  int root = S.dfs();
  size_t leaves = 0, sols = 0; for (auto& c : S.tree) { if (c.type <= 2) leaves++; if (c.type == 4) sols++; }
  printf("search tree: %zu nodes, %zu leaves, %zu solution leaves (%lld ms)\n", S.tree.size(), leaves, sols,
         (long long)chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - t1).count());
  if (sols) { printf("UNEXPECTED solution below the answer\n"); exit(1); }
  TreeChecker C(IC, S.tree);
  bool cok = C.check(root);
  printf("independent re-check with the semantics of the Lean checker: %s (%llu nodes)\n", cok ? "accepted" : "REJECTED", (unsigned long long)C.checked);
  if (!cok) exit(1);
  if (!certDir.empty()) { writeLean(certDir, IC, S.tree, root, nFiles, subSizeG); printf("Lean data and certificate written to %s\n", certDir.c_str()); }
  printf("\nRESULT Q1: min max T = %d = %s\n\n", answer, factorStr(answer).c_str());
}

int main(int argc, char** argv) {
  string mode = argc > 1 ? argv[1] : "q1";
  string certDir; int nFiles = 16;
  for (int i = 2; i < argc; i++) {
    if (!strcmp(argv[i], "--cert") && i + 1 < argc) certDir = argv[++i];
    else if (!strcmp(argv[i], "--files") && i + 1 < argc) nFiles = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--sub") && i + 1 < argc) subSizeG = (size_t)atoll(argv[++i]);
  }
  printf("start: %s\n\n", nowUTC().c_str());
  auto t0 = chrono::steady_clock::now();
  if (mode == "q1") runQ1(certDir, nFiles);
  else if (mode == "cert" && argc > 2) runCert(atoi(argv[2]), certDir, nFiles);
  else if (mode == "lag" && argc > 2) runLag(atoi(argv[2]), certDir);
  else if (mode == "q2") runQ2();
  else if (mode == "all") { runQ1(certDir, nFiles); runQ2(); }
  printf("end: %s\nelapsed: %lld ms\n", nowUTC().c_str(),
         (long long)chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - t0).count());
  return 0;
}
