// q2exact.cpp -- exact search for Problem 2 (primitive Egyptian fractions of 1), one size at a time.
//
//   Find every finite T subset {2,3,4,...} with  sum_{n in T} 1/n = 1,  no element of T dividing
//   another, and |T| = K.   There is NO bound on the size of the elements.
//
// Method (README.md, sections 1-2):
//   * No prime power lies in T (Lemma 1).
//   * Lagrangian bound with lambda = 1/A: sum_{n in T, n >= A} (lambda - 1/n) <= sigma := K/A + W - 1,
//     W = max weight of an antichain of non-prime-powers below A for weights 1/n - 1/A (computed as an
//     exactly verified chain cover).  Hence at most hmax elements of T exceed Y (Lemmas 2, 3).
//   * Core C = T cap [2, Y]: depth-first search in increasing order with a value window and exact
//     p-adic residues.  Each prime p whose residue is nonzero ("unsatisfied") must divide an element
//     of H = T cap (Y, oo); two unsatisfied primes p, q can share an element only if no core element
//     divides p^e q^f, so the unsatisfied primes need at least chi(U) elements of H (Lemma 4).
//     Pruning rules (P1)-(P6) of README section 2: value bounds, chi(U), the clique rule (Lemma 5), the
//     monotone loop break (P5) and the clique test made in the parent (P6).
//   * h = 1: a completion needs delta = 1/b exactly (b = prod_{p in U} p^{e_p}); a fixed-point test
//     refutes the core without GMP when S - sUp > floor(S/b) + 1 (S = 2^96).
//   * Completion: every H with |H| = h = K - |C| and sum_H 1/x = 1 - sum_C exactly, found by exact
//     Egyptian-fraction algorithms (compl.h, or ind2.h for h = 2 with Q2_H2=ind).  Every reported
//     solution is re-verified exactly (sum and primitivity).
//
// Exact arithmetic only (64/128-bit integers, fixed point with directed rounding, GMP integers).
// No floating-point type is used.
//
// Build:  g++ -O2 -march=native -pthread -o q2exact q2exact.cpp /usr/lib/x86_64-linux-gnu/libgmp.so.10
// Run:    ./q2exact K A [threads] [splitDepth] [dumpfile|-] [nocomplete|deferH|all] [ticketLo] [ticketHi]
//         deferH: cores with h >= H are only written to the dump (a name ending in .gz is gzip-compressed);
//         [ticketLo, ticketHi): only the split subtrees with these indices (for resuming / splitting a run).
// Environment: Q2_H2=ind (h = 2 inline with ind2.h), Q2_H2SAMPLE=file (hash-selected ~1/64 of the h = 2
//         cores, for cross-checks), Q2_NOBREAK=1 (disable rule P5, for comparisons).
#include <bits/stdc++.h>
#include "gmpz.h"
#include "compl.h"
#include "ind2.h"
using namespace std;
typedef unsigned long long u64; typedef long long i64; typedef __int128 i128; typedef unsigned __int128 u128;

static int K; static u64 A, Y = 0; static int HMAX;
static const u128 S = (u128)1 << 96;
static u128 lamLow, lamUp, Wup = 0; static i128 sigmaUp;

static u64 inv_mod(u64 a, u64 m) { i128 t = 0, nt = 1, r = m, nr = a % m;
  while (nr) { i128 q = r / nr, tmp = t - q * nt; t = nt; nt = tmp; tmp = r - q * nr; r = nr; nr = tmp; }
  if (t < 0) t += m; return (u64)t; }
static bool isPrimePowerSmall(u64 n) { for (u64 p = 2; p * p <= n; p++) if (n % p == 0) { while (n % p == 0) n /= p; return n == 1; } return true; }
static vector<pair<u64,int>> factorSmall(u64 n) { vector<pair<u64,int>> f; for (u64 p = 2; p * p <= n; p++) if (n % p == 0) { int k = 0; while (n % p == 0) { n /= p; k++; } f.push_back({p, k}); } if (n > 1) f.push_back({n, 1}); return f; }

// ---------------- Lagrangian constant: verified chain cover ----------------
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
// Upper bound (scaled by S) for max_{antichain Q of non-prime-powers < A} sum_{n in Q} (1/n - 1/A).
// The flow gives weighted chains y_c with sum_{c ∋ n} y_c >= ceil(S/n) - floor(S/A) for every n
// (checked exactly below); an antichain meets each chain at most once, so the antichain weight is
// at most sum_c y_c.
static u128 chainCoverBound(size_t* nChains) {
  vector<u64> P; for (u64 n = 6; n < A; n++) if (!isPrimePowerSmall(n)) P.push_back(n);
  int m = P.size(); vector<i128> w(m); for (int i = 0; i < m; i++) w[i] = (i128)((S + P[i] - 1) / P[i]) - (i128)(S / A);
  const int SH = 40; vector<u64> wk(m); for (int i = 0; i < m; i++) wk[i] = (u64)(w[i] >> SH) + 1;
  Dinic g(2 * m + 2); int s = 2 * m, t = 2 * m + 1;
  for (int i = 0; i < m; i++) { g.addEdge(s, i, wk[i]); g.addEdge(m + i, t, wk[i]); }
  for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) if (P[j] % P[i] == 0) g.addEdge(i, m + j, ~0ULL >> 2);
  g.run(s, t);
  vector<vector<pair<int,u64>>> out(m);
  for (int i = 0; i < m; i++) for (auto& e : g.G[i]) if (e.to >= m && e.to < 2 * m) { u64 f = g.G[e.to][e.rev].cap; if (f) out[i].push_back({e.to - m, f}); }
  vector<vector<pair<int,u64>>> arriving(m); vector<vector<int>> pref; vector<vector<int>> chains; vector<u64> amount;
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
  vector<u128> cov(m, 0); u128 W = 0;
  for (size_t c = 0; c < chains.size(); c++) { u128 y = (u128)amount[c] << SH; W += y; for (int e : chains[c]) cov[e] += y;
    for (size_t k = 1; k < chains[c].size(); k++) if (P[chains[c][k]] % P[chains[c][k - 1]]) { fprintf(stderr, "not a chain\n"); exit(1); } }
  for (int e = 0; e < m; e++) if ((i128)cov[e] < w[e]) { fprintf(stderr, "chain cover fails\n"); exit(1); }
  *nChains = chains.size(); return W;
}

// ---------------- core universe ----------------
static vector<u64> U; static vector<u128> rLow, rUp; static vector<vector<int>> comp;
static vector<vector<pair<int,u64>>> res;
static vector<u64> pr, Mq; static vector<int> Eq, lastIdx; static unordered_map<u64,int> pid;
static u128 lowTarget[64];
static int splitDepth = 34; static bool doComplete = true; static int deferFromH = 99; /* cores with h >= deferFromH are only dumped */ static vector<int> smallP;   // indices (into pr) of primes <= 31
static vector<unsigned> smallMask;   // smallMask[k]: primes <= 31 dividing U[k] (bits over smallP)
static vector<int> smallIdx;         // smallIdx[qi] = position of pr[qi] in smallP, or -1
static bool useBreak = true;
static bool h2ind = false;            // Q2_H2=ind: complete h = 2 cores inline with ind2.h instead of compl.h
static FILE* h2SampleF = nullptr;      // Q2_H2SAMPLE=file: also write ~1/64 of the h = 2 cores (hash-selected) for cross-checks   // rule (P5); Q2_NOBREAK=1 disables it (for comparisons)
static atomic<u64> nextTicket(0); static u64 ticketLo = 0, ticketHi = ~0ULL;   // process split subtrees with index in [ticketLo, ticketHi)
struct Searcher; static vector<Searcher*> allSearchers;
static mutex outMu; static FILE* dumpF = nullptr;
static vector<string> allSolutions;

static string nowJSTs() { time_t t = time(nullptr) + 9 * 3600; char b[64]; strftime(b, sizeof b, "%Y-%m-%dT%H:%M:%S+09:00", gmtime(&t)); return b; }
struct Searcher {
  vector<int> cur, blk; vector<u64> R; vector<char> inSet; vector<pair<u64,int>> ufBuf;
  Completer cp;
  ind2::Counters h2cnt; u64 h1Refuted = 0, breaks = 0, cliqueSkips = 0, nodes = 0, qualSets = 0, coresByH[16] = {0}, rejU = 0, splitSeen = 0, myTicket = 0, cliquePruned = 0;
  atomic<u64> inProgress{0};   // index of the split subtree being processed (all smaller indices of this thread are done)
  Searcher() { blk.assign(U.size(), 0); R.assign(pr.size(), 0); inSet.assign(Y + 1, 0); cp.Y = Y;
    cp.onSolution = [](const string& s) { lock_guard<mutex> g(outMu); printf("%s\n", s.c_str()); fflush(stdout); allSolutions.push_back(s); };
    myTicket = nextTicket.fetch_add(1); }
  // min(chi(U), cap + 1) for the conflict graph of Lemma 4 (p, q conflict iff a core element divides p^e_p q^e_q)
  int chromaticU(const vector<pair<u64,int>>& Ul, int cap) {
    int n = Ul.size(); if (n == 0) return 0;
    if (n > 64) { fprintf(stderr, "chromaticU: more than 64 primes\n"); exit(9); }
    u64 adj[64] = {0}; bool anyEdge = false;
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) {
      u64 p = Ul[i].first, q = Ul[j].first, pe = 1, qe = 1; for (int t = 0; t < Ul[i].second; t++) pe *= p; for (int t = 0; t < Ul[j].second; t++) qe *= q;
      bool c = false;
      for (u64 x = p; x <= pe && x <= Y && !c; x *= p) for (u64 y = q; y <= qe && x * y <= Y; y *= q) if (inSet[x * y]) { c = true; break; }
      if (c) { adj[i] |= 1ULL << j; adj[j] |= 1ULL << i; anyEdge = true; }
    }
    if (!anyEdge) return 1;
    int order[64]; for (int i = 0; i < n; i++) order[i] = i;
    sort(order, order + n, [&](int x, int y) { return __builtin_popcountll(adj[x]) > __builtin_popcountll(adj[y]); });
    for (int k = 2; k <= cap; k++) {   // is the graph k-colourable?  colour classes as bit masks
      u64 cls[8] = {0};
      struct Rec { static bool go(int i, int used, int k, int n, const int* order, const u64* adj, u64* cls) {
        if (i == n) return true; int v = order[i];
        for (int c = 0; c < k && c <= used; c++) if (!(adj[v] & cls[c])) {
          cls[c] |= 1ULL << v; if (go(i + 1, max(used, c + 1), k, n, order, adj, cls)) return true; cls[c] &= ~(1ULL << v); }
        return false; } };
      if (Rec::go(0, 0, k, n, order, adj, cls)) return k;
    }
    return cap + 1;
  }
  u64 nzw[8] = {0};   // bit qi set iff R[qi] != 0
  void setR(int qi, u64 v) { R[qi] = v; if (v) nzw[qi >> 6] |= 1ULL << (qi & 63); else nzw[qi >> 6] &= ~(1ULL << (qi & 63)); }
  // primes with nonzero residue whose multiples all lie before index finalBefore, with e_p
  void unsatisfiedInto(int finalBefore, vector<pair<u64,int>>& Ul) {
    Ul.clear();
    for (int w = 0; w < 8; w++) for (u64 m = nzw[w]; m; m &= m - 1) { int qi = (w << 6) + __builtin_ctzll(m);
      if (lastIdx[qi] >= finalBefore) continue;
      u64 r = R[qi]; int v = 0; while (r % pr[qi] == 0) { r /= pr[qi]; v++; } Ul.push_back({pr[qi], Eq[qi] - v}); }
  }
  vector<pair<u64,int>> unsatisfied(int finalBefore) { vector<pair<u64,int>> Ul; unsatisfiedInto(finalBefore, Ul); return Ul; }
  void leafCheck(int cnt, u128 sUp) {
    qualSets++;
    int h = K - cnt;
    vector<pair<u64,int>> Ul = unsatisfied(INT_MAX);
    if (Ul.empty() != (h == 0)) return;
    if (h > 0 && chromaticU(Ul, h) > h) { rejU++; return; }
    if (h == 1 && sUp < S) {
      // h = 1 needs delta = 1/b exactly (x = b/a with gcd(a,b) = 1), b = prod_{p in U} p^{e_p} (Lemma 4).
      // sUp >= S(1 - delta) gives S - sUp <= S*delta; so S - sUp > floor(S/b) + 1 implies delta > 1/b.
      u128 bq = 1; bool big = false;
      for (auto& u : Ul) for (int t = 0; t < u.second && !big; t++) { if (bq > S / u.first) big = true; else bq *= u.first; }
      u128 sb = big ? 0 : S / bq;
      if (S - sUp > sb + 1) { h1Refuted++; return; }
    }
    vector<u64> C; for (int x : cur) C.push_back(U[x]);
    Z num(0), den(1);
    for (u64 n : C) { Z nn(n); num = num * nn + den; den = den * nn; Z g = gcd(num, den); num = divexact(num, g); den = divexact(den, g); }
    Z a = den - num, b = den;
    cp.core = C; cp.coreSet = set<u64>(C.begin(), C.end());
    if (h == 0) { if (a.sgn() == 0) { vector<Z> none; cp.verify(none); } return; }
    if (a.sgn() <= 0) return;
    if (cmp(a * (Y + 1), b * (unsigned long)h) > 0) return;               // sum_H <= h/(Y+1)
    Z bb(1); for (auto& u : Ul) for (int t = 0; t < u.second; t++) bb = bb * u.first;
    if (cmp(bb, b) != 0) { fprintf(stderr, "residue/denominator mismatch\n"); exit(8); }
    coresByH[h]++;
    bool defer = (h >= deferFromH);
    if (dumpF && (defer || deferFromH == 99)) { lock_guard<mutex> g(outMu); for (u64 n : C) fprintf(dumpF, "%llu ", (unsigned long long)n); fprintf(dumpF, "| h=%d %s/%s\n", h, a.str().c_str(), b.str().c_str()); }
    if (!doComplete || defer) return;
    if (h == 2 && h2ind) {
      if (h2SampleF) { u64 hs = 1469598103934665603ULL; for (u64 n : C) { hs ^= n; hs *= 1099511628211ULL; }
        if ((hs >> 20) % 64 == 0) { lock_guard<mutex> g(outMu); for (u64 n : C) fprintf(h2SampleF, "%llu ", (unsigned long long)n); fprintf(h2SampleF, "| h=2 %s/%s\n", a.str().c_str(), b.str().c_str()); } }
      vector<pair<u64,int>> fb(Ul.begin(), Ul.end()); vector<pair<Z,Z>> out;
      ind2::solve(a, b, fb, Z((unsigned long)Y), 200000, out, h2cnt); cp.calls++;
      for (auto& xy : out) {
        bool ok = cmpu(xy.first, Y) > 0 && !divisible(xy.second, xy.first);
        for (u64 c : C) if (ok && (divisibleU(xy.first, c) || divisibleU(xy.second, c))) ok = false;
        if (!ok) continue;
        vector<Z> H{xy.first, xy.second}; cp.verify(H);
      }
      return;
    }
    Fac bf; for (auto& u : Ul) bf.push_back({Z(u.first), u.second}); vector<Z> ch; cp.run(a, b, bf, h, Z(Y), ch);
  }
  // Clique rule.  D = primes p <= 31 with nonzero current residue, pairwise "conflicting": pq in C.
  // A later core element contains at most one prime of a conflicting pair (else it is a multiple of
  // pq), so after x more core elements at least |D| - x primes of D stay unsatisfied; they pairwise
  // need different huge elements, so h_final = K - cnt - x >= |D| - x, i.e. |D| <= K - cnt.
  // maximum clique D among the primes <= 31 with nonzero residue, "pq in C'" being the edges;
  // *members receives D as a bit mask over smallP.
  int maxCliqueSmall(unsigned* members) {
    int ids[16], n = 0;
    for (int qi = 0; qi < (int)smallP.size(); qi++) if (R[smallP[qi]]) ids[n++] = qi;
    *members = 0;
    if (n == 0) return 0;
    unsigned adj[16] = {0};
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) { u64 pq = pr[smallP[ids[a]]] * pr[smallP[ids[b]]]; if (pq <= Y && inSet[pq]) { adj[a] |= 1u << b; adj[b] |= 1u << a; } }
    int best = 0; unsigned bestSet = 0;
    function<void(unsigned,int,unsigned)> bk = [&](unsigned cand, int size, unsigned in) {
      if (!cand) { if (size > best) { best = size; bestSet = in; } return; }
      if (size + __builtin_popcount(cand) <= best) return;
      while (cand) { int v = __builtin_ctz(cand); cand &= cand - 1; bk(cand & adj[v], size + 1, in | (1u << v)); if (size + 1 + __builtin_popcount(cand) <= best) return; }
    };
    bk((1u << n) - 1, 0, 0);
    for (int a = 0; a < n; a++) if (bestSet >> a & 1) *members |= 1u << ids[a];
    return best;
  }
  void dfs(int i, int cnt, u128 sLow, u128 sUp) {
    if (myTicket >= ticketHi) return;
    if (cnt == splitDepth) { bool mine = (splitSeen == myTicket); splitSeen++; if (!mine) return; inProgress = myTicket; myTicket = nextTicket.fetch_add(1); }
    nodes++;
    if ((nodes & ((1ULL << 25) - 1)) == 0) { lock_guard<mutex> g(outMu); u64 doneBelow = ~0ULL; for (auto* o : allSearchers) doneBelow = min(doneBelow, (u64)o->inProgress); if (dumpF) fflush(dumpF); fprintf(stderr, "[%s] doneBelow=%llu thread-nodes=%llu tickets=%llu qual=%llu cores=%llu,%llu,%llu,%llu,%llu comp=%llu n1=%llu\n", nowJSTs().c_str(), (unsigned long long)doneBelow, (unsigned long long)nodes, (unsigned long long)nextTicket.load(), (unsigned long long)qualSets, (unsigned long long)coresByH[1], (unsigned long long)coresByH[2], (unsigned long long)coresByH[3], (unsigned long long)coresByH[4], (unsigned long long)coresByH[5], (unsigned long long)cp.calls, (unsigned long long)cp.n1Tried); }
    unsigned clqMask = 0; int clq = (K - cnt <= 9) ? maxCliqueSmall(&clqMask) : 0;
    if (K - cnt <= 8 && clq > K - cnt) { cliquePruned++; return; }
    // (P6) a child C' + {U[k]} still contains the clique D minus the primes of U[k] (edges are never removed
    // and only the residues of primes dividing U[k] change), so the child fails the clique rule when
    // |D \ primes(U[k])| > K - cnt - 1.  The test is made here, before the child is created.
    // Lower bound used: S = D \ primes(U[k]), extended greedily by each prime t <= 31 of U[k] whose residue
    // after adding U[k] is nonzero and which is adjacent (tq in C' + {U[k]}) to every member of S; S is a
    // clique of the child, so |S| > K - cnt - 1 refutes the child and the leaf C' + {U[k]} (chi(U) >= |S|).
    if (K - cnt - 1 > 8 || clq < K - cnt - 1) clqMask = 0;
    unsatisfiedInto(i, ufBuf);
    int hlo = ufBuf.empty() ? 0 : chromaticU(ufBuf, HMAX);
    if (hlo > HMAX) return;
    int jmax = K - hlo, jmin = max(cnt + 1, K - HMAX);
    if (jmin > jmax) return;
    // value window: for some admissible final size j, the j - cnt largest remaining reciprocals must
    // lift the sum to at least 1 - (K-j)/(Y+1)
    bool any = false; u128 acc = sUp; int taken = 0;
    for (int k = i; k < (int)U.size() && cnt + taken < jmax; k++) if (!blk[k]) {
      acc += rUp[k]; taken++; int j = cnt + taken;
      if (j >= jmin && acc >= lowTarget[K - j]) { any = true; break; }
    }
    if (!any) return;
    for (int k = i; k < (int)U.size(); k++) if (!blk[k]) {
      u128 nl = sLow + rLow[k], nu = sUp + rUp[k];
      if (nl > S) continue;
      if (useBreak) {
        // (P5) relaxed reachability of the window by k plus t >= 0 of the next unblocked elements (current
        // blocking, i.e. ignoring the multiples of U[k] that k would block).  rUp is non-increasing along U,
        // so this bound is non-increasing in k: if it fails for k it fails for every later candidate.
        bool reach = false; u128 acc = nu; int j = cnt + 1, kk = k + 1;
        while (true) {
          if (j >= K - HMAX && j <= K && acc >= lowTarget[K - j]) { reach = true; break; }
          if (j >= K) break;
          while (kk < (int)U.size() && blk[kk]) kk++;
          if (kk >= (int)U.size()) break;
          acc += rUp[kk]; kk++; j++;
        }
        if (!reach) { breaks++; break; }
      }
      if (clqMask) {
        unsigned S2 = clqMask & ~smallMask[k]; int lb = __builtin_popcount(S2);
        if (lb <= K - cnt - 1) for (auto& r : res[k]) {
          int t = smallIdx[r.first]; if (t < 0) continue;
          if ((R[r.first] + r.second) % Mq[r.first] == 0) continue;
          u64 pt = pr[r.first]; bool adjAll = true;
          for (unsigned m2 = S2; m2 && adjAll; m2 &= m2 - 1) { u64 pq = pt * pr[smallP[__builtin_ctz(m2)]]; if (!(pq == U[k] || (pq <= Y && inSet[pq]))) adjAll = false; }
          if (adjAll) { S2 |= 1u << t; lb++; }
        }
        if (lb > K - cnt - 1) { cliqueSkips++; continue; }
      }
      for (int f : comp[k]) blk[f]++; cur.push_back(k); inSet[U[k]] = 1;
      for (auto& r : res[k]) setR(r.first, (R[r.first] + r.second) % Mq[r.first]);
      int j = cnt + 1;
      if (j >= K - HMAX && j <= K && nu >= lowTarget[K - j]) leafCheck(j, nu);
      if (j < K) dfs(k + 1, j, nl, nu);
      for (auto& r : res[k]) setR(r.first, (R[r.first] + Mq[r.first] - r.second) % Mq[r.first]);
      inSet[U[k]] = 0; cur.pop_back(); for (int f : comp[k]) blk[f]--;
    }
  }
};

static string nowJST() { time_t t = time(nullptr) + 9 * 3600; char b[64]; strftime(b, sizeof b, "%Y-%m-%dT%H:%M:%S+09:00", gmtime(&t)); return b; }

int main(int argc, char** argv) {
  if (argc < 3) { fprintf(stderr, "usage: q2exact K A [threads] [splitDepth] [dumpfile|-] [nocomplete]\n"); return 1; }
  K = atoi(argv[1]); A = strtoull(argv[2], 0, 10);
  int threads = argc > 3 ? atoi(argv[3]) : 1; if (argc > 4) splitDepth = atoi(argv[4]);
  bool dumpGz = false;
  if (argc > 5 && string(argv[5]) != "-") { string fn = argv[5];
    if (fn.size() > 3 && fn.substr(fn.size() - 3) == ".gz") { dumpF = popen(("gzip -1 > '" + fn + "'").c_str(), "w"); dumpGz = true; }
    else dumpF = fopen(argv[5], "w"); }
  if (argc > 6 && string(argv[6]) == "nocomplete") doComplete = false;
  if (argc > 6 && string(argv[6]).rfind("defer", 0) == 0) deferFromH = atoi(argv[6] + 5);   // e.g. defer3
  if (argc > 7) ticketLo = strtoull(argv[7], 0, 10);
  if (argc > 8) ticketHi = strtoull(argv[8], 0, 10);
  nextTicket = ticketLo;
  if (getenv("Q2_NOBREAK")) useBreak = false;
  if (getenv("Q2_H2") && string(getenv("Q2_H2")) == "ind") h2ind = true;
  if (getenv("Q2_H2SAMPLE")) h2SampleF = fopen(getenv("Q2_H2SAMPLE"), "w");
  string t0s = nowJST(); auto t0 = chrono::steady_clock::now();
  lamLow = S / A; lamUp = (S + A - 1) / A; size_t nch = 0; Wup = chainCoverBound(&nch);
  sigmaUp = (i128)K * (i128)lamUp + (i128)Wup - (i128)S;               // >= sigma * S
  int hinf = 0; while ((i128)(hinf + 1) * (i128)lamLow <= sigmaUp) hinf++;
  { u64 y = A; while ((i128)(hinf + 1) * ((i128)lamLow - (i128)((S + y) / (y + 1))) <= sigmaUp) y++; Y = y; }
  HMAX = 0; while ((i128)(HMAX + 1) * ((i128)lamLow - (i128)((S + Y) / (Y + 1))) <= sigmaUp) HMAX++;
  for (u64 n = 6; n <= Y; n++) if (!isPrimePowerSmall(n)) U.push_back(n);
  int m = U.size(); comp.assign(m, {});
  for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++) if (U[b] % U[a] == 0) { comp[a].push_back(b); comp[b].push_back(a); }
  for (u64 n : U) { rLow.push_back(S / n); rUp.push_back((S + n - 1) / n); }
  for (int h = 0; h <= HMAX; h++) lowTarget[h] = S - (S * (u128)h) / (Y + 1) - 1;   // <= S(1 - h/(Y+1))
  set<u64> ps; for (u64 n : U) for (auto& f : factorSmall(n)) ps.insert(f.first);
  for (u64 p : ps) { pid[p] = pr.size(); pr.push_back(p); int E = 0; u64 M = 1; while (M <= Y / p) { M *= p; E++; } Mq.push_back(M); Eq.push_back(E); lastIdx.push_back(-1); }
  for (size_t qi = 0; qi < pr.size(); qi++) if (pr[qi] <= 31) smallP.push_back(qi);
  smallIdx.assign(pr.size(), -1); for (size_t t = 0; t < smallP.size(); t++) smallIdx[smallP[t]] = t;
  smallMask.assign(m, 0); for (int a = 0; a < m; a++) for (size_t t = 0; t < smallP.size(); t++) if (U[a] % pr[smallP[t]] == 0) smallMask[a] |= 1u << t;
  res.assign(m, {});
  for (int i = 0; i < m; i++) for (auto& f : factorSmall(U[i])) {
    int qi = pid[f.first]; u64 M = Mq[qi], q = f.first; int v = f.second; u64 u = U[i]; for (int t = 0; t < v; t++) u /= q;
    u64 pw = 1; for (int t = 0; t < Eq[qi] - v; t++) pw *= q;
    res[i].push_back({qi, (u64)((u128)pw * inv_mod(u % M, M) % M)}); lastIdx[qi] = i;
  }
  if (pr.size() > 512) { fprintf(stderr, "too many primes for the residue bit set\n"); return 1; }
  if (splitDepth >= K - HMAX) { fprintf(stderr, "splitDepth must be < K - hmax\n"); return 1; }
  printf("q2exact K=%d A=%llu  chains=%zu  sigma*1e12 <= %lld  hmax=%d  Y=%llu  |core universe|=%d  threads=%d splitDepth=%d tickets=[%llu,%llu)\nstart %s\n",
         K, (unsigned long long)A, nch, (long long)(sigmaUp / (i128)(S / 1000000000000ULL)), HMAX, (unsigned long long)Y, m, threads, splitDepth, (unsigned long long)ticketLo, (unsigned long long)ticketHi, t0s.c_str());
  fflush(stdout);
  vector<Searcher*> ss; vector<thread> th;
  for (int t = 0; t < threads; t++) { ss.push_back(new Searcher()); ss.back()->inProgress = ss.back()->myTicket; }
  allSearchers = ss;
  // tickets: each Searcher took one ticket in its constructor; tickets are handed out in increasing order
  for (int t = 0; t < threads; t++) th.emplace_back([&, t] { ss[t]->dfs(0, 0, 0, 0); });
  for (auto& x : th) x.join();
  u64 h1r = 0, brk = 0, csk = 0, nodes = 0, qual = 0, rej = 0, byH[16] = {0}, calls = 0, pairs = 0, n1 = 0, clq = 0; long long sols = 0;
  for (auto* s : ss) { h1r += s->h1Refuted; brk += s->breaks; csk += s->cliqueSkips; clq += s->cliquePruned; nodes += s->nodes; qual += s->qualSets; rej += s->rejU; for (int h = 0; h < 16; h++) byH[h] += s->coresByH[h]; calls += s->cp.calls; pairs += s->cp.pairsTried; n1 += s->cp.n1Tried; sols += s->cp.nSol; }
  double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
  printf("DONE K=%d A=%llu Y=%llu hmax=%d nodes=%llu qualifyingSets=%llu rejectedByUnsatisfiedPrimes=%llu", K, (unsigned long long)A, (unsigned long long)Y, HMAX,
         (unsigned long long)nodes, (unsigned long long)qual, (unsigned long long)rej);
  for (int h = 0; h <= HMAX; h++) printf(" cores[h=%d]=%llu", h, (unsigned long long)byH[h]);
  printf(" cliquePruned=%llu loopBreaks=%llu cliqueSkips=%llu h1RefutedByDeltaTest=%llu", (unsigned long long)clq, (unsigned long long)brk, (unsigned long long)csk, (unsigned long long)h1r);
  printf(" completionCalls=%llu twoTermCandidates=%llu smallestElementCandidates=%llu solutions=%lld wall=%.1fs\nend %s\n",
         (unsigned long long)calls, (unsigned long long)pairs, (unsigned long long)n1, sols, secs, nowJST().c_str());
  { u64 ap = 0, dv = 0; for (auto* s : ss) { ap += s->h2cnt.ap; dv += s->h2cnt.dv; } if (h2ind) printf("h2 inline (ind2): viaAP=%llu viaDivisors=%llu\n", (unsigned long long)ap, (unsigned long long)dv); }
  if (h2SampleF) fclose(h2SampleF);
  if (dumpF) { if (dumpGz) pclose(dumpF); else fclose(dumpF); }
}
