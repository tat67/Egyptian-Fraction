// q2b.cpp -- single-threaded predecessor of q2exact.cpp without the clique rule (cross-check).
// Core C = T cap [2,Y] by increasing-order depth-first search (value window + residue pruning),
// huge part H = T cap (Y, oo) with |H| = h <= hmax by exact completion (compl.h).
#include <bits/stdc++.h>
#include "gmpz.h"
#include "compl.h"
using namespace std;
typedef unsigned long long u64; typedef long long i64; typedef __int128 i128; typedef unsigned __int128 u128;

static int K; static u64 A, Y = 0; static int HMAX;
static const u128 S = (u128)1 << 96;
static u128 lamLow, lamUp; static u128 Wup = 0;

static u64 inv_mod(u64 a, u64 m) { i128 t = 0, nt = 1, r = m, nr = a % m;
  while (nr) { i128 q = r / nr, tmp = t - q * nt; t = nt; nt = tmp; tmp = r - q * nr; r = nr; nr = tmp; }
  if (t < 0) t += m; return (u64)t; }
static bool isPrimePowerSmall(u64 n) { for (u64 p = 2; p * p <= n; p++) if (n % p == 0) { while (n % p == 0) n /= p; return n == 1; } return true; }
static vector<pair<u64,int>> factorSmall(u64 n) { vector<pair<u64,int>> f; for (u64 p = 2; p * p <= n; p++) if (n % p == 0) { int k = 0; while (n % p == 0) { n /= p; k++; } f.push_back({p, k}); } if (n > 1) f.push_back({n, 1}); return f; }

// ---- Lagrangian constant: chain cover of the weights 1/n - 1/A on non-prime-powers n < A ----
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
// Returns an exact upper bound Wup (scaled by S) for the maximum weight of an antichain, where the
// weight of n is ceil(S/n) - floor(S/A); verified as a chain cover.
static u128 chainCoverBound() {
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
  for (int e = 0; e < m; e++) if ((i128)cov[e] < w[e]) { fprintf(stderr, "cover fails\n"); exit(1); }
  return W;
}

// ---- core universe and search ----
static vector<u64> U; static vector<u128> rLow, rUp; static vector<vector<int>> comp;
static vector<vector<pair<int,u64>>> res;   // per element: (prime index, residue contribution)
static vector<u64> pr, Mq; static vector<int> Eq, lastIdx; static unordered_map<u64,int> pid;
static u128 lowTarget[64];
static Completer comp_;
static u64 nodes = 0, qualSets = 0, coresByH[16] = {0}, rejUfin = 0;
static vector<int> cur; static vector<int> blk; static vector<u64> R; static vector<char> inSet;
static FILE* dumpF = nullptr; static bool doComplete = true; static int splitDepth = 12, workerId = 0, workers = 1; static u64 splitCounter = 0;

static int chromaticU(const vector<pair<u64,int>>& Ul, int cap) {
  int n = Ul.size(); if (n == 0) return 0;
  vector<vector<char>> adj(n, vector<char>(n, 0));
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) {
    u64 p = Ul[i].first, q = Ul[j].first; u64 pe = 1, qe = 1; for (int t = 0; t < Ul[i].second; t++) pe *= p; for (int t = 0; t < Ul[j].second; t++) qe *= q;
    bool c = false;
    for (u64 x = p; x <= pe && x <= Y && !c; x *= p) for (u64 y = q; y <= qe && x * y <= Y; y *= q) if (inSet[x * y]) { c = true; break; }
    adj[i][j] = adj[j][i] = c;
  }
  vector<int> order(n); iota(order.begin(), order.end(), 0);
  vector<int> deg(n, 0); for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) deg[i] += adj[i][j];
  sort(order.begin(), order.end(), [&](int x, int y) { return deg[x] > deg[y]; });
  int best = cap + 1; vector<int> col(n, -1);
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
static vector<pair<u64,int>> currentU(int fromIdxFinal) {  // primes whose residue is final (lastIdx < fromIdxFinal) and nonzero
  vector<pair<u64,int>> Ul;
  for (size_t qi = 0; qi < pr.size(); qi++) if (R[qi] && lastIdx[qi] < fromIdxFinal) {
    u64 r = R[qi]; int v = 0; while (r % pr[qi] == 0) { r /= pr[qi]; v++; } Ul.push_back({pr[qi], Eq[qi] - v}); }
  return Ul;
}
static void leafCheck(int cnt, u128 sLow, u128 sUp) {
  qualSets++;
  int h = K - cnt;
  vector<pair<u64,int>> Ul = currentU(INT_MAX);
  if (Ul.empty() != (h == 0)) return;
  if (h > 0 && chromaticU(Ul, h) > h) { rejUfin++; return; }
  // exact remainder
  vector<u64> C; for (int x : cur) C.push_back(U[x]);
  Z num(0), den(1);
  for (u64 n : C) { Z nn(n); num = num * nn + den; den = den * nn; Z g = gcd(num, den); num = divexact(num, g); den = divexact(den, g); }
  Z a = den - num, b = den;
  if (h == 0) { if (a.sgn() == 0) { comp_.core = C; vector<Z> none; comp_.verify(none); } return; }
  if (a.sgn() <= 0) return;
  if (cmp(a * (Y + 1), b * (unsigned long)h) > 0) return;
  Z bb(1); for (auto& u : Ul) for (int t = 0; t < u.second; t++) bb = bb * u.first; if (cmp(bb, b) != 0) { fprintf(stderr, "residue/denominator mismatch\n"); exit(8); }
  coresByH[h]++;
  if (dumpF) { for (u64 n : C) fprintf(dumpF, "%llu ", (unsigned long long)n); fprintf(dumpF, "| h=%d %s/%s\n", h, a.str().c_str(), b.str().c_str()); }
  if (doComplete) { comp_.core = C; comp_.coreSet = set<u64>(C.begin(), C.end()); Fac bf; for (auto& u : Ul) bf.push_back({Z(u.first), u.second}); vector<Z> ch; comp_.run(a, b, bf, h, Z(Y), ch); }
}
static void dfs(int i, int cnt, u128 sLow, u128 sUp, int hloParent) {
  if (workers > 1 && cnt == splitDepth) { if ((splitCounter++ % workers) != (u64)workerId) return; }
  nodes++;
  // residues already final at this node
  vector<pair<u64,int>> Uf = currentU(i);
  int hlo = Uf.empty() ? 0 : chromaticU(Uf, HMAX);
  if (hlo > HMAX) return;
  int jmax = K - hlo, jmin = max(cnt + 1, K - HMAX);
  if (jmin > jmax) return;
  // value bound: some size j in [jmin, jmax] must still reach its window
  bool any = false; u128 acc = sUp; int taken = 0;
  for (int k = i; k < (int)U.size() && cnt + taken < jmax; k++) if (!blk[k]) {
    acc += rUp[k]; taken++; int j = cnt + taken;
    if (j >= jmin && acc >= lowTarget[K - j]) { any = true; break; }
  }
  if (!any) return;
  for (int k = i; k < (int)U.size(); k++) if (!blk[k]) {
    u128 nl = sLow + rLow[k], nu = sUp + rUp[k];
    if (nl > S) continue;   // elements are in increasing order but rLow decreases: later k may still fit
    for (int f : comp[k]) blk[f]++; cur.push_back(k); inSet[U[k]] = 1;
    for (auto& r : res[k]) R[r.first] = (R[r.first] + r.second) % Mq[r.first];
    int j = cnt + 1;
    if (j >= K - HMAX && j <= K && nu >= lowTarget[K - j]) leafCheck(j, nl, nu);
    if (j < K) dfs(k + 1, j, nl, nu, hlo);
    for (auto& r : res[k]) R[r.first] = (R[r.first] + Mq[r.first] - r.second) % Mq[r.first];
    inSet[U[k]] = 0; cur.pop_back(); for (int f : comp[k]) blk[f]--;
  }
}

int main(int argc, char** argv) {
  // usage: q2b K A [Y|0] [nocomplete] [dump]
  K = atoi(argv[1]); A = strtoull(argv[2], 0, 10); if (argc > 3) Y = strtoull(argv[3], 0, 10);
  if (argc > 4 && string(argv[4]) == "nocomplete") doComplete = false;
  if (argc > 5 && string(argv[5]) != "-") dumpF = fopen(argv[5], "w");
  if (argc > 7) { workerId = atoi(argv[6]); workers = atoi(argv[7]); }
  if (argc > 8) splitDepth = atoi(argv[8]);
  auto t0 = chrono::steady_clock::now();
  lamLow = S / A; lamUp = (S + A - 1) / A; Wup = chainCoverBound();
  i128 sig = (i128)K * (i128)lamUp + (i128)Wup - (i128)S;          // >= K/A + W - 1 (scaled)
  int hinf = 0; while ((i128)(hinf + 1) * (i128)lamLow <= sig) hinf++;
  if (Y == 0) { u64 y = A; while ((i128)(hinf + 1) * ((i128)lamLow - (i128)((S + y) / (y + 1))) <= sig) y++; Y = y; }
  HMAX = 0; while ((i128)(HMAX + 1) * ((i128)lamLow - (i128)((S + Y) / (Y + 1))) <= sig) HMAX++;
  for (u64 n = 6; n <= Y; n++) if (!isPrimePowerSmall(n)) U.push_back(n);
  int m = U.size(); comp.assign(m, {}); blk.assign(m, 0); inSet.assign(Y + 1, 0);
  for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++) if (U[b] % U[a] == 0) { comp[a].push_back(b); comp[b].push_back(a); }
  for (u64 n : U) { rLow.push_back(S / n); rUp.push_back((S + n - 1) / n); }
  for (int h = 0; h <= HMAX; h++) lowTarget[h] = S - (S * (u128)h) / (Y + 1) - 1;
  set<u64> ps; for (u64 n : U) for (auto& f : factorSmall(n)) ps.insert(f.first);
  for (u64 p : ps) { pid[p] = pr.size(); pr.push_back(p); int E = 0; u64 M = 1; while (M <= Y / p) { M *= p; E++; } Mq.push_back(M); Eq.push_back(E); lastIdx.push_back(-1); }
  res.assign(m, {});
  for (int i = 0; i < m; i++) for (auto& f : factorSmall(U[i])) {
    int qi = pid[f.first]; u64 M = Mq[qi], q = f.first; int v = f.second; u64 u = U[i]; for (int t = 0; t < v; t++) u /= q;
    u64 pw = 1; for (int t = 0; t < Eq[qi] - v; t++) pw *= q;
    res[i].push_back({qi, (u64)((u128)pw * inv_mod(u % M, M) % M)}); lastIdx[qi] = i;
  }
  R.assign(pr.size(), 0);
  comp_.Y = Y; comp_.onSolution = [](const string& s) { printf("%s\n", s.c_str()); fflush(stdout); };
  printf("K=%d A=%llu Y=%llu hmax=%d universe=%d sigmaUp*1e9/S=%lld\n", K, (unsigned long long)A, (unsigned long long)Y, HMAX, m, (long long)(sig / (i128)(S / 1000000000ULL)));
  fflush(stdout);
  dfs(0, 0, 0, 0, 0);
  double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
  printf("DONE K=%d A=%llu Y=%llu hmax=%d nodes=%llu qualifyingSets=%llu rejectedByU=%llu", K, (unsigned long long)A, (unsigned long long)Y, HMAX, (unsigned long long)nodes, (unsigned long long)qualSets, (unsigned long long)rejUfin);
  for (int h = 0; h <= HMAX; h++) printf(" cores[h=%d]=%llu", h, (unsigned long long)coresByH[h]);
  printf(" completionCalls=%llu twoTermPairs=%llu n1=%llu solutions=%lld time=%.2fs\n", (unsigned long long)comp_.calls, (unsigned long long)comp_.pairsTried, (unsigned long long)comp_.n1Tried, comp_.nSol, secs);
  if (dumpF) fclose(dumpF);
}
