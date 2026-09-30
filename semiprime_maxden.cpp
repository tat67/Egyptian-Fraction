// semiprime_maxden.cpp
//
// Problem.  P = { p*q : p < q primes } = { 6, 10, 14, 15, 21, ... }.  Among all nonempty finite
// T ⊆ P with  sum_{n in T} 1/n = 1,  find the minimum possible value of max T.
//
// Answer computed by this program: 589 = 19 * 31.
//
// Method (all arithmetic is exact: machine integers and a small big-natural type; the program
// contains no floating-point type).
//
//  * A set T ⊆ P is a graph on the primes (n = p*q is the edge {p,q}).  If sum 1/n = 1 then,
//    for every prime q, the residue  rho_q(T) = sum_{p : pq in T} p^{-1}  is 0 in Z/qZ
//    (local criterion; Lemma 1 of README.md, `integral_iff_localCond` in Lean).
//  * For a bound B let E_B = P ∩ [1, B] and D_B = product of the primes <= B/2, so that every
//    n in E_B divides D_B and  sum_{n in T} 1/n = 1  <=>  sum_{n in T} D_B/n = D_B.
//  * Search.  A node of the search is a partial assignment: every edge of E_B is IN, OUT or
//    undecided.  A node is closed ("leaf") when one of three exact tests shows that no
//    completion T can satisfy both conditions:
//       hi : sum_{IN} D/n > D                           (the sum already exceeds 1)
//       lo : sum_{not OUT} D/n < D                      (even taking everything left, sum < 1)
//       md q : q prime and  -rho_q(IN)  is not a subset sum (mod q) of the inverses of the
//              undecided edges at q  (computed by a residue-reachability bitset).
//    Otherwise, if some undecided edge is *forced* (setting it IN, resp. OUT, closes the node
//    at once by one of the tests), it is set the other way; else the search branches on an
//    edge at the prime whose residue condition has the fewest completions.  A node with no
//    undecided edge that is not closed is an exact solution (sum = 1).
//  * Minimality.  For each m in P in increasing order the program searches E_m with the
//    edge m forced IN, i.e. for a solution with max T = m.  The first m with a solution is
//    the answer; every smaller m has been refuted exhaustively.
//  * Independent certificate.  The program also searches E_{m*-1} (nothing forced) and records
//    the whole search tree.  It re-checks that tree with a separate checker that implements
//    exactly the function `check` of lean/SemiprimeEgypt/MaxDenCheck.lean, and (with --cert)
//    writes it as a Lean file; Lean's kernel then re-checks it (see lean/README_MAXDEN.md).
//
// Build:  g++ -O2 -std=c++17 -o semiprime_maxden semiprime_maxden.cpp
// Run:    ./semiprime_maxden                 (solve and verify)
//         ./semiprime_maxden --cert FILE     (also write the Lean certificate for bound m*-1)
//         ./semiprime_maxden --count         (also count all solutions with max T = m*)

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <string>
#include <vector>

using namespace std;
typedef uint64_t u64;
typedef int64_t i64;

// ------------------------------------------------------------------------------------------
// Big natural numbers (base 2^32, little endian).  Only what is needed: +, -, compare,
// multiplication and division by a small number, decimal output.
// ------------------------------------------------------------------------------------------
struct BigNat {
  vector<uint32_t> d;
  BigNat() {}
  explicit BigNat(u64 x) {
    while (x) { d.push_back((uint32_t)x); x >>= 32; }
  }
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
  BigNat r; u64 c = 0; size_t n = max(a.d.size(), b.d.size());
  r.d.resize(n);
  for (size_t i = 0; i < n; i++) {
    u64 t = c + (i < a.d.size() ? a.d[i] : 0) + (i < b.d.size() ? b.d[i] : 0);
    r.d[i] = (uint32_t)t; c = t >> 32;
  }
  if (c) r.d.push_back((uint32_t)c);
  r.trim(); return r;
}
// requires a >= b
static BigNat sub(const BigNat& a, const BigNat& b) {
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
static BigNat divSmall(const BigNat& a, uint32_t m, uint32_t* rem = nullptr) {
  BigNat r; r.d.assign(a.d.size(), 0); u64 rm = 0;
  for (int i = (int)a.d.size() - 1; i >= 0; i--) {
    u64 cur = (rm << 32) | a.d[i];
    r.d[i] = (uint32_t)(cur / m); rm = cur % m;
  }
  r.trim(); if (rem) *rem = (uint32_t)rm; return r;
}
static string toDec(BigNat a) {
  if (a.isZero()) return "0";
  vector<uint32_t> parts;
  while (!a.isZero()) { uint32_t r; a = divSmall(a, 1000000000u, &r); parts.push_back(r); }
  string s = to_string(parts.back());
  char buf[16];
  for (int i = (int)parts.size() - 2; i >= 0; i--) { snprintf(buf, sizeof buf, "%09u", parts[i]); s += buf; }
  return s;
}
// decimal expansion of num/den (num/den < 10) with `digits` digits after the point, truncated
static string fracDec(BigNat num, const BigNat& den, int digits) {
  int ip = 0;
  while (cmp(num, den) >= 0) { num = sub(num, den); ip++; }
  string s = to_string(ip) + ".";
  for (int k = 0; k < digits; k++) {
    num = mulSmall(num, 10); int dg = 0;
    while (cmp(num, den) >= 0) { num = sub(num, den); dg++; }
    s += char('0' + dg);
  }
  return s;
}

// ------------------------------------------------------------------------------------------
// Elementary number theory (integers only)
// ------------------------------------------------------------------------------------------
static vector<int> primesUpTo(int n) {
  vector<int> ps; if (n < 2) return ps;
  vector<char> s(n + 1, 1); s[0] = s[1] = 0;
  for (int i = 2; (i64)i * i <= n; i++) if (s[i]) for (int j = i * i; j <= n; j += i) s[j] = 0;
  for (int i = 2; i <= n; i++) if (s[i]) ps.push_back(i);
  return ps;
}
static bool isPrimeTD(i64 n) {  // trial division
  if (n < 2) return false;
  for (i64 d = 2; d * d <= n; d++) if (n % d == 0) return false;
  return true;
}
static int powMod(i64 a, i64 e, i64 m) {
  i64 r = 1 % m; a %= m;
  while (e) { if (e & 1) r = r * a % m; a = a * a % m; e >>= 1; }
  return (int)r;
}
// n is a squarefree semiprime: returns true and sets p < q with n = p*q
static bool splitSP(i64 n, i64& p, i64& q) {
  for (i64 d = 2; d * d <= n; d++) if (n % d == 0) {
    p = d; q = n / d;
    return isPrimeTD(p) && isPrimeTD(q) && p < q;
  }
  return false;
}

// ------------------------------------------------------------------------------------------
// Instance for a bound B: the edges E_B = P ∩ [1, B], D_B, weights D_B/n, incidences.
// ------------------------------------------------------------------------------------------
struct Instance {
  int B = 0;
  vector<int> primes;           // primes <= B/2, ascending
  vector<int> pidx;             // prime -> index in `primes`, else -1
  vector<int> en, ep, eq;       // edges: n = ep*eq, ep < eq, sorted by n
  vector<int> eidx;             // n -> edge index or -1
  BigNat D;                     // product of the primes <= B/2
  vector<BigNat> w;             // w[e] = D / en[e]
  BigNat total;                 // sum of all w[e]
  vector<vector<int>> inc;      // per prime index: incident edges (ascending n)
  vector<vector<int>> incInv;   // inverse (mod that prime) of the other end
  explicit Instance(int B_) : B(B_) {
    primes = primesUpTo(B / 2);
    pidx.assign(B / 2 + 2, -1);
    for (size_t i = 0; i < primes.size(); i++) pidx[primes[i]] = (int)i;
    vector<pair<int, int>> ed;
    for (size_t a = 0; a < primes.size(); a++)
      for (size_t b = a + 1; b < primes.size() && (i64)primes[a] * primes[b] <= B; b++)
        ed.push_back({primes[a] * primes[b], (int)a});
    sort(ed.begin(), ed.end());
    eidx.assign(B + 1, -1);
    D = BigNat(1);
    for (int p : primes) D = mulSmall(D, (uint32_t)p);
    inc.assign(primes.size(), {}); incInv.assign(primes.size(), {});
    for (auto& t : ed) {
      int n = t.first, p = primes[t.second], q = n / p, e = (int)en.size();
      en.push_back(n); ep.push_back(p); eq.push_back(q); eidx[n] = e;
      w.push_back(divSmall(D, (uint32_t)n));
      total = add(total, w.back());
      int a = pidx[p], b = pidx[q];
      inc[a].push_back(e); incInv[a].push_back(powMod(q, p - 2, p));
      inc[b].push_back(e); incInv[b].push_back(powMod(p, q - 2, q));
    }
  }
};

// ------------------------------------------------------------------------------------------
// The search.
// ------------------------------------------------------------------------------------------
enum { UND = 0, IN = 1, OUT = 2 };
enum LeafKind { NOLEAF = 0, LEAF_LO, LEAF_HI, LEAF_MD };
struct Leaf { LeafKind k; int q; };

struct CertNode {       // search tree / certificate node
  int type;             // 0 = lo, 1 = hi, 2 = md q, 3 = br n (a: IN child, b: OUT child), 4 = solution
  int arg;
  int a, b;
};

struct Solver {
  const Instance& I;
  bool buildTree = false;     // record the tree (certificate mode)
  bool countAll = false;      // continue after solutions (count them)
  vector<int8_t> st;
  BigNat sIn, sAll;           // sum of w over IN edges, over not-OUT edges
  u64 nodes = 0, solutions = 0;
  bool stop = false;
  vector<int> firstSolution;  // edge values
  vector<vector<int>> allSolutions;  // all solutions found (count mode)
  vector<CertNode> tree;

  explicit Solver(const Instance& inst) : I(inst) {
    st.assign(I.en.size(), UND);
    sAll = I.total;
  }
  void setIn(int e) { st[e] = IN; sIn = add(sIn, I.w[e]); }
  void unsetIn(int e) { st[e] = UND; sIn = sub(sIn, I.w[e]); }
  void setOut(int e) { st[e] = OUT; sAll = sub(sAll, I.w[e]); }
  void unsetOut(int e) { st[e] = UND; sAll = add(sAll, I.w[e]); }

  // md test at prime index qi: true if the residue condition at q can no longer be met
  bool modLeaf(int qi) const {
    int q = I.primes[qi], rho = 0;
    vector<char> R(q, 0), S(q);
    R[0] = 1;
    for (size_t t = 0; t < I.inc[qi].size(); t++) {
      int e = I.inc[qi][t], a = I.incInv[qi][t];
      if (st[e] == IN) rho = (rho + a) % q;
      else if (st[e] == UND) {
        for (int x = 0; x < q; x++) S[x] = R[x];
        for (int x = 0; x < q; x++) if (R[x]) S[(x + a) % q] = 1;
        R.swap(S);
      }
    }
    return !R[(q - rho) % q];
  }
  Leaf valueLeaf() const {
    if (cmp(sIn, I.D) > 0) return {LEAF_HI, 0};
    if (cmp(sAll, I.D) < 0) return {LEAF_LO, 0};
    return {NOLEAF, 0};
  }
  Leaf anyLeaf() const {
    Leaf v = valueLeaf(); if (v.k) return v;
    for (size_t i = 0; i < I.primes.size(); i++) if (modLeaf((int)i)) return {LEAF_MD, I.primes[i]};
    return {NOLEAF, 0};
  }
  // after changing edge e only the value tests and the tests at the two ends can change
  Leaf leafAfter(int e) const {
    Leaf v = valueLeaf(); if (v.k) return v;
    int a = I.pidx[I.ep[e]], b = I.pidx[I.eq[e]];
    if (modLeaf(a)) return {LEAF_MD, I.ep[e]};
    if (modLeaf(b)) return {LEAF_MD, I.eq[e]};
    return {NOLEAF, 0};
  }
  int mk(int type, int arg, int a = -1, int b = -1) {
    if (!buildTree) return -1;
    tree.push_back({type, arg, a, b});
    return (int)tree.size() - 1;
  }
  int mkLeaf(Leaf L) {
    if (L.k == LEAF_LO) return mk(0, 0);
    if (L.k == LEAF_HI) return mk(1, 0);
    return mk(2, L.q);
  }
  // number of subsets of the undecided edges at qi meeting the residue condition (saturating)
  u64 completions(int qi, int& firstUnd, int& nUnd) const {
    int q = I.primes[qi], rho = 0;
    vector<u64> c(q, 0), c2(q);
    c[0] = 1; firstUnd = -1; nUnd = 0;
    for (size_t t = 0; t < I.inc[qi].size(); t++) {
      int e = I.inc[qi][t], a = I.incInv[qi][t];
      if (st[e] == IN) rho = (rho + a) % q;
      else if (st[e] == UND) {
        if (firstUnd < 0) firstUnd = e;
        nUnd++;
        for (int x = 0; x < q; x++) c2[x] = c[x];
        for (int x = 0; x < q; x++) {
          u64& y = c2[(x + a) % q];
          y = (y > UINT64_MAX - c[x]) ? UINT64_MAX : y + c[x];
        }
        c.swap(c2);
      }
    }
    return c[(q - rho) % q];
  }

  int dfs() {
    if (stop) return -1;
    nodes++;
    Leaf L = anyLeaf();
    if (L.k) return mkLeaf(L);
    // forced moves
    for (size_t e = 0; e < st.size(); e++) {
      if (st[e] != UND) continue;
      setIn((int)e); Leaf a = leafAfter((int)e); unsetIn((int)e);
      if (a.k) {
        int la = mkLeaf(a);
        setOut((int)e); int r = dfs(); unsetOut((int)e);
        return mk(3, I.en[e], la, r);
      }
      setOut((int)e); Leaf b = leafAfter((int)e); unsetOut((int)e);
      if (b.k) {
        int lb = mkLeaf(b);
        setIn((int)e); int r = dfs(); unsetIn((int)e);
        return mk(3, I.en[e], r, lb);
      }
    }
    // branching edge: at the prime with the fewest completions
    int best = -1; u64 bestCount = UINT64_MAX;
    for (size_t i = 0; i < I.primes.size(); i++) {
      int f, k; u64 c = completions((int)i, f, k);
      if (k > 0 && c < bestCount) { bestCount = c; best = f; }
    }
    if (best < 0) {
      // every edge decided and no test closes the node: sum_IN = sum_notOUT, neither < D nor
      // > D, so the IN edges sum to exactly 1.
      solutions++;
      vector<int> cur;
      for (size_t e = 0; e < st.size(); e++) if (st[e] == IN) cur.push_back(I.en[e]);
      if (firstSolution.empty()) firstSolution = cur;
      if (countAll && allSolutions.size() < 1000) allSolutions.push_back(cur);
      if (!countAll) stop = true;
      return mk(4, 0);
    }
    setIn(best); int x = dfs(); unsetIn(best);
    setOut(best); int y = dfs(); unsetOut(best);
    return mk(3, I.en[best], x, y);
  }
};

// ------------------------------------------------------------------------------------------
// Independent checker of a recorded tree.  It implements exactly `check` of
// lean/SemiprimeEgypt/MaxDenCheck.lean: the state is (inn, out, sIn, sAll) with inn/out bit
// sets indexed by the semiprime n itself, the md test walks the ascending prime list and uses
// a rotated q-bit reachability mask, and a branch requires n in E_B and n undecided.
// ------------------------------------------------------------------------------------------
struct TreeChecker {
  int B; vector<int> PL; vector<char> isPM, isEM; BigNat D;
  vector<char> inn, out;
  BigNat sIn, sAll;
  const vector<CertNode>& T;
  u64 checked = 0;
  TreeChecker(const Instance& I, const vector<CertNode>& tree) : T(tree) {
    B = I.B; PL = I.primes; D = I.D;
    isPM.assign(B + 1, 0); for (int p : PL) isPM[p] = 1;
    isEM.assign(B + 1, 0); for (int n : I.en) isEM[n] = 1;
    inn.assign(B + 1, 0); out.assign(B + 1, 0);
    // S0 = sum over n <= B with EM bit of D / n
    for (int n = 1; n <= B; n++) if (isEM[n]) sAll = add(sAll, divSmall(D, (uint32_t)n));
  }
  bool md(int q) const {
    if (q < 0 || q > B || !isPM[q]) return false;
    int rho = 0;
    vector<char> R(q, 0), R2(q);
    R[0] = 1;
    for (int p : PL) {
      if ((i64)p * q > B) break;           // PL ascending: nbrs stops at the first p with p*q > B
      if (p == q) continue;
      int n = p * q, a = powMod(p, q - 2, q);
      if (inn[n]) rho = (rho + a) % q;
      else if (!out[n]) {                  // R ||| rot q a R
        for (int x = 0; x < q; x++) R2[x] = R[x];
        for (int x = 0; x < q; x++) if (R[x]) R2[(x + a) % q] = 1;
        R.swap(R2);
      }
    }
    return !R[(q - rho) % q];
  }
  bool check(int v) {
    checked++;
    const CertNode& c = T[v];
    if (c.type == 0) return cmp(sAll, D) < 0;
    if (c.type == 1) return cmp(D, sIn) < 0;
    if (c.type == 2) return md(c.arg);
    if (c.type != 3) return false;
    int n = c.arg;
    if (n < 0 || n > B || !isEM[n] || inn[n] || out[n]) return false;
    BigNat wn = divSmall(D, (uint32_t)n);
    inn[n] = 1; BigNat old = sIn; sIn = add(sIn, wn);
    bool ok = check(c.a);
    inn[n] = 0; sIn = old;
    if (!ok) return false;
    out[n] = 1; old = sAll; sAll = sub(sAll, wn);
    ok = check(c.b);
    out[n] = 0; sAll = old;
    return ok;
  }
};

// ------------------------------------------------------------------------------------------
// Lean output of the data and the certificate
// ------------------------------------------------------------------------------------------
static void writeLean(const char* path, const Instance& I, const vector<CertNode>& T, int root) {
  FILE* f = fopen(path, "w");
  if (!f) { perror(path); exit(1); }
  fprintf(f, "/-\nGenerated by semiprime_maxden.cpp (--cert).  Do not edit.\n\n"
             "The data of the bound B = %d and the certificate tree (%zu nodes) of the search over\n"
             "E_B = P ∩ [1, B].  `MaxDenMain.lean` checks it with `decide +kernel`.\n-/\n"
             "import SemiprimeEgypt.MaxDenCheck\n\nnamespace SemiprimeEgypt.MaxDen.C%d\n\n",
          I.B, T.size(), I.B);
  // data
  BigNat EM, PM;
  {
    // bit masks as big naturals
    vector<uint32_t> em((I.B + 32) / 32 + 1, 0), pm((I.B + 32) / 32 + 1, 0);
    for (int n : I.en) em[n / 32] |= (1u << (n % 32));
    for (int p : I.primes) pm[p / 32] |= (1u << (p % 32));
    EM.d = em; EM.trim(); PM.d = pm; PM.trim();
  }
  fprintf(f, "/-- The data for B = %d: primes <= B/2, D = their product, the bit masks of E_B and of\n"
             "the primes, and S0 = sum_{n in E_B} D/n. -/\ndef data : Data where\n", I.B);
  fprintf(f, "  Bd := %d\n  PL := [", I.B);
  for (size_t i = 0; i < I.primes.size(); i++) fprintf(f, "%s%d", i ? ", " : "", I.primes[i]);
  fprintf(f, "]\n  D := %s\n  EM := %s\n  PM := %s\n  S0 := %s\n\n",
          toDec(I.D).c_str(), toDec(EM).c_str(), toDec(PM).c_str(), toDec(I.total).c_str());
  // certificate, chunked into definitions
  vector<string> S(T.size());
  int cnt = 0;
  for (size_t i = 0; i < T.size(); i++) {
    const CertNode& c = T[i];
    string s;
    if (c.type == 0) s = ".lo";
    else if (c.type == 1) s = ".hi";
    else if (c.type == 2) s = "(.md " + to_string(c.arg) + ")";
    else s = "(.br " + to_string(c.arg) + " " + S[c.a] + " " + S[c.b] + ")";
    if (s.size() > 1500) {
      fprintf(f, "def c%d : Cert := %s\n\n", cnt, s.c_str());
      s = "c" + to_string(cnt); cnt++;
    }
    S[i] = s;
    if (c.type == 3) { S[c.a].clear(); S[c.a].shrink_to_fit(); S[c.b].clear(); S[c.b].shrink_to_fit(); }
  }
  fprintf(f, "/-- The certificate: the root of the search tree for B = %d. -/\ndef cert : Cert := %s\n\n",
          I.B, S[root].c_str());
  fprintf(f, "end SemiprimeEgypt.MaxDen.C%d\n", I.B);
  fclose(f);
}

// ------------------------------------------------------------------------------------------
static string nowUTC() {
  time_t t = time(nullptr); char buf[64];
  strftime(buf, sizeof buf, "%Y-%m-%d %H:%M:%S UTC", gmtime(&t));
  return buf;
}
static long long msSince(chrono::steady_clock::time_point t0) {
  return (long long)chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - t0).count();
}

int main(int argc, char** argv) {
  const char* certPath = nullptr; bool doCount = false; int scanLimit = 100000;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--cert") && i + 1 < argc) certPath = argv[++i];
    else if (!strcmp(argv[i], "--count")) doCount = true;
    else if (!strcmp(argv[i], "--limit") && i + 1 < argc) scanLimit = atoi(argv[++i]);
    else { fprintf(stderr, "usage: %s [--cert FILE] [--count] [--limit N]\n", argv[0]); return 1; }
  }
  auto t0 = chrono::steady_clock::now();
  printf("start: %s\n\n", nowUTC().c_str());

  // ---------------- Part 1: a trivial lower bound from the size of the sum ----------------
  printf("=== Part 1: size bound ===\n");
  int trivial = 0;
  {
    Instance J(scanLimit < 2000 ? scanLimit : 2000);
    BigNat s;
    for (size_t e = 0; e < J.en.size(); e++) {
      s = add(s, J.w[e]);
      if (cmp(s, J.D) >= 0) { trivial = J.en[e]; break; }
    }
    printf("sum of 1/n over all n in P with n <= m first reaches 1 at m = %d\n", trivial);
    printf("  => max T >= %d for every solution T\n\n", trivial);
  }

  // ---------------- Part 2: scan m in P upwards, search for a solution with max T = m -------
  printf("=== Part 2: exhaustive search for max T = m, m in P increasing ===\n");
  int answer = -1; vector<int> sol; u64 scanNodes = 0; int scanned = 0;
  for (int m = 6; m <= scanLimit; m++) {
    i64 p, q;
    if (!splitSP(m, p, q)) continue;
    Instance I(m);
    Solver S(I);
    int em = I.eidx[m];
    S.setIn(em);
    S.dfs();
    scanNodes += S.nodes; scanned++;
    if (S.solutions > 0) {
      answer = m; sol = S.firstSolution;
      printf("m = %d = %lld*%lld: solution found (%llu search nodes)\n", m, (long long)p, (long long)q,
             (unsigned long long)S.nodes);
      break;
    }
    if (S.nodes > 1)
      printf("m = %d = %lld*%lld: no solution with max T = m (%llu search nodes)\n", m, (long long)p,
             (long long)q, (unsigned long long)S.nodes);
  }
  if (answer < 0) { printf("no solution with max T <= %d\n", scanLimit); return 0; }
  printf("(every other m in P below %d is refuted at the root node by the tests alone)\n", answer);
  printf("values of m refuted: %d (all m in P below %d); total search nodes %llu\n\n", scanned - 1, answer,
         (unsigned long long)scanNodes);

  // ---------------- Part 3: verify the solution exactly ----------------
  printf("=== Part 3: exact verification of the solution ===\n");
  sort(sol.begin(), sol.end());
  bool ok = true;
  vector<int> usedPrimes;
  for (size_t i = 0; i < sol.size(); i++) {
    i64 p, q;
    if (!splitSP(sol[i], p, q)) { ok = false; printf("  %d is not a squarefree semiprime!\n", sol[i]); }
    else { usedPrimes.push_back((int)p); usedPrimes.push_back((int)q); }
    if (i && sol[i] == sol[i - 1]) ok = false;
  }
  sort(usedPrimes.begin(), usedPrimes.end());
  usedPrimes.erase(unique(usedPrimes.begin(), usedPrimes.end()), usedPrimes.end());
  BigNat L(1);
  for (int p : usedPrimes) L = mulSmall(L, (uint32_t)p);
  BigNat num;
  for (int n : sol) { uint32_t r; BigNat t = divSmall(L, (uint32_t)n, &r); if (r) ok = false; num = add(num, t); }
  bool sumIsOne = cmp(num, L) == 0;
  printf("T (%zu elements):\n", sol.size());
  for (size_t i = 0; i < sol.size(); i++) {
    i64 p, q; splitSP(sol[i], p, q);
    printf("  %d = %lld*%lld%s", sol[i], (long long)p, (long long)q, (i % 6 == 5 || i + 1 == sol.size()) ? "\n" : "");
  }
  printf("common denominator L = product of the %zu primes used = %s\n", usedPrimes.size(), toDec(L).c_str());
  printf("sum_{n in T} L/n       = %s\n", toDec(num).c_str());
  printf("all elements distinct squarefree semiprimes: %s\n", ok ? "yes" : "NO");
  printf("sum_{n in T} 1/n = 1 exactly: %s\n", sumIsOne ? "yes" : "NO");
  printf("max T = %d\n\n", sol.back());
  if (!ok || !sumIsOne || sol.back() != answer) { printf("VERIFICATION FAILED\n"); return 1; }

  // ---------------- Part 4: certificate for the bound answer-1 ----------------
  int Bc = answer - 1;
  printf("=== Part 4: certificate: no solution inside E_%d = P ∩ [1, %d] (nothing forced) ===\n", Bc, Bc);
  Instance IC(Bc);
  {
    printf("|E_%d| = %zu, primes <= %d: %zu, D = product of those primes (%zu bits)\n", Bc, IC.en.size(), Bc / 2,
           IC.primes.size(), IC.D.d.size() * 32);
    printf("sum over E_%d of 1/n = %s...\n", Bc, fracDec(IC.total, IC.D, 12).c_str());
    Solver S(IC);
    S.buildTree = true; S.countAll = true;
    int root = S.dfs();
    int solNodes = 0, leaves = 0;
    for (auto& c : S.tree) { if (c.type == 4) solNodes++; if (c.type <= 2) leaves++; }
    printf("search tree: %zu nodes, %d closed leaves, %d solution leaves\n", S.tree.size(), leaves, solNodes);
    if (solNodes) { printf("UNEXPECTED: solution inside E_%d\n", Bc); return 1; }
    TreeChecker C(IC, S.tree);
    bool cok = C.check(root);
    printf("independent re-check of the tree (semantics of the Lean `check`): %s (%llu nodes)\n",
           cok ? "accepted" : "REJECTED", (unsigned long long)C.checked);
    if (!cok) return 1;
    if (certPath) { writeLean(certPath, IC, S.tree, root); printf("Lean certificate written to %s\n", certPath); }
  }
  printf("\n");

  // ---------------- optional: count all solutions with max T = answer ----------------
  if (doCount) {
    printf("=== Count of all T with sum 1 and max T = %d ===\n", answer);
    Instance I(answer);
    Solver S(I); S.countAll = true;
    S.setIn(I.eidx[answer]);
    S.dfs();
    printf("solutions: %llu (search nodes %llu)\n", (unsigned long long)S.solutions, (unsigned long long)S.nodes);
    for (auto& v : S.allSolutions) {
      // exact re-verification of each one
      vector<int> ps2;
      for (int n : v) { i64 p, q; if (splitSP(n, p, q)) { ps2.push_back((int)p); ps2.push_back((int)q); } }
      sort(ps2.begin(), ps2.end()); ps2.erase(unique(ps2.begin(), ps2.end()), ps2.end());
      BigNat L2(1); for (int p : ps2) L2 = mulSmall(L2, (uint32_t)p);
      BigNat s2; for (int n : v) s2 = add(s2, divSmall(L2, (uint32_t)n));
      printf("  |T| = %zu, sum = 1 exactly: %s:", v.size(), cmp(s2, L2) == 0 ? "yes" : "NO");
      for (int n : v) printf(" %d", n);
      printf("\n");
    }
    printf("\n");
  }

  printf("=== RESULT ===\n");
  printf("The minimum of max T over all nonempty T ⊆ P with sum_{n in T} 1/n = 1 is %d = ", answer);
  { i64 p, q; splitSP(answer, p, q); printf("%lld*%lld.\n", (long long)p, (long long)q); }
  printf("\nend: %s\nelapsed: %lld ms\n", nowUTC().c_str(), msSince(t0));
  return 0;
}
