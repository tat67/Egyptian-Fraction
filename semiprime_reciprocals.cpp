// semiprime_reciprocals.cpp
//
// Problem.  Let P = { p*q : p < q primes } = { 6, 10, 14, 15, 21, 22, 26, 33, ... }.
// Is there a nonempty T subset of P with |T| <= 46 such that sum_{n in T} 1/n is an integer?
//
// Answer computed by this program: NO.
//
// The program is a complete, exact (integer-only) computer proof.  No floating point type
// (float/double/long double) is used anywhere.  All "real number" comparisons are done
// either with exact big-integer rationals or with 96-bit fixed-point numbers whose rounding
// direction is always chosen so that the comparison stays valid (upper bounds are rounded
// up, lower bounds are rounded down).  See README.md for the full mathematical argument;
// the comments below summarise it.
//
// ---------------------------------------------------------------------------------------
// 1.  Size.  If |T| = k <= 46 then sum 1/n <= H_46 := sum of the reciprocals of the 46
//     smallest elements of P, and H_46 < 2 (checked exactly below).  So an integral sum
//     must be exactly 1.  Also H_37 < 1, hence k >= 38.
//
// 2.  Graph form.  View T as a graph on primes: n = p*q in T is an edge {p,q}.  For a prime
//     p write N(p) for its neighbours.  Then sum_{n in T} 1/n is an integer  <=>  for every
//     prime p:   sum_{q in N(p)} q^{-1} == 0 (mod p).                                  (*)
//     (The only terms with p in the denominator are (1/p)*sum_{q in N(p)} 1/q.)
//
// 3.  Decomposition.  S = primes <= 73 (these are all primes occurring in the 46 smallest
//     elements of P); "big" primes are primes >= 79.  C = edges of T inside S ("core"),
//     G = the other edges (each has at least one big end).  For q in S let rho(q) be the
//     residue of sum_{r: qr in C} r^{-1} mod q, and U = { q in S : rho(q) != 0 }.
//     Every q in U must have a big neighbour (otherwise (*) fails at q) and an edge of G has
//     at most one end in S, so   |G| >= |U|   and therefore   |C| + |U| <= |T| <= 46.
//     If |C| + |U| = 46 then |G| = |U| exactly: every q in U has exactly one big
//     neighbour, no other edge of G exists, so every big prime P is a "star" whose
//     neighbours all lie in U; (*) at q in U forces P^{-1} == -rho(q) (mod q), and (*) at P
//     forces P | n(B) := sum_{q in B} prod(B)/q, where B = N(P).
//
// 4.  Value.  Every edge of G has a prime factor >= 79.  If q in U, the edge joining q to a
//     big prime is at most 1/(79q).  Hence  sum_C >= 1 - sum_{q in U} 1/(79 q) - V(46-|C|-|U|)
//     where V(x) = sum of the x largest reciprocals of elements of P having a factor >= 79.
//     Also sum_C <= 1.
//
// 5.  Computation.  Enumerate ALL cores C (subsets of the 210 semiprimes with both factors
//     in S) with |C| + |U(C)| <= 46 that satisfy the value condition in 4.  This is a depth
//     first search over the 21 primes of S in decreasing order; when prime p is processed,
//     all of its core edges are fixed, so rho(p) is known and p is either satisfied or put
//     into U (which costs one unit of the 46-budget).  For every surviving core:
//       - if U is empty, C itself would be a solution;
//       - if |C|+|U| <= 45 (and U nonempty) the core is reported as UNRESOLVED;
//       - if |C|+|U| = 46 we test every partition of U into blocks B and every prime P>73
//         with P == (-rho(q))^{-1} (mod q) for q in B and P | n(B) (these are the only
//         possible completions by 3).
//     The run finds no solution and no unresolved core, which proves the answer is NO.
//
// Usage:  ./semiprime_reciprocals [threads] [--selftest]
//   --selftest additionally (a) finds and exactly verifies all 47-term solutions whose
//   primes are <= 73 (showing the engine finds solutions when they exist), and (b) runs the
//   full machinery with S = primes <= 53 and budget 47, where known 47-term solutions using
//   the prime 59 must be rediscovered through the "star" completion step.
// ---------------------------------------------------------------------------------------

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <mutex>
#include <numeric>
#include <set>
#include <string>
#include <thread>
#include <vector>

using namespace std;
typedef unsigned long long u64;
typedef unsigned __int128 u128;

// ============================ integer utilities =======================================
static u64 mulmod(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }
static u64 powmod(u64 a, u64 e, u64 m) {
    u64 r = 1 % m; a %= m;
    while (e) { if (e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; }
    return r;
}
// deterministic Miller-Rabin for all 64-bit integers
static bool isPrime64(u64 n) {
    if (n < 2) return false;
    static const u64 small[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (u64 p : small) if (n % p == 0) return n == p;
    u64 d = n - 1; int s = 0;
    while (!(d & 1)) { d >>= 1; ++s; }
    for (u64 a : small) {
        u64 x = powmod(a, d, n);
        if (x == 1 || x == n - 1) continue;
        bool composite = true;
        for (int r = 1; r < s; ++r) { x = mulmod(x, x, n); if (x == n - 1) { composite = false; break; } }
        if (composite) return false;
    }
    return true;
}
static u64 invmodPrime(u64 a, u64 p) { return powmod(a % p, p - 2, p); }   // p prime, p !| a
static vector<int> primesUpTo(int n) {
    vector<char> c(n + 1, 1); vector<int> r;
    for (int i = 2; i <= n; ++i) if (c[i]) { r.push_back(i); for (long long j = (long long)i * i; j <= n; j += i) c[j] = 0; }
    return r;
}

// ----- 96-bit fixed point: x is represented by an integer X ~ x * 2^96 -----
static const int FP = 96;
static const u128 ONE = (u128)1 << FP;
static inline u128 recipUp(u64 n) { return (ONE + n - 1) / n; }   // >= 2^96/n
static inline u128 recipLo(u64 n) { return ONE / n; }             // <= 2^96/n
// decimal rendering of a fixed-point number (integer arithmetic only), 6 decimals, truncated
static string fpToString(u128 x) {
    u128 ip = x >> FP; u128 frac = x & (ONE - 1);
    u128 f6 = (frac * 1000000) >> FP;
    char buf[64]; snprintf(buf, sizeof buf, "%llu.%06llu", (u64)ip, (u64)f6); return buf;
}

// ----- minimal arbitrary precision natural numbers (base 2^32) -----
struct BigNat {
    vector<uint32_t> d;   // little endian, no leading zeros
    BigNat(u64 v = 0) { while (v) { d.push_back((uint32_t)v); v >>= 32; } }
    void mulSmall(uint32_t m) {
        u64 carry = 0;
        for (auto& x : d) { u64 t = (u64)x * m + carry; x = (uint32_t)t; carry = t >> 32; }
        if (carry) d.push_back((uint32_t)carry);
        if (m == 0) d.clear();
    }
    void add(const BigNat& o) {
        u64 carry = 0; size_t n = max(d.size(), o.d.size()); d.resize(n, 0);
        for (size_t i = 0; i < n; ++i) {
            u64 t = (u64)d[i] + (i < o.d.size() ? o.d[i] : 0) + carry; d[i] = (uint32_t)t; carry = t >> 32;
        }
        if (carry) d.push_back((uint32_t)carry);
    }
    static int cmp(const BigNat& a, const BigNat& b) {
        if (a.d.size() != b.d.size()) return a.d.size() < b.d.size() ? -1 : 1;
        for (size_t i = a.d.size(); i-- > 0;) if (a.d[i] != b.d[i]) return a.d[i] < b.d[i] ? -1 : 1;
        return 0;
    }
};
// Exact sum of 1/n over a list of squarefree semiprimes (given as prime pairs):
// returns (num, den) with den = product of all primes involved (a common denominator).
static void exactSum(const vector<pair<u64, u64>>& T, BigNat& num, BigNat& den) {
    set<u64> ps; for (auto& e : T) { ps.insert(e.first); ps.insert(e.second); }
    den = BigNat(1); for (u64 p : ps) den.mulSmall((uint32_t)p);
    num = BigNat(0);
    for (auto& e : T) {
        BigNat t(1);
        for (u64 p : ps) if (p != e.first && p != e.second) t.mulSmall((uint32_t)p);
        num.add(t);
    }
}
static bool exactSumIsOne(const vector<pair<u64, u64>>& T) {
    BigNat n, d; exactSum(T, n, d); return BigNat::cmp(n, d) == 0;
}

// ======================== Part 1: the smallest semiprimes ================================
struct SemiprimeList {
    vector<u64> val; vector<pair<u64, u64>> fac;
    explicit SemiprimeList(u64 limit) {
        vector<int> ps = primesUpTo((int)(limit / 2 + 1));
        vector<pair<u64, pair<u64, u64>>> v;
        for (size_t i = 0; i < ps.size(); ++i)
            for (size_t j = i + 1; j < ps.size() && (u64)ps[i] * ps[j] <= limit; ++j)
                v.push_back({(u64)ps[i] * ps[j], {(u64)ps[i], (u64)ps[j]}});
        sort(v.begin(), v.end());
        for (auto& x : v) { val.push_back(x.first); fac.push_back(x.second); }
    }
};

// ======================== Part 2: the core search engine ================================
struct Engine {
    // parameters
    int SB;          // S = primes <= SB
    int KT;          // budget for |C| + |U|  (the maximal number of elements of T)
    bool allowExc;   // allow unsatisfied primes (U nonempty); false = plain search
    int LOWN = 8;    // smallest LOWN primes handled through precomputed residue tables
    // data
    vector<int> pr; int m = 0; u64 bigMin = 0;
    vector<vector<int>> inv;                    // inv[a][b] = pr[b]^{-1} mod pr[a]
    vector<vector<u128>> EU, EL;               // EU[j][i] = up(pr[j]*pr[i]), EL = lo
    vector<vector<u128>> MX;                   // MX[j][R]
    vector<vector<vector<u128>>> BT;           // BT[j][i][R]
    struct LowSub { uint32_t mask; int cnt; u128 u, l; };
    vector<vector<vector<LowSub>>> LOWL;       // LOWL[j][residue]
    vector<u128> GV;                           // GV[j] = up(bigMin*pr[j]) bound for the U-edge at pr[j]
    vector<u128> VB;                           // VB[x] = sum of x largest 1/n, n in P with factor >= bigMin
    // results
    mutex mx;
    atomic<long long> nodes{0};
    long long endStates = 0, endTight = 0, unresolved = 0;
    vector<vector<pair<u64, u64>>> solutions;
    vector<string> unresolvedList;
    bool verbose = true;
    int maxStar = 0;                           // largest possible number of neighbours of a big prime

    Engine(int sb, int kt, bool exc) : SB(sb), KT(kt), allowExc(exc) {
        pr = primesUpTo(SB); m = (int)pr.size();
        vector<int> big = primesUpTo(4 * SB + 100);
        for (int p : big) if (p > SB) { bigMin = p; break; }
        inv.assign(m, vector<int>(m, 0));
        for (int a = 0; a < m; ++a) for (int b = 0; b < m; ++b) if (a != b) inv[a][b] = (int)invmodPrime(pr[b], pr[a]);
        // V(x): the x largest reciprocals of semiprimes having a prime factor > SB
        {
            u64 lim = 60ull * bigMin;   // far more than enough terms below this limit
            vector<int> ps = primesUpTo((int)(lim / 2 + 1)); vector<u64> bs;
            for (size_t a = 0; a < ps.size(); ++a)
                for (size_t b = a + 1; b < ps.size() && (u64)ps[a] * ps[b] <= lim; ++b)
                    if (ps[b] > SB) bs.push_back((u64)ps[a] * ps[b]);
            sort(bs.begin(), bs.end());
            VB.assign(KT + 2, 0);
            for (int x = 1; x <= KT + 1; ++x) VB[x] = VB[x - 1] + recipUp(bs[x - 1]);
        }
        GV.resize(m); for (int j = 0; j < m; ++j) GV[j] = recipUp(bigMin * pr[j]);
        // Star-size lemma: a big prime P with d neighbours, all in S, contributes at most
        // (1/bigMin) * (sum of the d largest 1/q, q in S); the other <= KT-d elements of T
        // contribute at most H_{KT-d}.  If the total is < 1, such a star cannot occur.
        {
            SemiprimeList sp(4000);
            maxStar = 0;
            for (int d = 1; d <= m && d <= KT; ++d) {
                u128 z = 0; for (int i = 0; i < d; ++i) z += recipUp(bigMin * (u64)pr[i]);
                u128 h = 0; for (int i = 0; i < KT - d; ++i) h += recipUp(sp.val[i]);
                if (z + h >= ONE) maxStar = d;
            }
        }
        // MX[j][R] = max_x ( M_j(x) + VB[R-x] ), M_j(x) = x largest reciprocals of semiprimes on pr[0..j-1]
        MX.assign(m + 1, vector<u128>(KT + 1, 0));
        for (int j = 0; j <= m; ++j) {
            vector<u64> v;
            for (int a = 0; a < j; ++a) for (int b = a + 1; b < j; ++b) v.push_back((u64)pr[a] * pr[b]);
            sort(v.begin(), v.end());
            vector<u128> M(KT + 1, 0); u128 s = 0;
            for (int x = 0; x <= KT; ++x) { M[x] = s; if (x < (int)v.size()) s += recipUp(v[x]); }
            for (int R = 0; R <= KT; ++R) {
                u128 best = 0;
                for (int x = 0; x <= R; ++x) {
                    u128 val = M[x] + (allowExc ? VB[R - x] : 0);
                    if (val > best) best = val;
                }
                MX[j][R] = best;
            }
        }
        EU.assign(m, {}); EL.assign(m, {});
        for (int j = 0; j < m; ++j) {
            EU[j].resize(j); EL[j].resize(j);
            for (int i = 0; i < j; ++i) { EU[j][i] = recipUp((u64)pr[j] * pr[i]); EL[j][i] = recipLo((u64)pr[j] * pr[i]); }
        }
        // BT[j][i][R] = max_t ( sum_{k<t} EU[j][k] + MX[j][R-t] ), t <= min(i,R):
        // best possible value of the rest if pr[j] still may take neighbours among pr[0..i-1]
        BT.assign(m, {});
        for (int j = 0; j < m; ++j) {
            BT[j].assign(j + 1, vector<u128>(KT + 1, 0));
            for (int i = 0; i <= j; ++i)
                for (int R = 0; R <= KT; ++R) {
                    u128 best = 0, g = 0;
                    for (int t = 0; t <= min(i, R); ++t) {
                        u128 v = g + MX[j][R - t]; if (v > best) best = v;
                        if (t < i) g += EU[j][t];
                    }
                    BT[j][i][R] = best;
                }
        }
        LOWL.assign(m, {});
        for (int j = 0; j < m; ++j) {
            int p = pr[j], L = min(j, LOWN); LOWL[j].assign(p, {});
            for (uint32_t mask = 0; mask < (1u << L); ++mask) {
                int r = 0, cnt = 0; u128 u = 0, l = 0;
                for (int q = 0; q < L; ++q) if (mask >> q & 1) { r = (r + inv[j][q]) % p; ++cnt; u += EU[j][q]; l += EL[j][q]; }
                LOWL[j][r].push_back(LowSub{mask, cnt, u, l});
            }
        }
    }

    // ---- completion of a tight core (|C|+|U| = KT) by stars of big primes ----
    // U given as list of (q, rho(q)).  Tries all partitions of U into blocks B with a prime
    // P > SB, P == (-rho(q))^{-1} mod q for q in B, P | n(B).  Returns true and the big
    // edges if a completion exists.
    bool blockPrime(const vector<pair<int, int>>& blk, u64& Pout) const {
        if (blk.size() < 2) return false;                     // a big prime needs >= 2 neighbours
        if ((int)blk.size() > maxStar) return false;          // impossible by the star-size lemma
        u64 D = 1; for (auto& x : blk) D *= (u64)x.first;      // <= 73*71*...*37 < 2^58 (<= 10 primes)
        u64 n = 0; for (auto& x : blk) n += D / (u64)x.first;  // n(B) < 2D since sum 1/q < 2
        // CRT: P == a_q (mod q), a_q = (-rho)^{-1} mod q
        u64 X = 0, Mo = 1;
        for (auto& x : blk) {
            u64 q = x.first, a = invmodPrime((u64)((q - x.second % q) % q), q);
            u64 t = (u64)((a + q - X % q) % q) * invmodPrime(Mo % q, q) % q;
            X += Mo * t; Mo *= q;
        }
        for (u64 P = X; P <= n;) {                            // P | n(B) forces P <= n(B) < 2D
            if (P > (u64)SB && n % P == 0 && isPrime64(P)) { Pout = P; return true; }
            if (n - P < D) break;
            P += D;
        }
        return false;
    }
    bool partitionSearch(vector<pair<int, int>>& rest, vector<pair<u64, u64>>& bigEdges) const {
        if (rest.empty()) return true;
        pair<int, int> first = rest[0];
        int r = (int)rest.size() - 1;
        for (uint32_t mask = 0; mask < (1u << r); ++mask) {
            vector<pair<int, int>> blk{first}, other;
            for (int i = 0; i < r; ++i) (mask >> i & 1 ? blk : other).push_back(rest[i + 1]);
            u64 P;
            if (!blockPrime(blk, P)) continue;
            size_t keep = bigEdges.size();
            for (auto& x : blk) bigEdges.push_back({(u64)x.first, P});
            if (partitionSearch(other, bigEdges)) return true;
            bigEdges.resize(keep);
        }
        return false;
    }

    // Work distribution: every thread walks the (small) part of the tree above level splitJ in
    // the same deterministic order; the nodes at level splitJ are numbered 0,1,2,... and each
    // number is claimed by exactly one thread through a shared atomic ticket counter.
    atomic<long long> ticket{0};
    struct Worker {
        Engine& E; int tid, T, splitJ; long long splitCounter = 0, myTicket = -1;
        // res[q]  : residue at q contributed by the core edges decided so far (edges to larger primes)
        // rho[q]  : full core residue of q, recorded when q is put into U
        vector<int> res, rho; vector<pair<int, int>> edges; uint32_t U = 0; u128 gz = 0; long long nodes = 0;
        vector<vector<int>> CH;
        Worker(Engine& e, int t, int TT, int sj) : E(e), tid(t), T(TT), splitJ(sj) { res.assign(E.m, 0); rho.assign(E.m, 0); CH.assign(E.m, {}); }

        void endState(int c, u128 su) {
            int e = __builtin_popcount(U);
            if (su + gz + E.VB[E.KT - c - e] < ONE) return;           // value condition (section 4)
            vector<pair<u64, u64>> T;
            for (auto& x : edges) T.push_back({(u64)E.pr[x.first], (u64)E.pr[x.second]});
            lock_guard<mutex> g(E.mx);
            E.endStates++;
            if (e == 0) { if (c > 0) E.solutions.push_back(T); return; }
            if (c + e < E.KT) {
                E.unresolved++;
                string s = "c=" + to_string(c) + " U={";
                for (int q = 0; q < E.m; ++q) if (U >> q & 1) s += " " + to_string(E.pr[q]) + ":" + to_string(rho[q]);
                s += " }"; E.unresolvedList.push_back(s); return;
            }
            E.endTight++;
            vector<pair<int, int>> Ul;
            for (int q = 0; q < E.m; ++q) if (U >> q & 1) Ul.push_back({E.pr[q], rho[q]});
            vector<pair<u64, u64>> bigEdges;
            if (E.partitionSearch(Ul, bigEdges)) {
                for (auto& b : bigEdges) T.push_back(b);
                E.solutions.push_back(T);
            }
        }
        void dfs(int j, int c, u128 su, u128 sl) {
            if (j == splitJ) {
                long long k = splitCounter++;
                if (myTicket < k) myTicket = E.ticket.fetch_add(1);
                if (myTicket != k) return;          // node k belongs to another thread
            }
            if (j < 0) { endState(c, su); return; }
            if (j == 0) {                                      // prime 2: no smaller primes left
                if (res[0] == 0) { dfs(-1, c, su, sl); }
                else if (E.allowExc && c + __builtin_popcount(U) + 1 <= E.KT) {
                    U |= 1; rho[0] = res[0]; gz += E.GV[0]; dfs(-1, c, su, sl); U &= ~1u; gz -= E.GV[0];
                }
                return;
            }
            int p = E.pr[j]; int target = (p - res[j]) % p; CH[j].clear();
            sub(j, j, target, 0, 0, c, su, sl, 0, 0);
        }
        // choose the neighbours of pr[j] among pr[0..i-1]; high part explicit, low part by table
        void sub(int j, int i, int target, int modsum, int cnt, int c, u128 su, u128 sl, u128 pu, u128 pl) {
            ++nodes;
            int p = E.pr[j]; int L = min(j, E.LOWN);
            int e = __builtin_popcount(U);
            int R = E.KT - c - e - cnt; if (R < 0) return;
            if (sl + pl > ONE) return;                              // core sum must stay <= 1
            if (su + pu + gz + E.BT[j][i][R] < ONE) return;         // cannot reach 1 any more
            if (i == L) {
                int need = (target - modsum + p) % p;
                bool excOK = E.allowExc && R >= 1 && (su + pu + gz + E.BT[j][L][R - 1] + E.GV[j] >= ONE);
                for (int r0 = 0; r0 < p; ++r0) {
                    bool exc = (r0 != need);
                    if (exc && !excOK) continue;
                    for (auto& ls : E.LOWL[j][r0]) {
                        int cc = cnt + ls.cnt; int RR = E.KT - c - e - cc - (exc ? 1 : 0); if (RR < 0) continue;
                        u128 nu = pu + ls.u, nl = pl + ls.l;
                        if (sl + nl > ONE) continue;
                        u128 g2 = gz + (exc ? E.GV[j] : 0);
                        if (su + nu + g2 + E.MX[j][RR] < ONE) continue;
                        vector<int>& ch = CH[j]; size_t base = ch.size();
                        for (int q = 0; q < L; ++q) if (ls.mask >> q & 1) ch.push_back(q);
                        for (int q : ch) { res[q] = (res[q] + E.inv[q][j]) % E.pr[q]; edges.push_back({q, j}); }
                        // full residue of pr[j] = res[j] + modsum + r0 = r0 - need (mod p)
                        if (exc) { U |= 1u << j; gz = g2; rho[j] = (r0 - need + p) % p; }
                        dfs(j - 1, c + cc, su + nu, sl + nl);
                        if (exc) { U &= ~(1u << j); gz -= E.GV[j]; }
                        for (int q : ch) { res[q] = (res[q] + E.pr[q] - E.inv[q][j]) % E.pr[q]; edges.pop_back(); }
                        ch.resize(base);
                    }
                }
                return;
            }
            int q = i - 1;
            CH[j].push_back(q);
            sub(j, i - 1, target, (modsum + E.inv[j][q]) % p, cnt + 1, c, su, sl, pu + E.EU[j][q], pl + E.EL[j][q]);
            CH[j].pop_back();
            sub(j, i - 1, target, modsum, cnt, c, su, sl, pu, pl);
        }
    };

    void run(int threads, int splitPrime) {
        int splitJ = -2;
        for (int j = 0; j < m; ++j) if (pr[j] == splitPrime) splitJ = j;
        vector<thread> th;
        for (int t = 0; t < threads; ++t)
            th.emplace_back([&, t]() {
                Worker w(*this, t, threads, splitJ);
                w.dfs(m - 1, 0, 0, 0);
                nodes += w.nodes;
            });
        for (auto& x : th) x.join();
    }
};

// ======================================= main ===========================================
static void printSolution(const vector<pair<u64, u64>>& T) {
    vector<u64> v; for (auto& e : T) v.push_back(e.first * e.second); sort(v.begin(), v.end());
    printf("    [%zu terms]", v.size());
    for (u64 x : v) printf(" %llu", x);
    printf("\n");
}

int main(int argc, char** argv) {
    int threads = (int)thread::hardware_concurrency(); if (threads <= 0) threads = 4;
    bool selftest = false, runMain = true, onlyC = false;
    int budget = 46;      // --budget N : search |T| <= N instead (N <= 46 keeps H_N < 2)
    for (int a = 1; a < argc; ++a) {
        if (!strcmp(argv[a], "--selftest")) selftest = true;
        else if (!strcmp(argv[a], "--skip-main")) runMain = false;          // (testing aid)
        else if (!strcmp(argv[a], "--star-unit-test")) { selftest = true; onlyC = true; }
        else if (!strcmp(argv[a], "--budget") && a + 1 < argc) budget = atoi(argv[++a]);
        else threads = max(1, atoi(argv[a]));
    }
    if (budget < 1 || budget > 46) { printf("budget must be in 1..46\n"); return 1; }
    auto t0 = chrono::steady_clock::now();
    auto secs = [&]() { return (long long)chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now() - t0).count(); };

    printf("=== Part 1: the smallest squarefree semiprimes ===\n");
    SemiprimeList SP(2000);
    {
        // exact rational H_k = sum_{i<k} 1/a_i
        auto Hcmp = [&](int k, u64 integer) {   // sign of H_k - integer
            vector<pair<u64, u64>> T(SP.fac.begin(), SP.fac.begin() + k);
            BigNat n, d; exactSum(T, n, d); BigNat rhs = d; rhs.mulSmall((uint32_t)integer);
            return BigNat::cmp(n, rhs);
        };
        u128 h = 0; for (int i = 0; i < 46; ++i) h += recipUp(SP.val[i]);
        printf("46 smallest elements of P:");
        for (int i = 0; i < 46; ++i) printf(" %llu", SP.val[i]);

        printf("\nH_46 = sum of their reciprocals < %s   (exact check H_46 < 2: %s)\n", fpToString(h).c_str(), Hcmp(46, 2) < 0 ? "yes" : "NO");
        printf("exact checks: H_37 < 1: %s,  H_38 > 1: %s   => any solution has 38..46 terms and sum exactly 1\n",
               Hcmp(37, 1) < 0 ? "yes" : "NO", Hcmp(38, 1) > 0 ? "yes" : "NO");
        if (!(Hcmp(46, 2) < 0)) { printf("unexpected\n"); return 1; }
    }

    bool proved = false;
    if (runMain) {
        printf("\n=== Part 2: exhaustive search (S = primes <= 73, |C|+|U| <= %d) ===\n", budget);
        printf("threads = %d\n", threads); fflush(stdout);
        Engine E(73, budget, true);
        printf("largest possible star (neighbours of one big prime): %d\n", E.maxStar);
        E.run(threads, 59);
        printf("search nodes           : %lld\n", (long long)E.nodes);
        printf("cores passing all tests: %lld (of which |C|+|U| = %d: %lld)\n", E.endStates, budget, E.endTight);
        printf("unresolved cores       : %lld\n", E.unresolved);
        for (auto& s : E.unresolvedList) printf("    UNRESOLVED %s\n", s.c_str());
        printf("solutions found        : %zu\n", E.solutions.size());
        for (auto& T : E.solutions) { printSolution(T); printf("      exact sum == 1 : %s\n", exactSumIsOne(T) ? "yes" : "no"); }
        printf("elapsed: %lld s\n", secs());
        proved = E.unresolved == 0 && E.solutions.empty();
    }

    if (selftest) {
        if (!onlyC) {
        printf("\n=== Self test (a): all 47-term solutions with every prime <= 73 ===\n"); fflush(stdout);
        Engine A(73, 47, false);
        A.run(threads, 59);
        int ok = 0;
        for (auto& T : A.solutions) { printSolution(T); if (exactSumIsOne(T)) ++ok; }
        printf("found %zu solutions, %d verified exactly (sum == 1)\n", A.solutions.size(), ok);
        }
        printf("\n=== Self test (c): star completion on a known 47-term solution ===\n");
        {
            // Watanabe-type 47-term solution (found again by self test (a)); uses the primes 47 and 59.
            const u64 known[47] = {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69,
                                   77, 82, 85, 86, 87, 91, 93, 94, 95, 118, 119, 123, 133, 145, 155, 161, 187, 203,
                                   215, 287, 329, 493, 517, 1247, 1357, 1363, 2537};
            vector<pair<u64, u64>> K;
            for (u64 n : known) for (u64 p = 2; p * p <= n; ++p) if (n % p == 0) { K.push_back({p, n / p}); break; }
            printf("exact sum of the 47 reciprocals == 1 : %s\n", exactSumIsOne(K) ? "yes" : "NO");
            // treat primes > 53 as "big": core = edges inside S = primes <= 53 (only 59 is big)
            Engine Z(53, 47, true);
            map<u64, int> rhoMap;
            for (auto& e : K) if (e.second <= 53) {
                rhoMap[e.first] = (int)((rhoMap[e.first] + invmodPrime(e.second, e.first)) % e.first);
                rhoMap[e.second] = (int)((rhoMap[e.second] + invmodPrime(e.first, e.second)) % e.second);
            }
            vector<pair<int, int>> Ul; for (auto& x : rhoMap) if (x.second) Ul.push_back({(int)x.first, x.second});
            int coreSize = 0; for (auto& e : K) if (e.second <= 53) ++coreSize;
            printf("core size %d, |U| = %zu, U =", coreSize, Ul.size());
            for (auto& x : Ul) printf(" %d", x.first);
            printf("\n");
            vector<pair<u64, u64>> bigEdges;
            bool ok = Z.partitionSearch(Ul, bigEdges);
            printf("star completion found: %s ->", ok ? "yes" : "NO");
            for (auto& b : bigEdges) printf(" %llu*%llu", b.first, b.second);
            printf("\n");
        }
        if (!onlyC) {
        printf("\n=== Self test (b): full machinery with S = primes <= 53, budget 47 ===\n"); fflush(stdout);
        Engine Bq(53, 47, true);
        Bq.run(threads, 43);
        int ok2 = 0, withBig = 0;
        for (auto& T : Bq.solutions) {
            bool big = false; for (auto& e : T) if (e.second > 53 || e.first > 53) big = true;
            if (exactSumIsOne(T)) { ++ok2; if (big) { ++withBig; printSolution(T); } }
        }
        printf("found %zu solutions, %d verified exactly, %d of them use a prime > 53 (found via stars); unresolved cores: %lld\n",
               Bq.solutions.size(), ok2, withBig, Bq.unresolved);
        printf("elapsed: %lld s\n", secs());
        }
    }

    printf("\n=== RESULT ===\n");
    if (!runMain)
        printf("(main search skipped)\n");
    else if (proved)
        printf("No nonempty set T of squarefree semiprimes with |T| <= %d has an integral sum of reciprocals.\n", budget);
    else
        printf("The search did not close the proof (see above).\n");
    return proved ? 0 : 2;
}
