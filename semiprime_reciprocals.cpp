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
//
// 4.  Value.  Every edge of G has a prime factor >= 79.  If q in U, the edge joining q to a
//     big prime is at most 1/(79q).  Hence  sum_C >= 1 - sum_{q in U} 1/(79 q) - V(46-|C|-|U|)
//     where V(x) = sum of the x largest reciprocals of elements of P having a factor >= 79.
//     Also sum_C <= 1.
//
// 5.  Computation.  Step 1 enumerates ALL cores C (subsets of the 210 semiprimes with both
//     factors in S) with |C| + |U(C)| <= 46 that satisfy the value condition in 4.  This is a
//     depth first search over the 21 primes of S in decreasing order; when prime p is
//     processed, all of its core edges are fixed, so rho(p) is known and p is either
//     satisfied or put into U (which costs one unit of the 46-budget).
//     Step 2 decides for every surviving core whether a big part G can complete it: with
//     d_q = number of big neighbours of q in S and b = number of big-big edges,
//       - d_q >= 1 on U, d_q in {0} u [2,inf) off U, and the excess
//         b + sum_{U}(d_q-1) + sum_{not U} d_q = |G| - |U| <= 46 - |C| - |U|;
//       - parity at 2: rho(2) + d_2 is even (every big prime is odd);
//       - value: 1 - sum_C <= sum_{d_q=1} 1/(q Pmin(q)) + sum_{d_q>=2} sum_{k<d_q} 1/(q b_k)
//         + b/(79*83), Pmin(q) = least prime > 73 congruent to (-rho(q))^{-1} mod q;
//       - if b = 0 every big prime is a star P | n(A), A = its neighbours in S, |A| <= 10;
//         all such stars are listed and an exact cover (multiplicities d_q, residues) is
//         searched.  A surviving shape with b > 0 would be reported as UNRESOLVED.
//     The run finds no solution and nothing unresolved, which proves the answer is NO.
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
#include <functional>
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
    long long shapesTried = 0, shapesAlive = 0, starCands = 0, coresWithShape = 0;
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
        for (int p : primesUpTo(20 * SB + 1000)) if (p > SB && bigList.size() < 64) bigList.push_back((u64)p);
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

    // ---------------- completion of a core by big primes (README, section 4) ----------------
    // A completion G of a core C is a set of <= KT-|C| elements of P, each with a prime factor
    // > SB, such that C u G satisfies (*) everywhere.  Its "shape" is
    //   d_q  = number of big neighbours of q in S,   nbb = number of edges joining two big primes.
    // Necessary conditions (all proved in the README):
    //   (i)   d_q >= 1 for q in U;  d_q = 0 or d_q >= 2 for q in S \ U;
    //   (ii)  excess E = nbb + sum_{q in U} (d_q - 1) + sum_{q not in U} d_q <= KT - |C| - |U|;
    //   (iii) parity at 2: every big prime is odd, so rho(2) + d_2 is even;
    //   (iv)  value: 1 - sum_C = sum_G <= sum_{q in U, d_q = 1} 1/(q*Pmin(q))
    //                 + sum_{d_q >= 2} sum_{k < d_q} 1/(q*b_k) + nbb/(b_0*b_1),
    //         where b_0 < b_1 < ... are the primes > SB and Pmin(q) is the least prime > SB with
    //         Pmin(q) == (-rho(q))^{-1} (mod q) (the only big neighbour of q must be in this class).
    // If nbb = 0 every big prime P has all its neighbours in W = {q : d_q >= 1}, so P | n(A) for
    // its neighbour set A; these finitely many stars are found by factoring n(A) and an exact
    // cover (with multiplicities d_q and the residue conditions) is searched.  A surviving
    // shape with nbb > 0 would be reported as unresolved (none occurs).
    vector<u64> bigList;                       // the first primes > SB
    u64 pminFor(int qi, int r) const {         // least prime P > SB with P == (-r)^{-1} mod pr[qi]
        u64 q = pr[qi]; u64 a = invmodPrime((q - (u64)r % q) % q, q);
        u64 P = a; while (P <= (u64)SB || !isPrime64(P)) P += q;
        return P;
    }
    static u64 rhoFactor(u64 n) {              // a nontrivial factor of composite n (Pollard rho)
        if (n % 2 == 0) return 2;
        for (u64 c = 1;; ++c) {
            u64 x = 2, y = 2, d = 1;
            auto f = [&](u64 v) { return (mulmod(v, v, n) + c) % n; };
            while (d == 1) { x = f(x); y = f(f(y)); d = gcd(x > y ? x - y : y - x, n); }
            if (d != n) return d;
        }
    }
    static void factorInto(u64 n, vector<u64>& out) {
        if (n == 1) return;
        if (isPrime64(n)) { out.push_back(n); return; }
        u64 d = rhoFactor(n); factorInto(d, out); factorInto(n / d, out);
    }
    struct Star { u64 P; uint32_t mask; };      // mask over the index list W
    // exact cover of W with multiplicities need[], distinct primes, residue conditions
    bool coverSearch(const vector<int>& W, const vector<int>& rhoW, vector<int>& need, vector<int>& resid,
                     const vector<Star>& cand, vector<u64>& usedP, vector<pair<u64, u64>>& out) const {
        int w = (int)W.size(), first = -1;
        for (int i = 0; i < w; ++i) if (need[i] > 0) { first = i; break; }
        if (first < 0) {
            for (int i = 0; i < w; ++i) { int q = pr[W[i]]; if ((resid[i] + rhoW[i]) % q != 0) return false; }
            return true;
        }
        for (auto& st : cand) {
            if (!(st.mask >> first & 1)) continue;
            bool ok = true;
            for (int i = 0; i < w && ok; ++i) if ((st.mask >> i & 1) && need[i] == 0) ok = false;
            for (u64 P : usedP) if (P == st.P) ok = false;
            if (!ok) continue;
            for (int i = 0; i < w; ++i) if (st.mask >> i & 1) { --need[i]; resid[i] = (int)((resid[i] + invmodPrime(st.P, pr[W[i]])) % pr[W[i]]); }
            usedP.push_back(st.P);
            size_t keep = out.size();
            for (int i = 0; i < w; ++i) if (st.mask >> i & 1) out.push_back({(u64)pr[W[i]], st.P});
            if (coverSearch(W, rhoW, need, resid, cand, usedP, out)) return true;
            out.resize(keep); usedP.pop_back();
            for (int i = 0; i < w; ++i) if (st.mask >> i & 1) { ++need[i]; resid[i] = (int)((resid[i] + pr[W[i]] - invmodPrime(st.P, pr[W[i]])) % pr[W[i]]); }
        }
        return false;
    }
    // star search for a shape without big-big edges; d[i] = multiplicity of pr[i]
    bool starCover(const vector<int>& d, const vector<int>& rhoAll, vector<pair<u64, u64>>& out, long long& nCand) const {
        vector<int> W, rhoW;
        for (int i = 0; i < m; ++i) if (d[i] > 0) { W.push_back(i); rhoW.push_back(rhoAll[i]); }
        int w = (int)W.size();
        vector<Star> cand;
        for (uint32_t mask = 1; mask < (1u << w); ++mask) {
            int k = __builtin_popcount(mask);
            if (k < 2 || k > maxStar) continue;       // a big prime has >= 2 neighbours; star-size lemma
            u64 D = 1; for (int i = 0; i < w; ++i) if (mask >> i & 1) D *= (u64)pr[W[i]];
            u64 n = 0; for (int i = 0; i < w; ++i) if (mask >> i & 1) n += D / (u64)pr[W[i]];
            u64 r = n; for (int i = 0; i < m; ++i) while (r % pr[i] == 0) r /= pr[i];   // factors <= SB are irrelevant
            vector<u64> fs; factorInto(r, fs); sort(fs.begin(), fs.end()); fs.erase(unique(fs.begin(), fs.end()), fs.end());
            for (u64 P : fs) {
                bool ok = true;                          // q with d_q = 1 must be fixed by P alone
                for (int i = 0; i < w && ok; ++i)
                    if ((mask >> i & 1) && d[W[i]] == 1) {
                        u64 q = pr[W[i]];
                        if ((invmodPrime(P, q) + (u64)rhoW[i]) % q != 0) ok = false;
                    }
                if (ok) cand.push_back(Star{P, mask});
            }
        }
        nCand += (long long)cand.size();
        vector<int> need(w), resid(w, 0); for (int i = 0; i < w; ++i) need[i] = d[W[i]];
        vector<u64> usedP;
        return coverSearch(W, rhoW, need, resid, cand, usedP, out);
    }
    struct CompletionResult { bool solution = false, unresolved = false; long long shapes = 0, shapesAlive = 0, cand = 0;
                              vector<pair<u64, u64>> bigEdges; string note; };
    // U: bitmask of unsatisfied primes (indices), rhoAll[i] = full core residue, c = |C|,
    // su = upper bound for the core sum (fixed point).
    CompletionResult complete(uint32_t U, const vector<int>& rhoAll, int c, u128 su) const {
        CompletionResult R;
        int e = __builtin_popcount(U);
        int slack = KT - c - e;
        u128 Zlo = su >= ONE ? 0 : ONE - su;          // lower bound for Z = 1 - sum_C
        vector<u128> single(m, 0);
        for (int i = 0; i < m; ++i) if (U >> i & 1) single[i] = recipUp((u64)pr[i] * pminFor(i, rhoAll[i]));
        auto multiVal = [&](int i, int dq) { u128 v = 0; for (int k = 0; k < dq; ++k) v += recipUp((u64)pr[i] * bigList[k]); return v; };
        vector<int> d(m, 0);
        // recursive enumeration of shapes
        function<void(int, int, u128)> rec = [&](int i, int used, u128 ub) {
            if (R.solution || R.unresolved) return;
            if (i == m) {
                if ((rhoAll[0] + d[0]) % 2 != 0) return;   // (iii) parity at 2 (rhoAll[0]=0 if 2 not in U)
                for (int nbb = 0; used + nbb <= slack; ++nbb) {
                    ++R.shapes;
                    u128 tot = ub + (u128)nbb * recipUp(bigList[0] * bigList[1]);
                    if (tot < Zlo) continue;                   // (iv)
                    ++R.shapesAlive;
                    if (nbb > 0) {
                        R.unresolved = true;
                        R.note = "shape with " + to_string(nbb) + " big-big edge(s) not excluded";
                        return;
                    }
                    vector<pair<u64, u64>> out;
                    if (starCover(d, rhoAll, out, R.cand)) { R.solution = true; R.bigEdges = out; return; }
                }
                return;
            }
            if (U >> i & 1) {
                d[i] = 1; rec(i + 1, used, ub + single[i]);
                for (int dq = 2; used + dq - 1 <= slack; ++dq) { d[i] = dq; rec(i + 1, used + dq - 1, ub + multiVal(i, dq)); }
            } else {
                d[i] = 0; rec(i + 1, used, ub);
                for (int dq = 2; used + dq <= slack; ++dq) { d[i] = dq; rec(i + 1, used + dq, ub + multiVal(i, dq)); }
            }
            d[i] = 0;
        };
        rec(0, 0, 0);
        return R;
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
            if (e == 0) {                                              // C alone satisfies (*)
                lock_guard<mutex> g(E.mx); E.endStates++;
                if (c > 0) E.solutions.push_back(T);
                return;
            }
            vector<int> rhoAll(E.m, 0);
            for (int q = 0; q < E.m; ++q) if (U >> q & 1) rhoAll[q] = rho[q];
            CompletionResult R = E.complete(U, rhoAll, c, su);
            lock_guard<mutex> g(E.mx);
            E.endStates++;
            if (c + e == E.KT) E.endTight++;
            E.shapesTried += R.shapes; E.shapesAlive += R.shapesAlive; E.starCands += R.cand;
            if (R.shapesAlive) E.coresWithShape++;
            if (R.unresolved) {
                E.unresolved++;
                string s = "c=" + to_string(c) + " U={";
                for (int q = 0; q < E.m; ++q) if (U >> q & 1) s += " " + to_string(E.pr[q]) + ":" + to_string(rho[q]);
                s += " } " + R.note; E.unresolvedList.push_back(s);
            }
            if (R.solution) { for (auto& b : R.bigEdges) T.push_back(b); E.solutions.push_back(T); }
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
    int splitPrime = 61;  // --split p : level (prime) at which work is distributed over threads
    for (int a = 1; a < argc; ++a) {
        if (!strcmp(argv[a], "--selftest")) selftest = true;
        else if (!strcmp(argv[a], "--skip-main")) runMain = false;          // (testing aid)
        else if (!strcmp(argv[a], "--star-unit-test")) { selftest = true; onlyC = true; }
        else if (!strcmp(argv[a], "--budget") && a + 1 < argc) budget = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--split") && a + 1 < argc) splitPrime = atoi(argv[++a]);
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
        E.run(threads, splitPrime);
        printf("search nodes           : %lld\n", (long long)E.nodes);
        printf("cores passing all tests: %lld (of which |C|+|U| = %d: %lld)\n", E.endStates, budget, E.endTight);
        printf("completion shapes      : %lld tried, %lld pass parity+value (in %lld cores), %lld candidate stars\n",
               E.shapesTried, E.shapesAlive, E.coresWithShape, E.starCands);
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
            // (c1) S = primes <= 53: only 59 is big, tight case (|C|+|U| = 47).
            // (c2) S = primes <= 43: 47 and 59 are big and 2 has two big neighbours (excess 2).
            for (int sb : {53, 43}) {
                Engine Z(sb, 47, true);
                vector<int> rhoAll(Z.m, 0); int coreSize = 0; u128 su = 0;
                auto idx = [&](u64 p) { for (int i = 0; i < Z.m; ++i) if ((u64)Z.pr[i] == p) return i; return -1; };
                for (auto& e : K) if ((int)e.second <= sb) {
                    ++coreSize; su += recipUp(e.first * e.second);
                    int a = idx(e.first), b = idx(e.second);
                    rhoAll[a] = (int)((rhoAll[a] + invmodPrime(e.second, e.first)) % e.first);
                    rhoAll[b] = (int)((rhoAll[b] + invmodPrime(e.first, e.second)) % e.second);
                }
                uint32_t Um = 0; for (int i = 0; i < Z.m; ++i) if (rhoAll[i]) Um |= 1u << i;
                printf("S = primes <= %d: core size %d, |U| = %d, U =", sb, coreSize, __builtin_popcount(Um));
                for (int i = 0; i < Z.m; ++i) if (Um >> i & 1) printf(" %d", Z.pr[i]);
                printf("\n");
                Engine::CompletionResult R = Z.complete(Um, rhoAll, coreSize, su);
                printf("  completion found: %s ->", R.solution ? "yes" : "NO");
                for (auto& b : R.bigEdges) printf(" %llu*%llu", b.first, b.second);
                printf("\n");
            }
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
