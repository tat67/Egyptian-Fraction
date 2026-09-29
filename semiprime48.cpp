// semiprime48.cpp
//
// Problem.  P = { p*q : p < q primes }.  Find ALL T subset of P with |T| = 48 and
// sum_{n in T} 1/n = 1, verify each exactly, and prove that the list is complete.
//
// Integer/rational arithmetic only: no float, double or long double anywhere.  Bounds on sums
// of reciprocals use 96-bit fixed point with directed rounding (upper bounds rounded up,
// lower bounds rounded down); every solution is verified with exact big-integer rationals.
//
// Method (README48.md has the proofs).  The framework is the one of semiprime47.cpp:
//  1. H_48 < 2, so for |T| <= 48:  sum = 1  <=>  sum is an integer  <=>  for every prime p,
//     sum_{q in N(p)} q^{-1} == 0 (mod p)                                               (*)
//     where N(p) = { q : pq in T } (T viewed as a graph on primes).
//  2. S = primes <= 73, "big" primes >= 79.  C = elements of T with both factors in S (core),
//     G = the rest.  rho(q) = core residue at q, U = { q in S : rho(q) != 0 }.
//     |G| >= |U|, so |C| + |U| <= K (K = 48 is the budget).
//  3. Step 1: enumerate every core C with |C| + |U| <= K and
//        sum(C) <= 1   and   sum(C) + sum_{q in U} 1/(79q) + V(K - |C| - |U|) >= 1.
//     NEW: besides the pruning bounds of semiprime47.cpp, every node of the depth-first search
//     is tested with a Lagrangian "loss" bound that takes the congruences (*) of the primes
//     that are not yet decided into account (README48.md, section 3).  It is a relaxation of the
//     final test, so the set of cores found is exactly the same as before; the search tree is
//     ~10^4 times smaller.
//  4. Step 2 (completion): for every core find ALL big parts G with sum(G) = 1 - sum(C) and
//     |G| <= K - |C|.  Shapes (d_q, nbb) are filtered by the excess, parity and value tests;
//     nbb = 0: stars P | n(A), all exact covers;  nbb = 1: one two-prime component, solved by a
//     divisor equation;  nbb >= 2: reported as unresolved (the run shows that none survives).
//     All star arithmetic is done in 128 bits (stars have up to K - 36 = 12 neighbours).
//  5. Every solution is checked: distinct squarefree semiprimes (factors proved prime), exact
//     sum 1.  The search covers every T with |T| <= K, so the run also re-finds the 23 known
//     47-element solutions (a built-in consistency check); the 48-element ones are the answer.
//
// Usage: ./semiprime48 [threads] [--budget K] [--selftest] [--split p] [--dump cores.txt]
// ---------------------------------------------------------------------------------------

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <functional>
#include <map>
#include <mutex>
#include <numeric>
#include <set>
#include <string>
#include <thread>
#include <unordered_map>
#include <vector>

using namespace std;
typedef unsigned long long u64;
typedef unsigned __int128 u128;
typedef __int128 i128;

// ============================ integer utilities =======================================
static u64 mulmod(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }
static u64 powmod(u64 a, u64 e, u64 m) {
    u64 r = 1 % m; a %= m;
    while (e) { if (e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; }
    return r;
}
// deterministic Miller-Rabin for all 64-bit integers (bases 2..37)
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
static u128 mulmod128(u128 a, u128 b, u128 mod) {        // a*b mod m for any m < 2^127
    if (!(mod >> 64)) return (u128)mulmod((u64)(a % mod), (u64)(b % mod), (u64)mod);
    u128 r = 0; a %= mod; b %= mod;
    while (b) {
        if (b & 1) { r += a; if (r >= mod) r -= mod; }
        b >>= 1;
        if (b) { a += a; if (a >= mod) a -= mod; }
    }
    return r;
}
static u128 powmod128(u128 a, u128 e, u128 m) {
    u128 r = 1 % m; a %= m;
    while (e) { if (e & 1) r = mulmod128(r, a, m); a = mulmod128(a, a, m); e >>= 1; }
    return r;
}
// Miller-Rabin with the first 13 prime bases: deterministic for n < psi_13 = 3317044064679887385961981
// (Sorenson-Webster).  Returns 1 = prime (proved), 0 = composite, 2 = probable prime (n >= psi_13).
static const u128 PSI13 = (u128)3317044064679ull * (u128)1000000000000ull + (u128)887385961981ull;
static int isPrime128(u128 n) {
    if (!(n >> 64)) return isPrime64((u64)n) ? 1 : 0;
    if (n >> 126) return 2;                               // outside the range of mulmod128 (never occurs)
    static const u64 bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41};
    for (u64 p : bases) if (n % p == 0) return 0;
    u128 d = n - 1; int s = 0; while (!(d & 1)) { d >>= 1; ++s; }
    for (u64 a : bases) {
        u128 x = powmod128(a, d, n);
        if (x == 1 || x == n - 1) continue;
        bool comp = true;
        for (int r = 1; r < s; ++r) { x = mulmod128(x, x, n); if (x == n - 1) { comp = false; break; } }
        if (comp) return 0;
    }
    return n < PSI13 ? 1 : 2;
}
static u128 gcd128(u128 a, u128 b) { while (b) { u128 r = a % b; a = b; b = r; } return a; }
static u128 rhoFactor128(u128 n) {                       // a nontrivial factor of an odd composite n
    for (u128 c = 1;; ++c) {
        u128 x = 2, y = 2, d = 1;
        auto f = [&](u128 v) { u128 t = mulmod128(v, v, n) + c; return t >= n ? t - n : t; };
        while (d == 1) { x = f(x); y = f(f(y)); d = gcd128(x > y ? x - y : y - x, n); }
        if (d != n) return d;
    }
}
// prime factorisation (with multiplicity); every factor is certified prime unless *probable is set
static void factor128(u128 n, vector<u128>& out, bool* probable) {
    static const int tp[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73};
    for (int p : tp) while (n % p == 0) { out.push_back(p); n /= p; }
    vector<u128> st{n};
    while (!st.empty()) {
        u128 x = st.back(); st.pop_back();
        if (x == 1) continue;
        int pp = isPrime128(x);
        if (pp) { if (pp == 2 && probable) *probable = true; out.push_back(x); continue; }
        u128 d = rhoFactor128(x); st.push_back(d); st.push_back(x / d);
    }
    sort(out.begin(), out.end());
}
static u64 invmodPrime(u64 a, u64 p) { return powmod(a % p, p - 2, p); }   // p prime, p !| a
static vector<int> primesUpTo(int n) {
    vector<char> c(n + 1, 1); vector<int> r;
    for (int i = 2; i <= n; ++i) if (c[i]) { r.push_back(i); for (long long j = (long long)i * i; j <= n; j += i) c[j] = 0; }
    return r;
}
static string u128str(u128 x) {
    if (!x) return "0";
    string s; while (x) { s += char('0' + (int)(x % 10)); x /= 10; }
    reverse(s.begin(), s.end()); return s;
}
// overflow-checked multiplication
static bool mulOK(u128 a, u128 b, u128& out) {
    if (a && b > ~(u128)0 / a) return false;
    out = a * b; return true;
}

// ----- 96-bit fixed point: x is represented by an integer X ~ x * 2^96 -----
static const int FP = 96;
static const u128 ONE = (u128)1 << FP;
static inline u128 recipUp(u128 n) { return (ONE + n - 1) / n; }   // >= 2^96/n
static inline u128 recipLo(u128 n) { return ONE / n; }             // <= 2^96/n
static string fpToString(u128 x) {                                  // 6 decimals, truncated
    u128 ip = x >> FP; u128 frac = x & (ONE - 1);
    u128 f6 = (frac * 1000000) >> FP;
    char buf[64]; snprintf(buf, sizeof buf, "%llu.%06llu", (u64)ip, (u64)f6); return buf;
}

// ----- minimal arbitrary precision natural numbers (base 2^32) -----
struct BigNat {
    vector<uint32_t> d;   // little endian, no leading zeros
    BigNat(u64 v = 0) { while (v) { d.push_back((uint32_t)v); v >>= 32; } }
    void mulSmall(uint32_t m) {
        if (m == 0) { d.clear(); return; }
        u64 carry = 0;
        for (auto& x : d) { u64 t = (u64)x * m + carry; x = (uint32_t)t; carry = t >> 32; }
        if (carry) d.push_back((uint32_t)carry);
    }
    void mul(const BigNat& o) {
        vector<uint32_t> r(d.size() + o.d.size() + 1, 0);
        for (size_t i = 0; i < d.size(); ++i) {
            u64 carry = 0;
            for (size_t j = 0; j < o.d.size(); ++j) {
                u64 t = (u64)d[i] * o.d[j] + r[i + j] + carry; r[i + j] = (uint32_t)t; carry = t >> 32;
            }
            size_t k = i + o.d.size();
            while (carry) { u64 t = (u64)r[k] + carry; r[k] = (uint32_t)t; carry = t >> 32; ++k; }
        }
        while (!r.empty() && r.back() == 0) r.pop_back();
        d.swap(r);
    }
    static BigNat of128(u128 v) { BigNat b; while (v) { b.d.push_back((uint32_t)v); v >>= 32; } return b; }
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
typedef pair<u128, u128> Elem;                 // an element p*q of P, stored as (p, q) with p < q
// exact test sum_{(p,q) in T} 1/(pq) == 1: common denominator = product of the distinct primes
static bool exactSumIsOne(const vector<Elem>& T) {
    set<u128> ps; for (auto& e : T) { ps.insert(e.first); ps.insert(e.second); }
    BigNat den(1); for (u128 p : ps) den.mul(BigNat::of128(p));
    BigNat num(0);
    for (auto& e : T) {
        BigNat t(1);
        for (u128 p : ps) if (p != e.first && p != e.second) t.mul(BigNat::of128(p));
        num.add(t);
    }
    return BigNat::cmp(num, den) == 0;
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
    int KT;          // budget: T has at most KT elements, so |C| + |U| <= KT
    int LOWN = 8;    // smallest LOWN primes handled through precomputed residue tables
    u64 thetaDen;    // Lagrange multiplier theta = 1/thetaDen of the loss bound
    int AD = 12;     // edge {pr[a],pr[b]}, a < b: the larger endpoint receives the share SHN[a]/AD of the
    vector<int> SHN; // weight, the smaller one the rest (tuned values; any values in [0,AD] are valid)
    // data
    vector<int> pr; int m = 0; u64 bigMin = 0;
    vector<vector<int>> inv;                    // inv[a][b] = pr[b]^{-1} mod pr[a]
    vector<vector<u128>> EU, EL;                // EU[j][i] = up(1/(pr[j]*pr[i])), EL = lo
    vector<vector<u128>> MX;                    // MX[j][R]
    vector<vector<vector<u128>>> BT;            // BT[j][i][R]
    struct LowSub { uint32_t mask; int cnt; u128 u, l; };
    vector<vector<vector<LowSub>>> LOWL;        // LOWL[j][residue]
    vector<u128> GV;                            // GV[j] = up(1/(bigMin*pr[j])): value of the U-edge at pr[j]
    vector<u128> VB;                            // VB[x] = sum of the x largest 1/n, n in P with a factor >= bigMin
    // loss bound (README48.md, section 3)
    i128 TH = 0, VTH = 0;                       // TH = theta in fixed point, VTH = max_x (VB[x] - x*TH)
    vector<vector<vector<i128>>> LOC;           // LOC[j][k][r]: local bound of pr[k], candidates pr[0..j] \ {pr[k]}
    vector<vector<vector<i128>>> TOPT;          // TOPT[j][i][t]: local bound of pr[j], candidates pr[0..i-1]
    // results
    mutex mx;
    atomic<long long> nodes{0};
    long long endStates = 0, endTight = 0, unresolved = 0;
    long long shapesTried = 0, shapesAlive = 0, starCands = 0, coresWithShape = 0, probablePrimes = 0;
    long long aliveByNbb[3] = {0, 0, 0};
    set<vector<Elem>> solutionSet;              // all solutions found (sorted element lists)
    FILE* dumpFile = nullptr;                   // optional: record every core that survives Step 1
    bool runStep2 = true;                       // false: Step 1 only (used by the validation harness)
    vector<string> unresolvedList;
    int maxStar = 0;                            // largest possible number of S-neighbours of a big prime
    vector<u64> bigList;                        // the first primes > SB
    u128 Dall = 1;                              // product of all primes of S (a common denominator)

    static i128 ceilDiv(i128 a, i128 d) { return a >= 0 ? (a + d - 1) / d : -((-a) / d); }

    Engine(int sb, int kt, u64 thDen = 145) : SB(sb), KT(kt), thetaDen(thDen) {
        pr = primesUpTo(SB); m = (int)pr.size();
        SHN.assign(m, 8);
        const int tuned[6] = {12, 11, 11, 10, 10, 9};                  // smaller endpoint 2, 3, 5, 7, 11, 13
        for (int i = 0; i < 6 && i < m; ++i) SHN[i] = tuned[i];
        vector<int> big = primesUpTo(4 * SB + 100);
        for (int p : big) if (p > SB) { bigMin = p; break; }
        inv.assign(m, vector<int>(m, 0));
        for (int a = 0; a < m; ++a) for (int b = 0; b < m; ++b) if (a != b) inv[a][b] = (int)invmodPrime(pr[b], pr[a]);
        // V(x): the x largest reciprocals of semiprimes having a prime factor > SB
        {
            u64 lim = 60ull * bigMin;
            vector<int> ps = primesUpTo((int)(lim / 2 + 1)); vector<u64> bs;
            for (size_t a = 0; a < ps.size(); ++a)
                for (size_t b = a + 1; b < ps.size() && (u64)ps[a] * ps[b] <= lim; ++b)
                    if (ps[b] > SB) bs.push_back((u64)ps[a] * ps[b]);
            sort(bs.begin(), bs.end());
            VB.assign(KT + 2, 0);
            for (int x = 1; x <= KT + 1; ++x) VB[x] = VB[x - 1] + recipUp(bs[x - 1]);
        }
        GV.resize(m); for (int j = 0; j < m; ++j) GV[j] = recipUp((u128)bigMin * pr[j]);
        for (int p : primesUpTo(20 * SB + 1000)) if (p > SB && bigList.size() < 64) bigList.push_back((u64)p);
        for (int p : pr) Dall *= (u128)p;
        // Star-size lemma: a big prime with d neighbours, all in S, contributes at most
        // (1/bigMin) * (sum of the d largest 1/q, q in S); the other <= KT-d elements of T
        // contribute at most H_{KT-d}.  If the total is < 1, such a star cannot occur.
        {
            SemiprimeList sp(4000);
            maxStar = 0;
            for (int d = 1; d <= m && d <= KT; ++d) {
                u128 z = 0; for (int i = 0; i < d; ++i) z += recipUp((u128)bigMin * pr[i]);
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
                for (int x = 0; x <= R; ++x) { u128 val = M[x] + VB[R - x]; if (val > best) best = val; }
                MX[j][R] = best;
            }
        }
        EU.assign(m, {}); EL.assign(m, {});
        for (int j = 0; j < m; ++j) {
            EU[j].resize(j); EL[j].resize(j);
            for (int i = 0; i < j; ++i) { EU[j][i] = recipUp((u128)pr[j] * pr[i]); EL[j][i] = recipLo((u128)pr[j] * pr[i]); }
        }
        // BT[j][i][R] = max_t ( sum_{k<t} EU[j][k] + MX[j][R-t] ), t <= min(i,R)
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
        buildLossTables();
    }

    // ---------------- the loss bound (README48.md, section 3) ----------------
    // For theta >= 0 and any final state:  value = sum_C 1/n + sum_U GV + VB[K-|C|-|U|]
    //   <= K*theta + VTH + sum_{e in C} w(e) + sum_{q in U} (GV_q - theta),   w(e) = up(1/e) - theta.
    // The weight of an undecided edge {a,b} (a < b) is split: share SHN[a]/AD to b, the rest to a
    // (each share rounded up).  The sum over the undecided part is then at most the sum, over the
    // undecided primes q, of the best "local" configuration of q: either q in U (value GV_q - theta
    // plus all positive shares) or a set X of undecided neighbours with the congruence (*) at q.
    void buildLossTables() {
        TH = (i128)(ONE / thetaDen);
        VTH = 0;
        for (int r = 0; r <= KT; ++r) { i128 v = (i128)VB[r] - (i128)r * TH; if (v > VTH) VTH = v; }
        const i128 NEG = -((i128)1 << 120);
        auto wv = [&](int a, int b) { return (i128)recipUp((u128)pr[a] * pr[b]) - TH; };
        LOC.assign(m, {}); TOPT.assign(m, {});
        for (int j = 0; j < m; ++j) {
            LOC[j].assign(j + 1, {});
            for (int k = 0; k <= j; ++k) {
                int q = pr[k];
                vector<i128> best(q, NEG); best[0] = 0; i128 pos = 0;   // best[s]: max share sum with residue s
                for (int x = 0; x <= j; ++x) if (x != k) {
                    i128 sh = ceilDiv(wv(k, x) * (k > x ? SHN[x] : AD - SHN[k]), AD);
                    if (sh > 0) pos += sh;
                    int iv = inv[k][x]; vector<i128> nb = best;
                    for (int r = 0; r < q; ++r) if (best[r] > NEG) { int r2 = (r + iv) % q; if (best[r] + sh > nb[r2]) nb[r2] = best[r] + sh; }
                    best.swap(nb);
                }
                i128 uo = (i128)GV[k] - TH + pos;
                LOC[j][k].assign(q, 0);
                for (int r = 0; r < q; ++r) { i128 v = best[(q - r) % q]; LOC[j][k][r] = v > uo ? v : uo; }
            }
            int p = pr[j];
            TOPT[j].assign(j + 1, vector<i128>(p, 0));
            vector<i128> best(p, NEG); best[0] = 0; i128 pos = 0;
            for (int i = 0; i <= j; ++i) {
                i128 uo = (i128)GV[j] - TH + pos;
                for (int t = 0; t < p; ++t) { i128 v = best[(p - t) % p]; TOPT[j][i][t] = v > uo ? v : uo; }
                if (i == j) break;
                i128 sh = ceilDiv(wv(j, i) * SHN[i], AD);
                if (sh > 0) pos += sh;
                int iv = inv[j][i]; vector<i128> nb = best;
                for (int r = 0; r < p; ++r) if (best[r] > NEG) { int r2 = (r + iv) % p; if (best[r] + sh > nb[r2]) nb[r2] = best[r] + sh; }
                best.swap(nb);
            }
            for (int t = 0; t < p; ++t)
                if (TOPT[j][j][t] != LOC[j][j][t]) { fprintf(stderr, "internal error: loss tables disagree\n"); exit(1); }
        }
    }

    // ---------------- completion of a core by big primes (README48.md, section 4) ----------------
    // A completion G of a core C is a set of <= KT-|C| elements of P, each with a prime factor
    // > SB, such that sum(C) + sum(G) = 1 (equivalently C u G satisfies (*) everywhere).
    // Shape: d_q = number of big neighbours of q in S, nbb = number of big-big edges.
    //   (i)   d_q >= 1 on U, d_q in {0} u [2,inf) off U;
    //   (ii)  excess nbb + sum_U (d_q-1) + sum_{not U} d_q = |G| - |U| <= KT - |C| - |U|;
    //   (iii) parity at 2: rho(2) + d_2 even;
    //   (iv)  value upper bound >= 1 - sum(C).
    // nbb = 0 : all big primes are stars; ALL exact covers are enumerated.
    // nbb = 1 : one component {P1,P2} (edge P1P2) plus stars; solved exactly through
    //           (t P1 - a1 b2)(t P2 - a2 b1) = b1 b2 (t + a1 a2),  t = Z_K b1 b2.
    // nbb >= 2: reported as unresolved (the run shows that no such shape survives).
    u64 pminFor(int qi, int r) const {         // least prime P > SB with P == (-r)^{-1} mod pr[qi]
        u64 q = pr[qi]; u64 a = invmodPrime((q - (u64)r % q) % q, q);
        u64 P = a; while (P <= (u64)SB || !isPrime64(P)) P += q;
        return P;
    }
    typedef unordered_map<uint32_t, vector<u128>> StarCache;   // A (bitmask over pr) -> big prime factors of n(A)
    struct Star { u128 P; uint32_t mask; u128 valNum; };      // value of the star = valNum / Dall
    struct Solution { vector<Elem> big; };
    struct CompletionResult { vector<Solution> sols; bool unresolved = false; long long shapes = 0, shapesAlive = 0, cand = 0;
                              long long probablePrimes = 0; long long aliveNbb[3] = {0, 0, 0}; string note; };
    // all prime factors > SB of n(A) = sum_{q in A} prod(A)/q (each certified prime; A has <= 21 elements)
    const vector<u128>& bigFactors(uint32_t Amask, StarCache& cache, CompletionResult& R) const {
        auto it = cache.find(Amask);
        if (it != cache.end()) return it->second;
        u128 D = 1, n = 0;
        for (int i = 0; i < m; ++i) if (Amask >> i & 1) D *= (u128)pr[i];
        for (int i = 0; i < m; ++i) if (Amask >> i & 1) n += D / (u128)pr[i];
        vector<u128> fs; bool prob = false; factor128(n, fs, &prob);
        if (prob) R.probablePrimes++;
        vector<u128> out;
        for (u128 f : fs) if (f > (u128)SB && (out.empty() || out.back() != f)) out.push_back(f);
        return cache[Amask] = out;
    }
    // all covers of the multiplicities need[] by distinct stars, candidates taken in increasing
    // index order (so every family is produced once)
    void allCovers(int w, vector<int>& need, const vector<Star>& cand, size_t start,
                   vector<int>& chosen, vector<vector<int>>& out) const {
        bool done = true; for (int v : need) if (v) { done = false; break; }
        if (done) { out.push_back(chosen); return; }
        for (size_t idx = start; idx < cand.size(); ++idx) {
            const Star& st = cand[idx];
            bool ok = true;
            for (int i = 0; i < w && ok; ++i) if ((st.mask >> i & 1) && need[i] == 0) ok = false;
            for (int c : chosen) if (cand[c].P == st.P) ok = false;
            if (!ok) continue;
            for (int i = 0; i < w; ++i) if (st.mask >> i & 1) --need[i];
            chosen.push_back((int)idx);
            allCovers(w, need, cand, idx + 1, chosen, out);
            chosen.pop_back();
            for (int i = 0; i < w; ++i) if (st.mask >> i & 1) ++need[i];
        }
    }
    // candidate stars on W: A subset of W, 2 <= |A| <= maxStar, P > SB prime factor of n(A),
    // P == (-rho(q))^{-1} mod q for every q in A with d_q = 1
    vector<Star> starCandidates(const vector<int>& W, const vector<int>& d, const vector<int>& rhoAll,
                                StarCache& cache, CompletionResult& R) const {
        int w = (int)W.size(); vector<Star> cand;
        for (uint32_t mask = 1; mask < (1u << w); ++mask) {
            int k = __builtin_popcount(mask);
            if (k < 2 || k > maxStar) continue;
            uint32_t Amask = 0; u128 D = 1;
            for (int i = 0; i < w; ++i) if (mask >> i & 1) { Amask |= 1u << W[i]; D *= (u128)pr[W[i]]; }
            u128 n = 0; for (int i = 0; i < w; ++i) if (mask >> i & 1) n += D / (u128)pr[W[i]];
            for (u128 P : bigFactors(Amask, cache, R)) {
                bool ok = true;
                for (int i = 0; i < w && ok; ++i)
                    if ((mask >> i & 1) && d[W[i]] == 1) {
                        u64 q = pr[W[i]];
                        if ((invmodPrime((u64)(P % q), q) + (u64)rhoAll[W[i]]) % q != 0) ok = false;
                    }
                if (!ok) continue;
                cand.push_back(Star{P, mask, (n / P) * (Dall / D)});   // = Dall * value(star), exact
            }
        }
        return cand;
    }
    // U: bitmask of unsatisfied primes, rhoAll = full core residues, c = |C|, su = upper
    // bound of the core sum (fixed point), zNum = Dall * (1 - sum C) exactly.
    CompletionResult complete(uint32_t U, const vector<int>& rhoAll, int c, u128 su, u128 zNum, StarCache& cache) const {
        CompletionResult R;
        int e = __builtin_popcount(U);
        int slack = KT - c - e;
        if (slack < 0) return R;
        u128 Zlo = su >= ONE ? 0 : ONE - su;          // lower bound of 1 - sum(C)
        vector<u128> single(m, 0);
        for (int i = 0; i < m; ++i) if (U >> i & 1) single[i] = recipUp((u128)pr[i] * pminFor(i, rhoAll[i]));
        auto multiVal = [&](int i, int dq) { u128 v = 0; for (int k = 0; k < dq; ++k) v += recipUp((u128)pr[i] * bigList[k]); return v; };
        vector<int> d(m, 0);
        function<void(int, int, u128)> rec = [&](int i, int used, u128 ub) {
            if (i == m) {
                if ((rhoAll[0] + d[0]) % 2 != 0) return;                     // (iii)
                for (int nbb = 0; used + nbb <= slack; ++nbb) {
                    ++R.shapes;
                    u128 tot = ub + (u128)nbb * recipUp((u128)bigList[0] * bigList[1]);
                    if (tot < Zlo) continue;                                 // (iv)
                    ++R.shapesAlive; R.aliveNbb[min(nbb, 2)]++;
                    if (nbb >= 2) {
                        R.unresolved = true;
                        R.note += " [shape with " + to_string(nbb) + " big-big edges]";
                        continue;
                    }
                    solveShape(d, nbb, rhoAll, zNum, cache, R);
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
    void solveShape(const vector<int>& d, int nbb, const vector<int>& rhoAll, u128 zNum, StarCache& cache, CompletionResult& R) const {
        vector<int> W; for (int i = 0; i < m; ++i) if (d[i] > 0) W.push_back(i);
        int w = (int)W.size();
        if (w > 20) { R.unresolved = true; R.note += " [too many attachments]"; return; }
        vector<Star> cand = starCandidates(W, d, rhoAll, cache, R);
        R.cand += (long long)cand.size();
        auto starElems = [&](const vector<int>& cv, Solution& S) {
            for (int id : cv) for (int i = 0; i < w; ++i) if (cand[id].mask >> i & 1) S.big.push_back({(u128)pr[W[i]], cand[id].P});
        };
        if (nbb == 0) {
            vector<int> need(w); for (int i = 0; i < w; ++i) need[i] = d[W[i]];
            vector<vector<int>> covers; vector<int> chosen;
            allCovers(w, need, cand, 0, chosen, covers);
            for (auto& cv : covers) {
                u128 s = 0; for (int id : cv) s += cand[id].valNum;
                if (s != zNum) continue;                                     // exact value check
                Solution S; starElems(cv, S); R.sols.push_back(S);
            }
            return;
        }
        // nbb == 1: attachment sets A1 (of P1) and A2 (of P2), both nonempty subsets of W
        auto fail = [&](const char* why) { R.unresolved = true; R.note += string(" [") + why + "]"; };
        for (uint32_t m1 = 1; m1 < (1u << w); ++m1)
            for (uint32_t m2 = m1; m2 < (1u << w); ++m2) {                  // unordered pair {A1, A2}
                vector<int> need(w); bool ok = true;
                for (int i = 0; i < w; ++i) {
                    need[i] = d[W[i]] - (int)(m1 >> i & 1) - (int)(m2 >> i & 1);
                    if (need[i] < 0) ok = false;
                }
                if (!ok) continue;
                vector<vector<int>> covers; vector<int> chosen;
                allCovers(w, need, cand, 0, chosen, covers);
                if (covers.empty()) continue;
                u128 b1 = 1, b2 = 1, a1 = 0, a2 = 0;
                for (int i = 0; i < w; ++i) { if (m1 >> i & 1) b1 *= pr[W[i]]; if (m2 >> i & 1) b2 *= pr[W[i]]; }
                for (int i = 0; i < w; ++i) { if (m1 >> i & 1) a1 += b1 / pr[W[i]]; if (m2 >> i & 1) a2 += b2 / pr[W[i]]; }
                u128 B, a1b2, a2b1, a1a2;
                if (!mulOK(b1, b2, B) || !mulOK(a1, b2, a1b2) || !mulOK(a2, b1, a2b1) || !mulOK(a1, a2, a1a2) ||
                    (a1b2 >> 126) || (a2b1 >> 126)) { fail("overflow"); continue; }
                u128 g = gcd128(B, Dall), Q = Dall / g;
                for (auto& cv : covers) {
                    u128 s = 0; for (int id : cv) s += cand[id].valNum;
                    if (s >= zNum) continue;
                    u128 zk = zNum - s;                                      // Z_K = zk / Dall
                    if (zk % Q != 0) continue;                               // t = Z_K * b1 * b2 must be an integer
                    u128 t, L, N;
                    if (!mulOK(zk / Q, B / g, t)) { fail("overflow"); continue; }
                    L = t + a1a2;
                    if (L < t || (L >> 100) || !mulOK(B, L, N) || (N >> 126)) { fail("large t"); continue; }
                    vector<u128> fs; bool prob = false; factor128(L, fs, &prob);
                    if (prob) { fail("probable prime in factorisation"); continue; }
                    for (int i = 0; i < w; ++i) { if (m1 >> i & 1) fs.push_back(pr[W[i]]); if (m2 >> i & 1) fs.push_back(pr[W[i]]); }
                    sort(fs.begin(), fs.end());
                    vector<pair<u128, int>> pe;
                    for (u128 p : fs) { if (!pe.empty() && pe.back().first == p) pe.back().second++; else pe.push_back({p, 1}); }
                    vector<u128> divs{1};
                    for (auto& x : pe) { size_t sz = divs.size(); u128 pk = 1;
                        for (int k = 1; k <= x.second; ++k) { pk *= x.first; for (size_t j = 0; j < sz; ++j) divs.push_back(divs[j] * pk); } }
                    for (u128 X : divs) {
                        u128 Y = N / X;
                        if ((X + a1b2) % t != 0 || (Y + a2b1) % t != 0) continue;
                        u128 P1 = (X + a1b2) / t, P2 = (Y + a2b1) / t;
                        if (P1 == P2 || P1 <= (u128)SB || P2 <= (u128)SB) continue;
                        bool dup = false; for (int id : cv) if (cand[id].P == P1 || cand[id].P == P2) dup = true;
                        if (dup) continue;
                        int pp1 = isPrime128(P1), pp2 = isPrime128(P2);
                        if (!pp1 || !pp2) continue;
                        if (pp1 == 2 || pp2 == 2) R.probablePrimes++;
                        Solution S; starElems(cv, S);
                        for (int i = 0; i < w; ++i) { if (m1 >> i & 1) S.big.push_back({(u128)pr[W[i]], P1}); if (m2 >> i & 1) S.big.push_back({(u128)pr[W[i]], P2}); }
                        S.big.push_back({min(P1, P2), max(P1, P2)});
                        R.sols.push_back(S);
                    }
                }
            }
    }

    // ---------------- Step 1: the depth-first search over the primes of S ----------------
    // Work distribution: every thread walks the (small) part of the tree above level splitJ in
    // the same deterministic order; the nodes at level splitJ are numbered 0,1,2,... and each
    // number is claimed by exactly one thread through a shared atomic ticket counter.
    atomic<long long> ticket{0};
    struct Worker {
        Engine& E; int splitJ; long long splitCounter = 0, myTicket = -1;
        // res[q]  : residue at q contributed by the core edges decided so far (edges to larger primes)
        // rho[q]  : full core residue of q, recorded when q is put into U
        vector<int> res, rho; vector<pair<int, int>> edges; uint32_t U = 0; u128 gz = 0; long long nodes = 0;
        vector<vector<int>> CH; vector<vector<i128>> MS;
        StarCache cache;
        Worker(Engine& e, int sj) : E(e), splitJ(sj) {
            res.assign(E.m, 0); rho.assign(E.m, 0); CH.assign(E.m, {}); MS.assign(E.m, vector<i128>(1u << E.LOWN, 0));
        }

        void endState(int c, u128 su) {
            int e = __builtin_popcount(U);
            if (su + gz + E.VB[E.KT - c - e] < ONE) return;           // value condition (section 2)
            vector<Elem> core;
            for (auto& x : edges) core.push_back({(u128)E.pr[x.first], (u128)E.pr[x.second]});
            if (E.dumpFile) {
                string line = "E " + to_string(c) + " " + to_string(e) + " U";
                for (int q = 0; q < E.m; ++q) if (U >> q & 1) line += " " + to_string(E.pr[q]) + ":" + to_string(rho[q]);
                line += " C";
                for (auto& x : core) line += " " + u128str(x.first * x.second);
                lock_guard<mutex> g(E.mx); fprintf(E.dumpFile, "%s\n", line.c_str());
            }
            if (!E.runStep2) { lock_guard<mutex> g(E.mx); E.endStates++; if (e > 0 && c + e == E.KT) E.endTight++; return; }
            if (e == 0) {                                              // C alone satisfies (*): sum(C) = 1
                lock_guard<mutex> g(E.mx); E.endStates++;
                if (c > 0) { sort(core.begin(), core.end()); E.solutionSet.insert(core); }
                return;
            }
            vector<int> rhoAll(E.m, 0);
            for (int q = 0; q < E.m; ++q) if (U >> q & 1) rhoAll[q] = rho[q];
            u128 sumNum = 0; for (auto& x : core) sumNum += E.Dall / (x.first * x.second);   // Dall * sum(C), exact
            u128 zNum = sumNum < E.Dall ? E.Dall - sumNum : 0;
            CompletionResult R = E.complete(U, rhoAll, c, su, zNum, cache);
            lock_guard<mutex> g(E.mx);
            E.endStates++;
            if (c + e == E.KT) E.endTight++;
            E.shapesTried += R.shapes; E.shapesAlive += R.shapesAlive; E.starCands += R.cand; E.probablePrimes += R.probablePrimes;
            for (int k = 0; k < 3; ++k) E.aliveByNbb[k] += R.aliveNbb[k];
            if (R.shapesAlive) E.coresWithShape++;
            if (R.unresolved) {
                E.unresolved++;
                string s = "c=" + to_string(c) + " U={";
                for (int q = 0; q < E.m; ++q) if (U >> q & 1) s += " " + to_string(E.pr[q]) + ":" + to_string(rho[q]);
                s += " }" + R.note; E.unresolvedList.push_back(s);
            }
            for (auto& S : R.sols) {
                vector<Elem> T = core;
                for (auto& b : S.big) T.push_back(b);
                sort(T.begin(), T.end());
                E.solutionSet.insert(T);
            }
        }
        // process prime pr[j]: SL = sum_{k<j} LOC[j][k][res[k]]
        void dfs(int j, int c, u128 su, u128 sl, i128 SL) {
            if (j == splitJ) {
                long long k = splitCounter++;
                if (myTicket < k) myTicket = E.ticket.fetch_add(1);
                if (myTicket != k) return;          // node k belongs to another thread
            }
            if (j < 0) { endState(c, su); return; }
            if (j == 0) {                                      // prime 2: no smaller primes left
                if (res[0] == 0) { dfs(-1, c, su, sl, 0); }
                else if (c + __builtin_popcount(U) + 1 <= E.KT) {
                    U |= 1; rho[0] = res[0]; gz += E.GV[0]; dfs(-1, c, su, sl, 0); U &= ~1u; gz -= E.GV[0];
                }
                return;
            }
            CH[j].clear();
            sub(j, j, 0, 0, c, su, sl, 0, 0, SL);
        }
        // choose the neighbours of pr[j] among pr[0..i-1]; high part explicit, low part by table.
        // modsum = inverse sum of the neighbours chosen so far, cnt = their number,
        // pu/pl = upper/lower bound of their reciprocal sum,
        // SL = sum_{i<=k<j} LOC[j-1][k][res'(k)] + sum_{k<i} LOC[j][k][res(k)]   (res' includes the choice)
        void sub(int j, int i, int modsum, int cnt, int c, u128 su, u128 sl, u128 pu, u128 pl, i128 SL) {
            ++nodes;
            int p = E.pr[j]; int L = min(j, E.LOWN);
            int e = __builtin_popcount(U);
            int R = E.KT - c - e - cnt; if (R < 0) return;
            if (sl + pl > ONE) return;                              // (P2) core sum must stay <= 1
            if (su + pu + gz + E.BT[j][i][R] < ONE) return;         // (P3) cannot reach 1 any more
            int t = (res[j] + modsum) % p;                          // residue of pr[j] so far
            // (P4) loss bound
            if ((i128)(su + pu + gz) + (i128)R * E.TH + E.VTH + E.TOPT[j][i][t] + SL < (i128)ONE) return;
            if (i == L) {
                int need = (p - t) % p;
                bool excOK = R >= 1 && (su + pu + gz + E.BT[j][L][R - 1] + E.GV[j] >= ONE);
                // the loss-bound contribution of the low primes as a function of the chosen subset
                i128 base = SL; i128 dd[32];
                for (int q = 0; q < L; ++q) {
                    int pq = E.pr[q];
                    i128 a = E.LOC[j][q][res[q]], b0 = E.LOC[j - 1][q][res[q]], b1 = E.LOC[j - 1][q][(res[q] + E.inv[q][j]) % pq];
                    base += b0 - a; dd[q] = b1 - b0;
                }
                vector<i128>& ms = MS[j]; ms[0] = 0;
                for (uint32_t mask = 1; mask < (1u << L); ++mask) ms[mask] = ms[mask & (mask - 1)] + dd[__builtin_ctz(mask)];
                for (int r0 = 0; r0 < p; ++r0) {
                    bool exc = (r0 != need);
                    if (exc && !excOK) continue;
                    for (auto& ls : E.LOWL[j][r0]) {
                        int cc = cnt + ls.cnt; int RR = E.KT - c - e - cc - (exc ? 1 : 0); if (RR < 0) continue;
                        u128 nu = pu + ls.u, nl = pl + ls.l;
                        if (sl + nl > ONE) continue;
                        u128 g2 = gz + (exc ? E.GV[j] : 0);
                        if (su + nu + g2 + E.MX[j][RR] < ONE) continue;
                        i128 SLc = base + ms[ls.mask];                  // = sum_{k<j} LOC[j-1][k][new res(k)]
                        if ((i128)(su + nu + g2) + (i128)RR * E.TH + E.VTH + SLc < (i128)ONE) continue;
                        vector<int>& ch = CH[j]; size_t b = ch.size();
                        for (int q = 0; q < L; ++q) if (ls.mask >> q & 1) ch.push_back(q);
                        for (int q : ch) { res[q] = (res[q] + E.inv[q][j]) % E.pr[q]; edges.push_back({q, j}); }
                        // full residue of pr[j] = t + r0 = r0 - need (mod p)
                        if (exc) { U |= 1u << j; gz = g2; rho[j] = (r0 - need + p) % p; }
                        dfs(j - 1, c + cc, su + nu, sl + nl, SLc - E.LOC[j - 1][j - 1][res[j - 1]]);
                        if (exc) { U &= ~(1u << j); gz -= E.GV[j]; }
                        for (int q : ch) { res[q] = (res[q] + E.pr[q] - E.inv[q][j]) % E.pr[q]; edges.pop_back(); }
                        ch.resize(b);
                    }
                }
                return;
            }
            int q = i - 1, pq = E.pr[q];
            i128 a = E.LOC[j][q][res[q]];
            CH[j].push_back(q);                                     // pr[q] is a neighbour of pr[j]
            sub(j, i - 1, (modsum + E.inv[j][q]) % p, cnt + 1, c, su, sl, pu + E.EU[j][q], pl + E.EL[j][q],
                SL - a + E.LOC[j - 1][q][(res[q] + E.inv[q][j]) % pq]);
            CH[j].pop_back();                                       // pr[q] is not
            sub(j, i - 1, modsum, cnt, c, su, sl, pu, pl, SL - a + E.LOC[j - 1][q][res[q]]);
        }
    };

    void run(int threads, int splitPrime) {
        int splitJ = -2;
        for (int j = 0; j < m; ++j) if (pr[j] == splitPrime) splitJ = j;
        i128 SL0 = 0; for (int k = 0; k < m - 1; ++k) SL0 += LOC[m - 1][k][0];
        vector<thread> th;
        for (int t = 0; t < threads; ++t)
            th.emplace_back([&]() {
                Worker w(*this, splitJ);
                w.dfs(m - 1, 0, 0, 0, SL0);
                nodes += w.nodes;
            });
        for (auto& x : th) x.join();
    }
};

// ======================================= main ===========================================
static string utcNow() {
    time_t t = time(nullptr); struct tm g; gmtime_r(&t, &g);
    char buf[64]; strftime(buf, sizeof buf, "%Y-%m-%d %H:%M:%S UTC", &g); return buf;
}
// full check of one solution: distinct elements p*q with p < q both (provably) prime, exact sum 1
static bool verifySolution(const vector<Elem>& T) {
    set<Elem> distinct(T.begin(), T.end());
    if (distinct.size() != T.size()) return false;
    for (auto& e : T) if (!(e.first < e.second) || isPrime128(e.first) != 1 || isPrime128(e.second) != 1) return false;
    return exactSumIsOne(T);
}

int main(int argc, char** argv) {
    int threads = (int)thread::hardware_concurrency(); if (threads <= 0) threads = 4;
    int splitPrime = 43, K = 48;
    bool selftest = false, runMain = true;
    const char* dumpPath = nullptr;
    for (int a = 1; a < argc; ++a) {
        if (!strcmp(argv[a], "--selftest")) selftest = true;
        else if (!strcmp(argv[a], "--skip-main")) runMain = false;
        else if (!strcmp(argv[a], "--split") && a + 1 < argc) splitPrime = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--dump") && a + 1 < argc) dumpPath = argv[++a];
        else if (!strcmp(argv[a], "--budget") && a + 1 < argc) K = atoi(argv[++a]);
        else threads = max(1, atoi(argv[a]));
    }
    if (K < 1 || K > 48) { printf("budget must be in 1..48\n"); return 1; }
    string startStr = utcNow();
    auto t0 = chrono::steady_clock::now();
    auto msecs = [&]() { return (long long)chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - t0).count(); };
    printf("start: %s\n", startStr.c_str());
    printf("budget K = %d (all T with |T| <= K and reciprocal sum 1 are found; the answer is |T| = K)\n\n", K);

    printf("=== Part 1: size lemma ===\n");
    SemiprimeList SP(2000);
    {
        auto Hcmp = [&](int k, u64 integer) {
            vector<Elem> T; for (int i = 0; i < k; ++i) T.push_back({SP.fac[i].first, SP.fac[i].second});
            set<u128> ps; for (auto& e : T) { ps.insert(e.first); ps.insert(e.second); }
            BigNat den(1); for (u128 p : ps) den.mul(BigNat::of128(p));
            BigNat num(0);
            for (auto& e : T) { BigNat t(1); for (u128 p : ps) if (p != e.first && p != e.second) t.mul(BigNat::of128(p)); num.add(t); }
            BigNat rhs = den; rhs.mulSmall((uint32_t)integer);
            return BigNat::cmp(num, rhs);
        };
        u128 h = 0; for (int i = 0; i < K; ++i) h += recipUp(SP.val[i]);
        printf("H_%d (sum of the reciprocals of the %d smallest elements of P) < %s ; exact check H_%d < 2: %s\n",
               K, K, fpToString(h).c_str(), K, Hcmp(K, 2) < 0 ? "yes" : "NO");
        printf("=> every T with |T| <= %d has 0 < sum < 2, so 'sum = 1' <=> 'sum is an integer' <=> (*) at every prime\n", K);
        if (!(Hcmp(K, 2) < 0)) return 1;
    }

    if (selftest) {
        printf("\n=== Self test: completion routine on planted big-prime structures ===\n");
        Engine Z(73, K);
        Engine::StarCache cache;
        auto idx = [&](u64 p) { for (int i = 0; i < Z.m; ++i) if ((u64)Z.pr[i] == p) return i; return -1; };
        // (1) a 47-term solution whose big part is a star at 3779 on {29,37,41}
        vector<u64> T1 = {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 86,
                          87, 91, 93, 95, 106, 111, 115, 123, 133, 155, 159, 161, 185, 203, 215, 253, 265, 583, 667, 731,
                          109591, 139823, 154939};
        vector<pair<u64, u64>> core;
        for (u64 n : T1) for (u64 p = 2; p * p <= n; ++p) if (n % p == 0) { if (n / p <= 73) core.push_back({p, n / p}); break; }
        vector<int> rhoAll(Z.m, 0); u128 su = 0, sumNum = 0;
        for (auto& e : core) {
            su += recipUp((u128)e.first * e.second); sumNum += Z.Dall / ((u128)e.first * e.second);
            int a = idx(e.first), b = idx(e.second);
            rhoAll[a] = (int)((rhoAll[a] + invmodPrime(e.second, e.first)) % e.first);
            rhoAll[b] = (int)((rhoAll[b] + invmodPrime(e.first, e.second)) % e.second);
        }
        uint32_t Um = 0; for (int i = 0; i < Z.m; ++i) if (rhoAll[i]) Um |= 1u << i;
        auto R = Z.complete(Um, rhoAll, (int)core.size(), su, Z.Dall - sumNum, cache);
        bool hit1 = false;
        printf("core of size %zu, |U| = %d: %zu completion(s):", core.size(), __builtin_popcount(Um), R.sols.size());
        for (auto& S : R.sols) {
            vector<u128> v; for (auto& b : S.big) v.push_back(b.first * b.second); sort(v.begin(), v.end());
            printf(" {"); for (u128 x : v) printf(" %s", u128str(x).c_str()); printf(" }");
            if (v == vector<u128>{109591, 139823, 154939}) hit1 = true;
        }
        printf("\n  planted star recovered: %s\n", hit1 ? "yes" : "NO");
        // (2) a planted component with one big-big edge: P1 ~ {2, P2}, P2 ~ {11, 13, P1}
        {
            vector<int> rho2(Z.m, 0);
            u64 P1 = 193, P2 = 191;   // 193 | 191 + 2 ; 191 | 193*(11+13) + 143
            vector<pair<u64, u64>> big = {{2, P1}, {11, P2}, {13, P2}};
            for (auto& b : big) { int i = idx(b.first); rho2[i] = (int)((rho2[i] + b.first - invmodPrime(b.second, b.first)) % b.first); }
            uint32_t U2 = 0; for (int i = 0; i < Z.m; ++i) if (rho2[i]) U2 |= 1u << i;
            u128 num = 191ull * 143 + 193ull * 2 * 13 + 193ull * 2 * 11 + 2 * 143;   // over 2*143*191*193
            u128 den = (u128)2 * 143 * 191 * 193;
            u128 g = gcd128(num, den); num /= g; den /= g;                   // den divides Dall
            u128 zNum = num * (Z.Dall / den);
            u128 suUp = ONE - (ONE / den) * num;
            auto R2 = Z.complete(U2, rho2, K - 4, suUp, zNum, cache);
            printf("planted component 2*193, 11*191, 13*191, 191*193: %zu completion(s):", R2.sols.size());
            bool hit = false;
            for (auto& S : R2.sols) {
                vector<u128> v; for (auto& b : S.big) v.push_back(b.first * b.second); sort(v.begin(), v.end());
                printf(" {"); for (u128 x : v) printf(" %s", u128str(x).c_str()); printf(" }");
                if (v == vector<u128>{386, 2101, 2483, 36863}) hit = true;
            }
            printf("\n  planted structure recovered: %s\n", hit ? "yes" : "NO");
        }
        // (3) 128-bit arithmetic: a star with 12 neighbours needs n(A) > 2^64
        {
            uint32_t A = 0; for (int i = Z.m - 12; i < Z.m; ++i) A |= 1u << i;
            Engine::CompletionResult dummy;
            const vector<u128>& f = Z.bigFactors(A, cache, dummy);
            u128 D = 1, n = 0; for (int i = Z.m - 12; i < Z.m; ++i) D *= Z.pr[i];
            for (int i = Z.m - 12; i < Z.m; ++i) n += D / Z.pr[i];
            u128 r = n; for (int p : Z.pr) while (r % p == 0) r /= p;
            u128 prod = 1; vector<u128> all; factor128(r, all, nullptr); for (u128 x : all) prod *= x;
            printf("n(A) for the 12 largest primes of S = %s (> 2^64: %s); prime factors > 73:", u128str(n).c_str(), (n >> 64) ? "yes" : "no");
            for (u128 x : f) printf(" %s", u128str(x).c_str());
            printf("\n  factorisation reproduces the cofactor: %s\n", prod == r ? "yes" : "NO");
        }
        fflush(stdout);
    }

    if (!runMain) return 0;
    printf("\n=== Part 2: exhaustive search (S = primes <= 73, |C| + |U| <= %d) ===\n", K);
    Engine E(73, K);
    printf("threads = %d, split prime = %d, loss bound: theta = 1/%llu, shares of the larger endpoint (/%d):",
           threads, splitPrime, E.thetaDen, E.AD);
    for (int i = 0; i < E.m; ++i) printf(" %d", E.SHN[i]);
    printf("\n");
    fflush(stdout);
    if (dumpPath) E.dumpFile = fopen(dumpPath, "w");
    printf("largest possible star (neighbours of one big prime): %d\n", E.maxStar);
    E.run(threads, splitPrime);
    if (E.dumpFile) fclose(E.dumpFile);
    long long searchMs = msecs();
    printf("search nodes           : %lld\n", (long long)E.nodes);
    printf("cores passing Step 1   : %lld (of which |C|+|U| = %d: %lld)\n", E.endStates, K, E.endTight);
    printf("completion shapes      : %lld tried, %lld pass parity+value (in %lld cores), %lld candidate stars\n",
           E.shapesTried, E.shapesAlive, E.coresWithShape, E.starCands);
    printf("surviving shapes by number of big-big edges: 0: %lld, 1: %lld, >=2: %lld\n", E.aliveByNbb[0], E.aliveByNbb[1], E.aliveByNbb[2]);
    printf("unresolved cores       : %lld\n", E.unresolved);
    for (auto& s : E.unresolvedList) printf("    UNRESOLVED %s\n", s.c_str());
    printf("probable (not proven) primes used: %lld\n", E.probablePrimes);
    printf("search + completion time: %lld.%03lld s\n", searchMs / 1000, searchMs % 1000);

    printf("\n=== Part 3: the solutions, each verified with exact rational arithmetic ===\n");
    vector<vector<Elem>> byK, smaller;
    for (auto& T : E.solutionSet) (T.size() == (size_t)K ? byK : smaller).push_back(T);
    auto byValues = [](const vector<Elem>& A, const vector<Elem>& B) {   // order by the sorted element lists
        vector<u128> a, b;
        for (auto& e : A) a.push_back(e.first * e.second);
        for (auto& e : B) b.push_back(e.first * e.second);
        sort(a.begin(), a.end()); sort(b.begin(), b.end());
        return a < b;
    };
    sort(byK.begin(), byK.end(), byValues); sort(smaller.begin(), smaller.end(), byValues);
    int good = 0, goodSmall = 0, idxS = 0;
    for (auto& T : byK) {
        bool ok = verifySolution(T); if (ok) ++good;
        printf("#%-4d %s |T|=%zu:", ++idxS, ok ? "OK " : "BAD", T.size());
        vector<u128> v; for (auto& e : T) v.push_back(e.first * e.second); sort(v.begin(), v.end());
        for (u128 x : v) printf(" %s", u128str(x).c_str());
        printf("\n");
    }
    map<size_t, int> smallCount;
    for (auto& T : smaller) {
        bool ok = verifySolution(T); if (ok) ++goodSmall;
        smallCount[T.size()]++;
        printf("(smaller) %s |T|=%zu:", ok ? "OK " : "BAD", T.size());
        vector<u128> v; for (auto& e : T) v.push_back(e.first * e.second); sort(v.begin(), v.end());
        for (u128 x : v) printf(" %s", u128str(x).c_str());
        printf("\n");
    }
    printf("\n=== RESULT ===\n");
    for (auto& x : smallCount) printf("sets with |T| = %zu and sum 1 found along the way (consistency check): %d\n", x.first, x.second);
    printf("number of %d-element subsets T of P with sum 1/n = 1: %zu (all %d verified exactly)\n", K, byK.size(), good);
    bool complete = E.unresolved == 0 && E.probablePrimes == 0 && good == (int)byK.size() && goodSmall == (int)smaller.size();
    if (complete) printf("The list is complete: every %d-element T with reciprocal sum 1 is listed above.\n", K);
    else printf("The completeness proof did NOT close (see above).\n");
    long long ms = msecs();
    printf("start: %s\nend:   %s\ntotal elapsed: %lld.%03lld s\n", startStr.c_str(), utcNow().c_str(), ms / 1000, ms % 1000);
    return 0;
}
