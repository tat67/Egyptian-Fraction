// semiprime47.cpp
//
// Problem.  P = { p*q : p < q primes }.  Find ALL T subset of P with |T| = 47 and
// sum_{n in T} 1/n = 1, verify each exactly, and prove that the list is complete.
//
// Integer/rational arithmetic only: no float, double or long double anywhere.  Bounds on sums
// of reciprocals use 96-bit fixed point with directed rounding (upper bounds rounded up,
// lower bounds rounded down); every solution is verified with exact big-integer rationals.
//
// Method (see README47.md for the proofs):
//  1. H_47 < 2, so for |T| = 47:  sum = 1  <=>  sum is an integer  <=>  for every prime p,
//     sum_{q in N(p)} q^{-1} == 0 (mod p)                                               (*)
//     where N(p) = { q : pq in T } (T viewed as a graph on primes).
//  2. S = primes <= 73, "big" primes >= 79.  C = elements of T with both factors in S (core),
//     G = the rest.  rho(q) = core residue at q, U = { q in S : rho(q) != 0 }.
//     Each q in U needs its own big edge, so |G| >= |U| and |C| + |U| <= 47.
//  3. Step 1 (search): enumerate every core C with |C| + |U(C)| <= 47 satisfying the value
//     inequality 1 - sum_{q in U} 1/(79q) - V(47-|C|-|U|) <= sum(C) <= 1.
//  4. Step 2 (completion): for every such core find ALL big parts G with sum(G) = 1 - sum(C).
//     A big part has a shape (d_q = number of big neighbours of q, nbb = big-big edges) with
//     excess nbb + sum_U(d_q-1) + sum_{not U} d_q <= 47-|C|-|U|, parity at 2 and a value upper
//     bound.  nbb = 0: all big primes are stars P | n(A); every exact cover is enumerated.
//     nbb = 1: one two-prime component, solved through a divisor equation.  Any surviving
//     shape with nbb >= 2 would be reported as unresolved (the run shows there is none).
//  5. Every solution found is checked: 47 distinct squarefree semiprimes, exact sum 1.
//
// Usage: ./semiprime47 [threads] [--selftest] [--split p] [--dump cores.txt]
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
    long long shapesTried = 0, shapesAlive = 0, starCands = 0, coresWithShape = 0, probablePrimes = 0;
    set<vector<u64>> solutionSet;              // all solutions found (sorted element lists)
    FILE* dumpFile = nullptr;                  // optional: record every core that survives Step 1
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
        for (int p : pr) Dall *= (u128)p;
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
    vector<u64> bigList;                       // the first primes > SB
    u128 Dall = 1;                             // product of all primes of S (a common denominator)
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
    struct Star { u64 P; uint32_t mask; u128 valNum; };   // value of the star = valNum / Dall
    struct Solution { vector<pair<u64, u64>> big; };
    // all covers of the multiplicities need[] by distinct stars, candidates taken in increasing
    // index order (so every family is produced once)
    void allCovers(const vector<int>& W, vector<int>& need, const vector<Star>& cand, size_t start,
                   vector<int>& chosen, vector<vector<int>>& out) const {
        bool done = true; for (int v : need) if (v) { done = false; break; }
        if (done) { out.push_back(chosen); return; }
        int w = (int)W.size();
        for (size_t idx = start; idx < cand.size(); ++idx) {
            const Star& st = cand[idx];
            bool ok = true;
            for (int i = 0; i < w && ok; ++i) if ((st.mask >> i & 1) && need[i] == 0) ok = false;
            for (int c : chosen) if (cand[c].P == st.P) ok = false;
            if (!ok) continue;
            for (int i = 0; i < w; ++i) if (st.mask >> i & 1) --need[i];
            chosen.push_back((int)idx);
            allCovers(W, need, cand, idx + 1, chosen, out);
            chosen.pop_back();
            for (int i = 0; i < w; ++i) if (st.mask >> i & 1) ++need[i];
        }
    }
    // candidate stars on W: A subset of W, 2 <= |A| <= maxStar, P > SB prime factor of n(A),
    // P == (-rho(q))^{-1} mod q for every q in A with d_q = 1
    vector<Star> starCandidates(const vector<int>& W, const vector<int>& d, const vector<int>& rhoAll) const {
        int w = (int)W.size(); vector<Star> cand;
        for (uint32_t mask = 1; mask < (1u << w); ++mask) {
            int k = __builtin_popcount(mask);
            if (k < 2 || k > maxStar) continue;
            u64 D = 1; for (int i = 0; i < w; ++i) if (mask >> i & 1) D *= (u64)pr[W[i]];
            u64 n = 0; for (int i = 0; i < w; ++i) if (mask >> i & 1) n += D / (u64)pr[W[i]];
            u64 r = n; for (int i = 0; i < m; ++i) while (r % pr[i] == 0) r /= pr[i];
            vector<u64> fs; factorInto(r, fs); sort(fs.begin(), fs.end()); fs.erase(unique(fs.begin(), fs.end()), fs.end());
            for (u64 P : fs) {
                bool ok = true;
                for (int i = 0; i < w && ok; ++i)
                    if ((mask >> i & 1) && d[W[i]] == 1) {
                        u64 q = pr[W[i]];
                        if ((invmodPrime(P, q) + (u64)rhoAll[W[i]]) % q != 0) ok = false;
                    }
                if (!ok) continue;
                // value of the star = (n/P)/D = (n/P) * (Dall/D) / Dall
                u128 val = (u128)(n / P) * (Dall / (u128)D);
                cand.push_back(Star{P, mask, val});
            }
        }
        return cand;
    }
    struct CompletionResult { vector<Solution> sols; bool unresolved = false; long long shapes = 0, shapesAlive = 0, cand = 0;
                              long long probablePrimes = 0; string note; };
    // U: bitmask of unsatisfied primes, rhoAll = full core residues, c = |C|, su = upper
    // bound of the core sum (fixed point), zNum = Dall * (1 - sum C) exactly.
    CompletionResult complete(uint32_t U, const vector<int>& rhoAll, int c, u128 su, u128 zNum) const {
        CompletionResult R;
        int e = __builtin_popcount(U);
        int slack = KT - c - e;
        if (slack < 0) return R;
        u128 Zlo = su >= ONE ? 0 : ONE - su;
        vector<u128> single(m, 0);
        for (int i = 0; i < m; ++i) if (U >> i & 1) single[i] = recipUp((u64)pr[i] * pminFor(i, rhoAll[i]));
        auto multiVal = [&](int i, int dq) { u128 v = 0; for (int k = 0; k < dq; ++k) v += recipUp((u64)pr[i] * bigList[k]); return v; };
        vector<int> d(m, 0);
        function<void(int, int, u128)> rec = [&](int i, int used, u128 ub) {
            if (i == m) {
                if ((rhoAll[0] + d[0]) % 2 != 0) return;                     // (iii)
                for (int nbb = 0; used + nbb <= slack; ++nbb) {
                    ++R.shapes;
                    u128 tot = ub + (u128)nbb * recipUp(bigList[0] * bigList[1]);
                    if (tot < Zlo) continue;                                 // (iv)
                    ++R.shapesAlive;
                    if (nbb >= 2) {
                        R.unresolved = true;
                        R.note += " [shape with " + to_string(nbb) + " big-big edges]";
                        continue;
                    }
                    solveShape(d, nbb, rhoAll, zNum, R);
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
    void solveShape(const vector<int>& d, int nbb, const vector<int>& rhoAll, u128 zNum, CompletionResult& R) const {
        vector<int> W; for (int i = 0; i < m; ++i) if (d[i] > 0) W.push_back(i);
        int w = (int)W.size();
        if (w > 20) { R.unresolved = true; R.note += " [too many attachments]"; return; }
        vector<Star> cand = starCandidates(W, d, rhoAll);
        R.cand += (long long)cand.size();
        if (nbb == 0) {
            vector<int> need(w); for (int i = 0; i < w; ++i) need[i] = d[W[i]];
            vector<vector<int>> covers; vector<int> chosen;
            allCovers(W, need, cand, 0, chosen, covers);
            for (auto& cv : covers) {
                u128 s = 0; for (int id : cv) s += cand[id].valNum;
                if (s != zNum) continue;                                     // exact value check
                Solution S;
                for (int id : cv) for (int i = 0; i < w; ++i) if (cand[id].mask >> i & 1) S.big.push_back({(u64)pr[W[i]], cand[id].P});
                R.sols.push_back(S);
            }
            return;
        }
        // nbb == 1: attachment sets A1 (of P1) and A2 (of P2), both nonempty subsets of W
        for (uint32_t m1 = 1; m1 < (1u << w); ++m1)
            for (uint32_t m2 = m1; m2 < (1u << w); ++m2) {                  // unordered pair {A1, A2}
                vector<int> need(w); bool ok = true;
                for (int i = 0; i < w; ++i) {
                    need[i] = d[W[i]] - (int)(m1 >> i & 1) - (int)(m2 >> i & 1);
                    if (need[i] < 0) ok = false;
                }
                if (!ok) continue;
                vector<vector<int>> covers; vector<int> chosen;
                allCovers(W, need, cand, 0, chosen, covers);
                u128 b1 = 1, b2 = 1, a1 = 0, a2 = 0;
                for (int i = 0; i < w; ++i) { if (m1 >> i & 1) b1 *= pr[W[i]]; if (m2 >> i & 1) b2 *= pr[W[i]]; }
                for (int i = 0; i < w; ++i) { if (m1 >> i & 1) a1 += b1 / pr[W[i]]; if (m2 >> i & 1) a2 += b2 / pr[W[i]]; }
                for (auto& cv : covers) {
                    u128 s = 0; for (int id : cv) s += cand[id].valNum;
                    if (s >= zNum) continue;
                    u128 zk = zNum - s;                                      // Z_K = zk / Dall
                    // t = Z_K * b1 * b2 must be a positive integer
                    u128 B = b1 * b2;
                    u128 g = B, h = Dall; while (h) { u128 r = g % h; g = h; h = r; }   // gcd(B, Dall)
                    u128 Q = Dall / g;
                    if (zk % Q != 0) continue;
                    u128 t = (zk / Q) * (B / g);
                    u128 L = t + a1 * a2;
                    if (L >> 63) { R.unresolved = true; R.note += " [large t]"; continue; }
                    vector<u64> fs; factorInto((u64)L, fs);
                    for (int i = 0; i < w; ++i) { if (m1 >> i & 1) fs.push_back(pr[W[i]]); if (m2 >> i & 1) fs.push_back(pr[W[i]]); }
                    sort(fs.begin(), fs.end());
                    vector<pair<u64, int>> pe;
                    for (u64 p : fs) { if (!pe.empty() && pe.back().first == p) pe.back().second++; else pe.push_back({p, 1}); }
                    u128 N = B * L;
                    vector<u128> divs{1};
                    for (auto& x : pe) { size_t sz = divs.size(); u128 pk = 1;
                        for (int k = 1; k <= x.second; ++k) { pk *= x.first; for (size_t j = 0; j < sz; ++j) divs.push_back(divs[j] * pk); } }
                    for (u128 X : divs) {
                        u128 Y = N / X;
                        if ((X + a1 * b2) % t != 0 || (Y + a2 * b1) % t != 0) continue;
                        u128 P1 = (X + a1 * b2) / t, P2 = (Y + a2 * b1) / t;
                        if (P1 == P2 || P1 <= (u128)SB || P2 <= (u128)SB) continue;
                        bool dup = false; for (int id : cv) if ((u128)cand[id].P == P1 || (u128)cand[id].P == P2) dup = true;
                        if (dup) continue;
                        int pp1 = isPrime128(P1), pp2 = isPrime128(P2);
                        if (!pp1 || !pp2) continue;
                        if (pp1 == 2 || pp2 == 2) R.probablePrimes++;
                        if ((P1 >> 64) || (P2 >> 64) || ((P1 * P2) >> 64)) { R.unresolved = true; R.note += " [huge component prime]"; continue; }
                        Solution S;
                        for (int id : cv) for (int i = 0; i < w; ++i) if (cand[id].mask >> i & 1) S.big.push_back({(u64)pr[W[i]], cand[id].P});
                        for (int i = 0; i < w; ++i) { if (m1 >> i & 1) S.big.push_back({(u64)pr[W[i]], (u64)P1}); if (m2 >> i & 1) S.big.push_back({(u64)pr[W[i]], (u64)P2}); }
                        S.big.push_back({(u64)min(P1, P2), (u64)max(P1, P2)});
                        R.sols.push_back(S);
                    }
                }
            }
    }
    // 1 = certainly prime (deterministic for < 2^64), 2 = probable prime (>= 2^64), 0 = composite
    static u128 mulmod128(u128 a, u128 b, u128 mod) {
        u128 r = 0; a %= mod;
        while (b) { if (b & 1) { r += a; if (r >= mod || r < a) r -= mod; } b >>= 1; if (b) { u128 a2 = a + a; if (a2 >= mod || a2 < a) a2 -= mod; a = a2; } }
        return r;
    }
    static int isPrime128(u128 n) {
        if (!(n >> 64)) return isPrime64((u64)n) ? 1 : 0;
        static const u64 bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71};
        for (u64 p : bases) if (n % p == 0) return 0;
        u128 dd = n - 1; int s = 0; while (!(dd & 1)) { dd >>= 1; ++s; }
        for (u64 a : bases) {
            u128 x = 1, b = a, e = dd;
            while (e) { if (e & 1) x = mulmod128(x, b, n); b = mulmod128(b, b, n); e >>= 1; }
            if (x == 1 || x == n - 1) continue;
            bool comp = true;
            for (int r = 1; r < s; ++r) { x = mulmod128(x, x, n); if (x == n - 1) { comp = false; break; } }
            if (comp) return 0;
        }
        return 2;
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
            vector<u64> core;
            for (auto& x : edges) core.push_back((u64)E.pr[x.first] * E.pr[x.second]);
            if (E.dumpFile) {
                string line = "E " + to_string(c) + " " + to_string(e) + " U";
                for (int q = 0; q < E.m; ++q) if (U >> q & 1) line += " " + to_string(E.pr[q]) + ":" + to_string(rho[q]);
                line += " C";
                for (u64 n : core) line += " " + to_string(n);
                lock_guard<mutex> g(E.mx); fprintf(E.dumpFile, "%s\n", line.c_str()); fflush(E.dumpFile);
            }
            if (e == 0) {                                              // C alone satisfies (*): sum(C) = 1
                lock_guard<mutex> g(E.mx); E.endStates++;
                if (c > 0) { sort(core.begin(), core.end()); E.solutionSet.insert(core); }
                return;
            }
            vector<int> rhoAll(E.m, 0);
            for (int q = 0; q < E.m; ++q) if (U >> q & 1) rhoAll[q] = rho[q];
            u128 sumNum = 0; for (u64 n : core) sumNum += E.Dall / n;   // Dall * sum(C), exact
            u128 zNum = sumNum < E.Dall ? E.Dall - sumNum : 0;
            CompletionResult R = E.complete(U, rhoAll, c, su, zNum);
            lock_guard<mutex> g(E.mx);
            E.endStates++;
            if (c + e == E.KT) E.endTight++;
            E.shapesTried += R.shapes; E.shapesAlive += R.shapesAlive; E.starCands += R.cand; E.probablePrimes += R.probablePrimes;
            if (R.shapesAlive) E.coresWithShape++;
            if (R.unresolved) {
                E.unresolved++;
                string s = "c=" + to_string(c) + " U={";
                for (int q = 0; q < E.m; ++q) if (U >> q & 1) s += " " + to_string(E.pr[q]) + ":" + to_string(rho[q]);
                s += " }" + R.note; E.unresolvedList.push_back(s);
            }
            for (auto& S : R.sols) {
                vector<u64> T = core;
                for (auto& b : S.big) T.push_back(b.first * b.second);
                sort(T.begin(), T.end());
                E.solutionSet.insert(T);
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
static bool isSquarefreeSemiprime(u64 n) {
    for (u64 p = 2; p * p <= n; ++p)
        if (n % p == 0) { u64 q = n / p; return q != p && isPrime64(p) && isPrime64(q); }
    return false;
}
static vector<pair<u64, u64>> splitPairs(const vector<u64>& T) {
    vector<pair<u64, u64>> r;
    for (u64 n : T) for (u64 p = 2; p * p <= n; ++p) if (n % p == 0) { r.push_back({p, n / p}); break; }
    return r;
}

int main(int argc, char** argv) {
    int threads = (int)thread::hardware_concurrency(); if (threads <= 0) threads = 4;
    int splitPrime = 61;
    bool selftest = false, runMain = true;
    const char* dumpPath = nullptr;
    for (int a = 1; a < argc; ++a) {
        if (!strcmp(argv[a], "--selftest")) selftest = true;
        else if (!strcmp(argv[a], "--skip-main")) runMain = false;
        else if (!strcmp(argv[a], "--split") && a + 1 < argc) splitPrime = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--dump") && a + 1 < argc) dumpPath = argv[++a];
        else if (!strcmp(argv[a], "--budget") && a + 1 < argc) ++a;
        else threads = max(1, atoi(argv[a]));
    }
    auto t0 = chrono::steady_clock::now();
    auto secs = [&]() { return (long long)chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now() - t0).count(); };
    int K = 47;
    for (int a = 1; a + 1 < argc; ++a) if (!strcmp(argv[a], "--budget")) K = atoi(argv[a + 1]);   // testing aid
    if (K < 1 || K > 47) return 1;

    printf("=== Part 1: size lemma ===\n");
    SemiprimeList SP(2000);
    {
        auto Hcmp = [&](int k, u64 integer) {
            vector<pair<u64, u64>> T(SP.fac.begin(), SP.fac.begin() + k);
            BigNat n, d; exactSum(T, n, d); BigNat rhs = d; rhs.mulSmall((uint32_t)integer);
            return BigNat::cmp(n, rhs);
        };
        u128 h = 0; for (int i = 0; i < K; ++i) h += recipUp(SP.val[i]);
        printf("H_47 (sum of the reciprocals of the 47 smallest elements of P) < %s ; exact check H_47 < 2: %s\n",
               fpToString(h).c_str(), Hcmp(K, 2) < 0 ? "yes" : "NO");
        printf("=> every 47-element T has 0 < sum < 2, so 'sum = 1' <=> 'sum is an integer' <=> (*) at every prime\n");
        if (!(Hcmp(K, 2) < 0)) return 1;
    }

    if (selftest) {
        printf("\n=== Self test: completion routine on planted big-prime structures ===\n");
        Engine Z(73, K, true);
        // (1) a 47-term solution whose big part is a star at 3779 on {29,37,41}
        vector<u64> T1 = {6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 77, 82, 86,
                          87, 91, 93, 95, 106, 111, 115, 123, 133, 155, 159, 161, 185, 203, 215, 253, 265, 583, 667, 731,
                          109591, 139823, 154939};
        vector<u64> core; for (u64 n : T1) if (n <= 73 * 73 && isSquarefreeSemiprime(n)) { bool small = true; for (auto& pq : splitPairs({n})) if (pq.second > 73) small = false; if (small) core.push_back(n); }
        vector<int> rhoAll(Z.m, 0); u128 su = 0, sumNum = 0;
        auto idx = [&](u64 p) { for (int i = 0; i < Z.m; ++i) if ((u64)Z.pr[i] == p) return i; return -1; };
        for (auto& e : splitPairs(core)) {
            su += recipUp(e.first * e.second); sumNum += Z.Dall / (e.first * e.second);
            int a = idx(e.first), b = idx(e.second);
            rhoAll[a] = (int)((rhoAll[a] + invmodPrime(e.second, e.first)) % e.first);
            rhoAll[b] = (int)((rhoAll[b] + invmodPrime(e.first, e.second)) % e.second);
        }
        uint32_t Um = 0; for (int i = 0; i < Z.m; ++i) if (rhoAll[i]) Um |= 1u << i;
        auto R = Z.complete(Um, rhoAll, (int)core.size(), su, Z.Dall - sumNum);
        printf("core of size %zu, |U| = %d: %zu completion(s):", core.size(), __builtin_popcount(Um), R.sols.size());
        for (auto& S : R.sols) { printf(" {"); for (auto& b : S.big) printf(" %llu", b.first * b.second); printf(" }"); }
        printf("\n");
        // (2) a planted component with one big-big edge: P1 ~ {2, P2}, P2 ~ {11, 13, P1}
        {
            Engine Y(73, K, true);
            vector<int> rho2(Y.m, 0);
            u64 P1 = 193, P2 = 191;   // 193 | 191 + 2 ; 191 | 193*(11+13) + 143
            vector<pair<u64, u64>> big = {{2, P1}, {11, P2}, {13, P2}};
            for (auto& b : big) { int i = idx(b.first); rho2[i] = (int)((rho2[i] + b.first - invmodPrime(b.second, b.first)) % b.first); }
            uint32_t U2 = 0; for (int i = 0; i < Y.m; ++i) if (rho2[i]) U2 |= 1u << i;
            // Z = value of the planted component, as a multiple of 1/Dall
            u128 zNum;
            // value = 1/(2*193) + 1/(11*191) + 1/(13*191) + 1/(191*193) = t/(b1*b2) with b1 = 2, b2 = 143
            u128 num = 191ull * 143 + 193ull * 2 * 13 + 193ull * 2 * 11 + 2 * 143;   // over 2*143*191*193
            u128 den = (u128)2 * 143 * 191 * 193;
            u128 g = num, h2 = den; while (h2) { u128 r = g % h2; g = h2; h2 = r; }
            num /= g; den /= g;                                    // den divides Dall
            zNum = num * (Y.Dall / den);
            u128 suUp = ONE - (ONE / den) * num;                   // any upper bound of 1 - Z works here
            auto R2 = Y.complete(U2, rho2, K - 4, suUp, zNum);
            printf("planted component 2*193, 11*191, 13*191, 191*193: %zu completion(s):", R2.sols.size());
            bool hit = false;
            for (auto& S : R2.sols) {
                vector<u64> v; for (auto& b : S.big) v.push_back(b.first * b.second); sort(v.begin(), v.end());
                printf(" {"); for (u64 x : v) printf(" %llu", x); printf(" }");
                if (v == vector<u64>{386, 2101, 2483, 36863}) hit = true;
            }
            printf("\n  planted structure recovered: %s\n", hit ? "yes" : "NO");
        }
        fflush(stdout);
    }

    if (!runMain) return 0;
    printf("\n=== Part 2: exhaustive search (S = primes <= 73, |C| + |U| <= 47) ===\n");
    printf("threads = %d\n", threads); fflush(stdout);
    Engine E(73, K, true);
    if (dumpPath) E.dumpFile = fopen(dumpPath, "w");
    printf("largest possible star (neighbours of one big prime): %d\n", E.maxStar);
    E.run(threads, splitPrime);
    printf("search nodes           : %lld\n", (long long)E.nodes);
    printf("cores passing Step 1   : %lld (of which |C|+|U| = 47: %lld)\n", E.endStates, E.endTight);
    printf("completion shapes      : %lld tried, %lld pass parity+value (in %lld cores), %lld candidate stars\n",
           E.shapesTried, E.shapesAlive, E.coresWithShape, E.starCands);
    printf("unresolved cores       : %lld\n", E.unresolved);
    for (auto& s : E.unresolvedList) printf("    UNRESOLVED %s\n", s.c_str());
    printf("probable (not proven) primes used: %lld\n", E.probablePrimes);
    printf("elapsed: %lld s\n", secs());

    printf("\n=== Part 3: the solutions, each verified with exact rational arithmetic ===\n");
    int idxS = 0, good = 0;
    for (auto& T : E.solutionSet) {
        bool ok = T.size() == (size_t)K;
        set<u64> distinct(T.begin(), T.end()); ok = ok && distinct.size() == T.size();
        for (u64 n : T) ok = ok && isSquarefreeSemiprime(n);
        ok = ok && exactSumIsOne(splitPairs(T));
        if (ok) ++good;
        printf("#%-3d %s |T|=%zu:", ++idxS, ok ? "OK " : "BAD", T.size());
        for (u64 n : T) printf(" %llu", n);
        printf("\n");
    }
    printf("\n=== RESULT ===\n");
    printf("number of 47-element subsets T of P with sum 1/n = 1: %zu (all %d verified exactly)\n", E.solutionSet.size(), good);
    if (E.unresolved == 0 && E.probablePrimes == 0 && good == (int)E.solutionSet.size())
        printf("The list is complete: every 47-element T with reciprocal sum 1 is listed above.\n");
    else
        printf("The completeness proof did NOT close (see above).\n");
    printf("total elapsed: %lld s\n", secs());
    return 0;
}
