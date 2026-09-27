// Brute-force reference for Step 1 on a small instance (S = primes <= SB, all 2^E edge subsets).
// For every core C and each budget K it evaluates
//   FIN(K): |C|+|U| <= K, lower-rounded sum_C <= 1, and the FINAL value test
//           sum_C(up) + sum_{q in U} up(1/(b0 q)) + VB[K-|C|-|U|] >= 1        (what endState tests)
//   SEG(K): |C|+|U| <= K, exact sum_C <= 1, and the value test for EVERY upper segment
//           U' = U ∩ [p_j, inf), j = 0..m (U' = U, ..., U' = empty)             (corrected condition)
// The DFS output D(K) must satisfy SEG(K) ⊆ D(K) ⊆ FIN(K).  Fixed point exactly as the program.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <algorithm>
#include <thread>
#include <string>
using namespace std;
typedef unsigned long long u64; typedef unsigned __int128 u128;
static const u128 ONE = (u128)1 << 96;
static u128 up(u64 n) { return (ONE + n - 1) / n; }
static u128 lo(u64 n) { return ONE / n; }
static bool isprime(u64 n) { if (n < 2) return false; for (u64 d = 2; d * d <= n; ++d) if (n % d == 0) return false; return true; }
static u64 inv(u64 a, u64 p) { a %= p; for (u64 x = 1; x < p; ++x) if (a * x % p == 1) return x; return 0; }
int SB; vector<u64> pr; int m, E; vector<int> ea, eb; vector<u128> EU, EL; vector<u64> NUM; u64 DALL = 1;
vector<vector<int>> INV; vector<u128> GZ; vector<u128> VB; vector<int> KS;
struct Res { vector<vector<u64>> seg, fin; };
void work(int prefix, int topbits, Res& R) {
    int low = E - topbits;
    int res[32] = {0}; uint32_t U = 0; int c = 0; u128 su = 0, sl = 0; u64 num = 0; u64 mask = 0;
    auto toggle = [&](int e) {
        int a = ea[e], b = eb[e]; bool add = !(mask >> e & 1); mask ^= (1ull << e);
        int pa = (int)pr[a], pb = (int)pr[b];
        if (add) { res[a] = (res[a] + INV[a][b]) % pa; res[b] = (res[b] + INV[b][a]) % pb; ++c; su += EU[e]; sl += EL[e]; num += NUM[e]; }
        else { res[a] = (res[a] + pa - INV[a][b]) % pa; res[b] = (res[b] + pb - INV[b][a]) % pb; --c; su -= EU[e]; sl -= EL[e]; num -= NUM[e]; }
        U = res[a] ? (U | 1u << a) : (U & ~(1u << a)); U = res[b] ? (U | 1u << b) : (U & ~(1u << b));
    };
    for (int t = 0; t < topbits; ++t) if (prefix >> t & 1) toggle(low + t);
    u64 steps = 1ull << low;
    for (u64 i = 0; i < steps; ++i) {
        if (i) toggle(__builtin_ctzll(i));
        int e = __builtin_popcount(U);
        for (size_t k = 0; k < KS.size(); ++k) {
            int K = KS[k]; if (c + e > K) continue;
            bool fin = sl <= ONE && su + GZ[U] + VB[K - c - e] >= ONE;
            bool seg = num <= DALL;
            if (seg) for (int j = 0; j <= m && seg; ++j) {
                uint32_t Up = U & ~((1u << j) - 1);           // U ∩ [p_j, inf)
                if (su + GZ[Up] + VB[K - c - __builtin_popcount(Up)] < ONE) seg = false;
            }
            if (fin) R.fin[k].push_back(mask);
            if (seg) R.seg[k].push_back(mask);
        }
    }
}
int main(int argc, char** argv) {
    SB = atoi(argv[1]); for (int i = 2; i < argc; ++i) KS.push_back(atoi(argv[i]));
    for (u64 p = 2; p <= (u64)SB; ++p) if (isprime(p)) pr.push_back(p);
    m = pr.size(); for (u64 p : pr) DALL *= p;
    u64 bigMin = SB + 1; while (!isprime(bigMin)) ++bigMin;
    for (int a = 0; a < m; ++a) for (int b = a + 1; b < m; ++b) { ea.push_back(a); eb.push_back(b); u64 n = pr[a] * pr[b]; EU.push_back(up(n)); EL.push_back(lo(n)); NUM.push_back(DALL / n); }
    E = ea.size(); INV.assign(m, vector<int>(m, 0));
    for (int a = 0; a < m; ++a) for (int b = 0; b < m; ++b) if (a != b) INV[a][b] = (int)inv(pr[b], pr[a]);
    GZ.assign(1u << m, 0); for (uint32_t s = 0; s < (1u << m); ++s) for (int j = 0; j < m; ++j) if (s >> j & 1) GZ[s] += up(bigMin * pr[j]);
    vector<u64> bs; u64 lim = 60 * bigMin;
    for (u64 p = 2; p <= lim / 2; ++p) if (isprime(p)) for (u64 q = p + 1; p * q <= lim; ++q) if (q > (u64)SB && isprime(q)) bs.push_back(p * q);
    sort(bs.begin(), bs.end()); int Kmax = *max_element(KS.begin(), KS.end());
    VB.assign(Kmax + 2, 0); for (int x = 1; x <= Kmax + 1; ++x) VB[x] = VB[x - 1] + up(bs[x - 1]);
    int topbits = 2; vector<Res> R(1 << topbits); vector<thread> th;
    for (int p = 0; p < (1 << topbits); ++p) { R[p].seg.assign(KS.size(), {}); R[p].fin.assign(KS.size(), {}); th.emplace_back(work, p, topbits, ref(R[p])); }
    for (auto& t : th) t.join();
    for (size_t k = 0; k < KS.size(); ++k) {
        vector<u64> seg, fin;
        for (auto& r : R) { seg.insert(seg.end(), r.seg[k].begin(), r.seg[k].end()); fin.insert(fin.end(), r.fin[k].begin(), r.fin[k].end()); }
        sort(seg.begin(), seg.end()); sort(fin.begin(), fin.end());
        printf("SB %d K %d edges %d : |SEG| = %zu  |FIN| = %zu\n", SB, KS[k], E, seg.size(), fin.size());
        string fs = "bf_seg_" + to_string(SB) + "_" + to_string(KS[k]) + ".txt", ff = "bf_fin_" + to_string(SB) + "_" + to_string(KS[k]) + ".txt";
        FILE* f = fopen(fs.c_str(), "w"); for (u64 x : seg) fprintf(f, "%llu\n", x); fclose(f);
        f = fopen(ff.c_str(), "w"); for (u64 x : fin) fprintf(f, "%llu\n", x); fclose(f);
    }
    return 0;
}
