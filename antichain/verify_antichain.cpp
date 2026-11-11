// verify_antichain.cpp -- exact verification (integer arithmetic only, no floating point).
// Each non-empty input line is a set T of positive integers (up to 20 digits each).  For every line the program checks:
//   (1) the elements are distinct and >= 2;   (2) no element divides another;   (3) sum_{n in T} 1/n == 1 exactly.
// The sum is computed over the common denominator lcm(T) with 128-bit integers; an overflow is detected and reported.
//   g++ -O2 -o verify_antichain verify_antichain.cpp && ./verify_antichain solutions43.txt
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
typedef unsigned __int128 u128;
static u128 gcd(u128 a, u128 b) { while (b) { u128 t = a % b; a = b; b = t; } return a; }
static u128 parse(const std::string& s) { u128 v = 0; for (char c : s) { if (c < '0' || c > '9') { fprintf(stderr, "bad number\n"); exit(2); } v = v * 10 + (u128)(c - '0'); } return v; }
int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage: verify_antichain FILE\n"); return 2; }
    std::ifstream f(argv[1]); std::string line; int ln = 0; bool all = true;
    while (std::getline(f, line)) {
        std::istringstream is(line); std::string tok; std::vector<u128> T; while (is >> tok) T.push_back(parse(tok));
        if (T.empty()) continue; ++ln; std::sort(T.begin(), T.end());
        bool ok = true; const char* why = "ok";
        for (size_t i = 0; i < T.size() && ok; i++) { if (T[i] < 2) { ok = false; why = "element < 2"; } if (i && T[i] == T[i - 1]) { ok = false; why = "repeated element"; } }
        for (size_t i = 0; i < T.size() && ok; i++) for (size_t j = i + 1; j < T.size(); j++) if (T[j] % T[i] == 0) { ok = false; why = "one element divides another"; break; }
        if (ok) {
            u128 L = 1; bool ovf = false;
            for (u128 n : T) { u128 g = gcd(L, n); u128 m = n / g; if (L > (((u128)1) << 120) / m) { ovf = true; break; } L *= m; }
            if (ovf) { ok = false; why = "lcm does not fit in 120 bits (use verify_antichain.py)"; }
            else { u128 s = 0; for (u128 n : T) s += L / n;   // each term <= L/2, at most 2^7 terms: no overflow
                   if (s != L) { ok = false; why = "sum != 1"; } }
        }
        printf("line %d: |T| = %zu : %s\n", ln, T.size(), ok ? "antichain, sum of reciprocals == 1  [OK]" : why);
        all = all && ok;
    }
    printf(all ? "ALL OK\n" : "FAILURE\n"); return all ? 0 : 1;
}
