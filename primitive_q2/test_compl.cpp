// Validation of compl.h: (1) two-term solver vs brute force on random fractions;
// (2) planted completions taken from the known 44-term set T44 (h = 1, 2, 3).
#include <bits/stdc++.h>
#include "gmpz.h"
#include "compl.h"
using namespace std; typedef unsigned long long u64;
static Fac facOf(u64 n) { Fac f; for (u64 p = 2; p * p <= n; p++) if (n % p == 0) { int e = 0; while (n % p == 0) { n /= p; e++; } f.push_back({Z(p), e}); } if (n > 1) f.push_back({Z(n), 1}); return f; }
int main(int argc, char** argv) { int hFrom = argc > 1 ? atoi(argv[1]) : 1, hTo = argc > 2 ? atoi(argv[2]) : 3;
  mt19937_64 rng(7); int bad = 0;
  for (int it = 0; it < 2000; it++) {
    u64 b = 2 + rng() % 5000, a = 1 + rng() % b; u64 g = __gcd(a, b); a /= g; b /= g;
    Completer c; c.Y = 0; set<pair<string,string>> got;
    c.onSolution = [&](const string& s) {}; 
    vector<Z> ch; c.twoTerm(Z(a), Z(b), facOf(b), Z(0), ch);
    for (auto& s : c.sols) { stringstream ss(s.substr(s.find(':') + 1)); string x, y; ss >> x >> y; got.insert({x, y}); }
    set<pair<string,string>> want;
    for (u64 x = b / a + 1; x <= 2 * b / a; x++) { // 1/y = a/b - 1/x = (a x - b)/(b x)
      u64 num = a * x - b, den = b * x; if (num == 0) continue; if (den % num == 0) { u64 y = den / num; if (y > x && y % x != 0) want.insert({to_string(x), to_string(y)}); } }
    if (got != want) { bad++; if (bad < 5) printf("mismatch a=%llu b=%llu got %zu want %zu\n", a, b, got.size(), want.size()); }
  }
  printf("two-term vs brute force: %d mismatches in 2000 random fractions\n", bad);
  // planted: T44 = core39 + H5
  vector<u64> T44 = {6,10,14,15,21,22,26,33,34,35,38,39,46,51,55,57,58,62,65,69,74,77,82,85,86,87,91,93,94,95,111,115,119,123,133,141,143,145,287,8729,10105,11687,14467,16813};
  for (int h = hFrom; h <= hTo; h++) { auto tt0 = chrono::steady_clock::now();
    vector<u64> core(T44.begin(), T44.end() - h);
    Z num(0), den(1); for (u64 n : core) { num = num * Z(n) + den; den = den * Z(n); Z g = gcd(num, den); num = divexact(num, g); den = divexact(den, g); }
    Z a = den - num, b = den;
    Fac bf; { Z r = b; for (u64 p = 2; cmpu(r, 1) > 0; p++) if (divisibleU(r, p)) { int e = 0; while (divisibleU(r, p)) { Z t; __gmpz_divexact_ui(t.v, r.v, p); r = t; e++; } bf.push_back({Z(p), e}); } }
    Completer c; c.Y = 287; c.core = core; c.coreSet = set<u64>(core.begin(), core.end());
    vector<Z> ch; c.run(a, b, bf, h, Z(core.back()), ch);
    printf("planted h=%d: completions found = %lld  n1=%llu pairs=%llu time=%.2fs\n", h, c.nSol, c.n1Tried, c.pairsTried, chrono::duration<double>(chrono::steady_clock::now()-tt0).count()); for (auto& s : c.sols) printf("  %s\n", s.substr(0, 40).c_str());
    for (auto& s : c.sols) printf("  ...%s\n", s.substr(s.size() > 60 ? s.size() - 60 : 0).c_str());
  }
}
