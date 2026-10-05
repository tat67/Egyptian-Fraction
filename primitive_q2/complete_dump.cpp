// complete_dump.cpp -- run the exact completion (compl.h) on cores read from a dump file.
// Each line: c1 ... cj | h=H a/b.  Recomputes 1 - sum 1/c exactly and checks it equals a/b.
#include <bits/stdc++.h>
#include "gmpz.h"
#include "compl.h"
#include "msclock.h"
using namespace std; typedef unsigned long long u64;
int main(int argc, char** argv) {
  // usage: complete_dump DUMP Y [onlyH] [maxCores]
  FILE* f = fopen(argv[1], "r"); u64 Y = strtoull(argv[2], 0, 10); int onlyH = argc > 3 ? atoi(argv[3]) : 0; long long maxC = argc > 4 ? atoll(argv[4]) : -1;
  char line[1 << 16]; long long n = 0; Completer tot; long long worstMs = 0; long long sols = 0;
  auto t0 = chrono::steady_clock::now();
  while (fgets(line, sizeof line, f)) {
    string L(line); size_t bar = L.find('|'); stringstream ss(L.substr(0, bar)); vector<u64> C; u64 x; while (ss >> x) C.push_back(x);
    int h = atoi(L.substr(L.find("h=") + 2).c_str()); if (onlyH && h != onlyH) continue;
    Z num(0), den(1); for (u64 c : C) { num = num * Z(c) + den; den = den * Z(c); Z g = gcd(num, den); num = divexact(num, g); den = divexact(den, g); }
    Z a = den - num, b = den;
    string fr = L.substr(L.find(' ', L.find("h=")) + 1); fr.erase(fr.find_last_not_of(" \n\r") + 1);
    if (fr != a.str() + "/" + b.str()) { fprintf(stderr, "remainder mismatch\n"); return 2; }
    Fac bf; { Z r = b; for (u64 p = 2; cmpu(r, 1) > 0; p++) if (divisibleU(r, p)) { int e = 0; while (divisibleU(r, p)) { Z t; __gmpz_divexact_ui(t.v, r.v, p); r = t; e++; } bf.push_back({Z(p), e}); } }
    Completer c; c.Y = Y; c.core = C; c.coreSet = set<u64>(C.begin(), C.end()); c.onSolution = [](const string& s) { printf("%s\n", s.c_str()); fflush(stdout); };
    auto t1 = chrono::steady_clock::now(); vector<Z> ch; c.run(a, b, bf, h, Z(Y), ch);
    long long dt = msSince(t1); worstMs = max(worstMs, dt);
    tot.prefilterTested += c.prefilterTested; tot.prefilterRejected += c.prefilterRejected; tot.calls += c.calls; tot.fastCalls += c.fastCalls; tot.slowCalls += c.slowCalls; tot.halfEntries += c.halfEntries; tot.omegaSum += c.omegaSum; tot.n1Tried += c.n1Tried; tot.pairsTried += c.pairsTried; sols += c.nSol; n++;
    if (maxC > 0 && n >= maxC) break;
  }
  printf("prefilter=%llu/%llu fast=%llu slow=%llu halfEntries=%llu omegaSum=%llu ", tot.prefilterRejected, tot.prefilterTested, tot.fastCalls, tot.slowCalls, tot.halfEntries, tot.omegaSum); printf("cores=%lld calls=%llu n1=%llu pairs=%llu solutions=%lld time=%s worst=%s\n", n, tot.calls, tot.n1Tried, tot.pairsTried, sols, secStr(msSince(t0), 1).c_str(), secStr(worstMs, 2).c_str());
}
