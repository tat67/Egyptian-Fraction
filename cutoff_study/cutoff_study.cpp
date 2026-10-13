// Cost of the exhaustive search as a function of the cutoff: S = primes <= SB, b0 = least prime > SB.
// Includes ../semiprime48.cpp unmodified.  Phase A: Step 1 (core search, 4 threads) with a dump of the
// surviving cores; phase B: Step 2 (all completions) on the dumped cores, in parallel.
// argv: SB K threads dumpfile [split]
#define main semiprime48_main
#include "../semiprime48.cpp"
#undef main
#include <fstream>
int main(int argc, char** argv) {
    if (argc < 5) { fprintf(stderr, "usage: SB K threads dumpfile [split]\n"); return 1; }
    int sb = atoi(argv[1]), K = atoi(argv[2]), threads = atoi(argv[3]);
    const char* dumpPath = argv[4];
    auto now = [] { return chrono::steady_clock::now(); };
    auto ms = [](auto a, auto b) { return (long long)chrono::duration_cast<chrono::milliseconds>(b - a).count(); };
    auto t0 = now();
    Engine E(sb, K);
    int split = argc > 5 ? atoi(argv[5]) : (E.m >= 9 ? E.pr[E.m - 8] : -1);   // 43 for SB = 73
    auto tTab = now();
    E.runStep2 = false;
    E.dumpFile = fopen(dumpPath, "w");
    E.run(threads, split);
    fclose(E.dumpFile);
    auto tA = now();
    // ---- phase B: Step 2 on every dumped core
    vector<string> lines; { ifstream in(dumpPath); string s; while (getline(in, s)) if (!s.empty() && s[0] == 'E') lines.push_back(s); }
    mutex mx; long long shapes = 0, alive = 0, cand = 0, prob = 0, nbb[3] = {0, 0, 0}, two = 0, unres = 0, withShape = 0;
    u128 maxBound = 0; set<vector<Elem>> sols; map<string, long long> notes;
    atomic<size_t> next{0};
    auto idx = [&](int p) { for (int i = 0; i < E.m; ++i) if (E.pr[i] == p) return i; return -1; };
    vector<thread> th;
    for (int t = 0; t < threads; ++t) th.emplace_back([&]() {
        Engine::StarCache cache;
        for (;;) {
            size_t k = next++; if (k >= lines.size()) break;
            vector<string> tok; { string w; for (char ch : lines[k]) { if (ch == ' ') { if (!w.empty()) tok.push_back(w); w.clear(); } else w += ch; } if (!w.empty()) tok.push_back(w); }
            size_t iu = 0, ic = 0; for (size_t i = 0; i < tok.size(); ++i) { if (tok[i] == "U") iu = i; if (tok[i] == "C") ic = i; }
            vector<int> rhoAll(E.m, 0); uint32_t U = 0;
            for (size_t i = iu + 1; i < ic; ++i) { int q = atoi(tok[i].c_str()); int r = atoi(strchr(tok[i].c_str(), ':') + 1); rhoAll[idx(q)] = r; U |= 1u << idx(q); }
            vector<Elem> core; u128 su = 0, sumNum = 0;
            for (size_t i = ic + 1; i < tok.size(); ++i) {
                u64 n = strtoull(tok[i].c_str(), nullptr, 10);
                for (int p : E.pr) if (n % p == 0) { core.push_back({(u128)p, (u128)(n / p)}); break; }
                su += recipUp(n); sumNum += E.Dall / n;
            }
            if (!U) { if (!core.empty() && sumNum == E.Dall) { sort(core.begin(), core.end()); lock_guard<mutex> g(mx); sols.insert(core); } continue; }
            auto R = E.complete(U, rhoAll, (int)core.size(), su, E.Dall - sumNum, cache);
            lock_guard<mutex> g(mx);
            shapes += R.shapes; alive += R.shapesAlive; cand += R.cand; prob += R.probablePrimes; two += R.twoBBsolves;
            for (int q = 0; q < 3; ++q) nbb[q] += R.aliveNbb[q];
            maxBound = max(maxBound, R.maxBound);
            if (R.shapesAlive) ++withShape;
            if (R.unresolved) { ++unres; string n = R.note.empty() ? "[b>=3 or other]" : R.note; notes[n.substr(0, 60)]++; }
            for (auto& S : R.sols) { vector<Elem> T = core; for (auto& b : S.big) T.push_back(b); sort(T.begin(), T.end()); sols.insert(T); }
        }
    });
    for (auto& x : th) x.join();
    auto tB = now();
    map<size_t, long long> bySize; for (auto& T : sols) bySize[T.size()]++;
    printf("SB %d m %d b0 %llu K %d split %d maxStar %d | step1: nodes %lld cores %zu ms %lld (tables %lld) | "
           "step2: shapes %lld alive %lld (in %lld cores; b=0 %lld b=1 %lld b>=2 %lld) stars %lld twoBB %lld bound %s "
           "unresolved %lld probable %lld ms %lld | total ms %lld | solutions:",
           sb, E.m, (unsigned long long)E.bigMin, K, split, E.maxStar, (long long)E.nodes, lines.size(), ms(t0, tA), ms(t0, tTab),
           shapes, alive, withShape, nbb[0], nbb[1], nbb[2], cand, two, u128str(maxBound).c_str(), unres, prob, ms(tA, tB), ms(t0, tB));
    for (auto& [s, c] : bySize) printf(" |T|=%zu: %lld", s, c);
    printf("\n");
    for (auto& [n, c] : notes) printf("   unresolved note x%lld: %s\n", c, n.c_str());
    fflush(stdout);
    return 0;
}
