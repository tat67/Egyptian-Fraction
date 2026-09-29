// Runs Step 2 of semiprime48.cpp (unmodified) on the cores of a dump file (format of --dump):
// every completion of every listed core, with the program's statistics.  argv: dump [K=48]
#define main semiprime48_main
#include "../semiprime48.cpp"
#undef main
int main(int argc, char** argv) {
    if (argc < 2) return 1;
    int K = argc > 2 ? atoi(argv[2]) : 48;
    Engine E(73, K);
    Engine::StarCache cache;
    FILE* f = fopen(argv[1], "r"); if (!f) return 1;
    char buf[1 << 16];
    long long cores = 0, unresolved = 0, alive = 0, two = 0;
    set<vector<Elem>> sols;
    while (fgets(buf, sizeof buf, f)) {
        vector<string> tok; char* s = strtok(buf, " \n");
        while (s) { tok.push_back(s); s = strtok(nullptr, " \n"); }
        if (tok.empty() || tok[0] != "E") continue;
        ++cores;
        size_t iu = 0, ic = 0; for (size_t i = 0; i < tok.size(); ++i) { if (tok[i] == "U") iu = i; if (tok[i] == "C") ic = i; }
        vector<int> rhoAll(E.m, 0); uint32_t U = 0;
        auto idx = [&](int p) { for (int i = 0; i < E.m; ++i) if (E.pr[i] == p) return i; return -1; };
        for (size_t i = iu + 1; i < ic; ++i) { int q = atoi(tok[i].c_str()); int r = atoi(strchr(tok[i].c_str(), ':') + 1); rhoAll[idx(q)] = r; U |= 1u << idx(q); }
        vector<Elem> core; u128 su = 0, sumNum = 0;
        for (size_t i = ic + 1; i < tok.size(); ++i) {
            u64 n = strtoull(tok[i].c_str(), nullptr, 10);
            for (int p : E.pr) if (n % p == 0) { core.push_back({(u128)p, (u128)(n / p)}); break; }
            su += recipUp(n); sumNum += E.Dall / n;
        }
        // recompute the residues from the core and compare with the dump
        vector<int> rr(E.m, 0);
        for (auto& e : core) { int a = idx((int)e.first), b = idx((int)e.second);
            rr[a] = (int)((rr[a] + invmodPrime((u64)e.second, (u64)e.first)) % e.first);
            rr[b] = (int)((rr[b] + invmodPrime((u64)e.first, (u64)e.second)) % e.second); }
        if (rr != rhoAll) { printf("residue mismatch in core %lld\n", cores); return 1; }
        if (!U) { if (sumNum == E.Dall) { sort(core.begin(), core.end()); sols.insert(core); } continue; }
        auto R = E.complete(U, rhoAll, (int)core.size(), su, E.Dall - sumNum, cache);
        alive += R.shapesAlive; two += R.twoBBsolves;
        if (R.unresolved) { ++unresolved; printf("UNRESOLVED core %lld:%s\n", cores, R.note.c_str()); }
        for (auto& S : R.sols) { vector<Elem> T = core; for (auto& b : S.big) T.push_back(b); sort(T.begin(), T.end()); sols.insert(T); }
    }
    printf("cores %lld, surviving shapes %lld, two-big-big-edge component problems %lld, unresolved %lld, solutions %zu\n",
           cores, alive, two, unresolved, sols.size());
    for (auto& T : sols) {
        vector<u128> v; for (auto& e : T) v.push_back(e.first * e.second); sort(v.begin(), v.end());
        printf("%zu", v.size()); for (u128 x : v) printf(" %s", u128str(x).c_str()); printf("\n");
    }
    return 0;
}
