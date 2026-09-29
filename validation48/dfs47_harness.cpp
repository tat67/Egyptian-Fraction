// Step-1-only harness for the OLD engine (semiprime47.cpp with Step 2 disabled by a one-line sed,
// see step1_equivalence.sh): S = primes <= sb, budget K.  argv: sb K threads splitPrime outfile
#define main semiprime47_main
#include "semiprime47_step1only.cpp"
#undef main
int main(int argc, char** argv) {
    if (argc < 6) return 1;
    int sb = atoi(argv[1]), K = atoi(argv[2]), threads = atoi(argv[3]), split = atoi(argv[4]);
    Engine E(sb, K, true);
    E.dumpFile = fopen(argv[5], "w");
    auto t0 = chrono::steady_clock::now();
    E.run(threads, split);
    fclose(E.dumpFile);
    long long ms = (long long)chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - t0).count();
    printf("OLD sb %d K %d threads %d split %d nodes %lld cores %lld ms %lld\n", sb, K, threads, split,
           (long long)E.nodes, E.endStates, ms);
    return 0;
}
