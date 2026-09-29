// Step-1-only harness for the NEW engine (semiprime48.cpp, unmodified): S = primes <= sb, budget K;
// dumps every core that survives Step 1.  argv: sb K threads splitPrime outfile
#define main semiprime48_main
#include "../semiprime48.cpp"
#undef main
int main(int argc, char** argv) {
    if (argc < 6) return 1;
    int sb = atoi(argv[1]), K = atoi(argv[2]), threads = atoi(argv[3]), split = atoi(argv[4]);
    Engine E(sb, K);
    E.runStep2 = false;
    E.dumpFile = fopen(argv[5], "w");
    auto t0 = chrono::steady_clock::now();
    E.run(threads, split);
    fclose(E.dumpFile);
    long long ms = (long long)chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - t0).count();
    printf("NEW sb %d K %d threads %d split %d nodes %lld cores %lld ms %lld\n", sb, K, threads, split,
           (long long)E.nodes, E.endStates, ms);
    return 0;
}
