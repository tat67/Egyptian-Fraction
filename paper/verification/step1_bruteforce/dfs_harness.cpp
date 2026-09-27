// Test harness: run only Step 1 (core enumeration) of semiprime47.cpp's Engine for S = primes <= sb
// and budget K, dumping every core that survives Step 1.  argv: sb K threads splitPrime outfile
#define main semiprime47_main
#include "semiprime47_step1only.cpp"
#undef main
int main(int argc, char** argv) {
    int sb = atoi(argv[1]), K = atoi(argv[2]), threads = atoi(argv[3]), split = atoi(argv[4]);
    Engine E(sb, K, true);
    E.dumpFile = fopen(argv[5], "w");
    E.run(threads, split);
    fclose(E.dumpFile);
    printf("sb %d K %d LOWN %d threads %d split %d nodes %lld cores %lld\n", sb, K, E.LOWN, threads, split,
           (long long)E.nodes, E.endStates);
    return 0;
}
