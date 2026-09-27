// Runs the Engine of semiprime47.cpp (unmodified source, included verbatim) with budget K = 46,
// dumps every core surviving Step 1, and prints the same statistics as the programs.
// Purpose: (i) re-derive the budget-46 counts with the second program's Step 2 code;
//          (ii) produce cores46.txt for the independent Python Step-2 check (complete47.py, KT=46).
#define main semiprime47_main
#include "/home/user/Egyptian-Fraction/semiprime47.cpp"
#undef main
int main(int argc, char** argv) {
    int threads = argc > 1 ? atoi(argv[1]) : 4;
    Engine E(73, 46, true);
    E.dumpFile = fopen("cores46.txt", "w");
    printf("largest possible star: %d\n", E.maxStar); fflush(stdout);
    E.run(threads, 61);
    fclose(E.dumpFile);
    printf("search nodes           : %lld\n", (long long)E.nodes);
    printf("cores passing Step 1   : %lld (of which |C|+|U| = 46 with U nonempty: %lld)\n", E.endStates, E.endTight);
    printf("completion shapes      : %lld tried, %lld pass parity+value (in %lld cores), %lld candidate stars\n",
           E.shapesTried, E.shapesAlive, E.coresWithShape, E.starCands);
    printf("unresolved cores       : %lld\n", E.unresolved);
    printf("probable primes used   : %lld\n", E.probablePrimes);
    printf("solutions              : %zu\n", E.solutionSet.size());
    return 0;
}
