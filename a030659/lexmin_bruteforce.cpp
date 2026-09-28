// Independent brute-force check (no solver, no prefilter): enumerate EVERY set
// {d_1 < ... < d_k = M} with sum 1/d_i = 1, and report the lexicographically
// smallest one (in increasing order) and the number of such sets.
// Depth-first search over d = M-1, M-2, ..., 1 (include / exclude).  Exact
// arithmetic: 1/d is w[d] = L/d with L = lcm(1..M) in unsigned __int128.
// Pruning: (i) count and value bounds from prefix sums of w;
//          (ii) once d < p for a prime p, every multiple of p has been decided,
//               and v_p(sum) >= 0 must hold: p^e | S_p, p^e || L, where S_p is
//               the sum of w[x] over chosen multiples x of p.  Both are necessary
//               conditions, so no solution is ever cut.
// Usage: lexmin_bruteforce k M
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
typedef unsigned __int128 u128;
static int M, K;
static u128 w[400], pre[400], L;
static int isprime[400];
static u128 ppow[400];                  // p^e exactly dividing L
static u128 S[400];                     // running sums per prime
static std::vector<int> primes_of[400];
static std::vector<int> cur, best;
static long long nsol = 0, nodes = 0;
static bool better(const std::vector<int>& a, const std::vector<int>& b){
    std::vector<int> x=a, y=b; std::sort(x.begin(),x.end()); std::sort(y.begin(),y.end());
    return x<y;
}
// decide d (going down); R = remaining value, c = remaining count
static void rec(int d, u128 R, int c){
    ++nodes;
    // p-adic check for prime p = d+1 (all its multiples are now decided)
    if(d+1<=M && isprime[d+1]){ int p=d+1; if(S[p]%ppow[p]) return; }
    if(c==0){
        if(R==0){
            // remaining primes <= d: no more elements, but their conditions must hold
            for(int p=2;p<=d;++p) if(isprime[p] && S[p]%ppow[p]) return;
            ++nsol;
            if(best.empty() || better(cur,best)) best=cur;
        }
        return;
    }
    if(d<c) return;
    u128 hi = pre[c], lo = pre[d]-pre[d-c];      // c largest from [1..d] / c smallest
    if(R>hi || R<lo) return;
    // include d
    if(w[d]<=R){
        cur.push_back(d);
        for(int p: primes_of[d]) S[p]+=w[d];
        rec(d-1, R-w[d], c-1);
        for(int p: primes_of[d]) S[p]-=w[d];
        cur.pop_back();
    }
    rec(d-1, R, c);
}
int main(int argc, char** argv){
    K=atoi(argv[1]); M=atoi(argv[2]);
    for(int i=2;i<=M;++i){ isprime[i]=1; for(int j=2;j*j<=i;++j) if(i%j==0){isprime[i]=0;break;} }
    L=1;
    for(int p=2;p<=M;++p) if(isprime[p]){
        u128 q=1; while(q*p<=(u128)M) q*=p;
        ppow[p]=q;
        if(L > (((u128)1<<126)/q)){ printf("L overflow\n"); return 1; }
        L*=q;
    }
    for(int d=1; d<=M; ++d){
        w[d]=L/d; pre[d]=pre[d-1]+w[d];
        for(int p=2;p<=d;++p) if(isprime[p] && d%p==0) primes_of[d].push_back(p);
    }
    cur.push_back(M);
    for(int p: primes_of[M]) S[p]+=w[M];
    rec(M-1, L-w[M], K-1);
    printf("%d %d count=%lld ", K, M, nsol);
    std::sort(best.begin(),best.end());
    for(size_t i=0;i<best.size();++i) printf(i?",%d":"%d", best[i]);
    printf(" nodes=%lld\n", nodes);
}
