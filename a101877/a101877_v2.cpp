// a101877_v2.cpp -- exact search for OEIS A101877, revised algorithm.
//
//   a(n) = min { max S : S a finite set of distinct positive integers with sum_{x in S} 1/x = n }.
//
// The program decides, for given n and K, whether some S in [1..K] with K in S (mode "witness")
// or S in [1..K] (mode "prove") has sum_{x in S} 1/x = n.  "NONE" is a proof (all search nodes
// closed); "FOUND" prints S, which is re-verified with exact integer arithmetic.
//
// No floating point is used anywhere: all arithmetic is on 64/128-bit integers.
//
// ------------------------------------------------------------------------------------------
// Mathematics (each step preserves every solution; see a101877_a9_verified.txt for proofs)
//
// (1) p-adic integrality.  For a prime p <= K let p^E be the largest power of p that is <= K and
//     c_p(x) = p^(E - v_p(x)) * (x / p^v_p(x))^(-1) mod p^E for p | x.  For S in [1..K]:
//     v_p(sum_S 1/x) >= 0  iff  res_p(S) := sum_{x in S, p | x} c_p(x) == 0 (mod p^E).
//     (c_p(x)/p^E is the p-part of the partial-fraction expansion of 1/x.)
// (2) Candidate set U.  x is deleted if for some prime p | x no set of remaining multiples of p
//     that contains x has res_p == 0; repeated to a fixed point.  Every S with integral sum lies in U.
// (3) Exclusion form.  Delta := sum_U 1/x - n.  For S in U put E = U \ S.  Then S has sum n iff
//     res_p(E) == R_p := res_p(U) (mod p^E) for all p ("E is residue-fixing") and sum_E 1/x = Delta.
//     KEY FACT: for every residue-fixing E, sum_E 1/x - Delta is an integer (it has no prime in
//     its denominator).  A solution has cost(E) := sum_E 1/x = Delta exactly, so a lower bound
//     > Delta on the cost of every residue-fixing E of a subproblem closes it.  When 0 <= Delta < 1
//     (always the case near a(n)) every residue-fixing E has cost in {Delta, Delta+1, ...}, so a
//     residue-fixing E with cost < Delta+1 is automatically a solution.
// (4) Lower bound (Lagrangian decomposition).  Integer weights lam[p][x] with
//     sum_{p | x} lam[p][x] = floor(2^F / x).  For every residue-fixing E:
//        2^F cost(E) >= sum_x in E floor(2^F/x) = sum_p sum_{x in E, p|x} lam[p][x]
//                    >= sum_p  min { sum_{x in T} lam[p][x] : T multiples of p in U, res_p(T) == R_p }.
//     If this exceeds Dhi := sum_U ceil(2^F/x) - n 2^F >= 2^F Delta, no solution exists.
//     The per-prime minimum is an exact dynamic program by p-adic valuation level.
//     Multipliers: Polyak subgradient with an adaptive target (best bound + delta, delta halved
//     on stagnation) -- this converges to a much better dual than a fixed target above Dhi.
// (5) Branch and bound over x in E / x in S.  Reduced-cost fixing from forward/backward DP tables:
//     if every residue-fixing E of the subproblem containing x (resp. not containing x) has bound
//     > Dhi, x is fixed the other way.  Fixings are propagated in place (no new node): the node is
//     re-probed with the same multipliers (the bound can only rise when options are removed) until
//     nothing changes, then the multipliers are re-optimised briefly and the node is probed again.
//     A node whose per-prime optimal sets agree gives a residue-fixing E; if its cost < Delta+1
//     it is a solution, which is re-verified exactly.  Otherwise branch on an element on which
//     the primes disagree, choosing the one whose weaker child bound is largest (largefirst=1:
//     prefer elements with a prime factor > sqrt(K)).  The child "x in E" is explored first.
//     Every element is decided in exactly one way in each child, so the children partition the
//     node's search space: no solution is lost by branching.
// (6) Parallel (threads=T > 1): subtrees are distributed over threads through a shared stack;
//     the explored nodes still partition the search space.  threads=1 (default) is deterministic.
// Options: threads=T rootiters=I nodeiters=J reiters=R maxopt=M stall=S maxnodes=N dive=1
//          largefirst=1 quiet=1 cert=FILE (root closures: multipliers for verify_cert.py)
//          fixfile=FILE (restrict to a subproblem; only for experiments, never for proofs)
// ------------------------------------------------------------------------------------------
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <string>
#include <vector>
#include <algorithm>
#include <chrono>
#include <thread>
#include <atomic>
#include <mutex>
#include <condition_variable>
typedef long long i64; typedef unsigned long long u64; typedef __int128 i128;
static const int FR = 48;
static const i64 ONE = 1LL << FR;
static const i64 INF = (i64)4000000000000000000LL;

static i64 modinv(i64 a, i64 m){ i64 r0=m, r1=((a%m)+m)%m, s0=0, s1=1; while(r1){ i64 q=r0/r1, t=r0-q*r1; r0=r1; r1=t; t=s0-q*s1; s0=s1; s1=t; } if(r0!=1) return -1; s0%=m; if(s0<0) s0+=m; return s0; }

static int K, NT;
static std::vector<int> primes, ppw, pex;
static std::vector<char> adm;
static int vpow(int x,int p){ int v=0; while(x%p==0){ x/=p; ++v; } return v; }
static int coefp(int x,int p){ int q=ppw[p], v=0, r=x; while(r%p==0){ r/=p; ++v; } i64 pe=1; for(int i=0;i<v;++i) pe*=p; return (int)(((q/pe)%q)*modinv(r,q)%q); }

// ------------------------------------------------------------------ candidates (step 2)
static std::vector<char> candidateSet(int K){
    std::vector<char> a(K+1,1); a[0]=0;
    for(bool ch=true; ch; ){
        ch=false;
        for(int p: primes){
            int q=ppw[p]; std::vector<int> ks, cs;
            for(int d=p; d<=K; d+=p) if(a[d]){ ks.push_back(d); cs.push_back(coefp(d,p)); }
            int m=ks.size(); if(!m) continue;
            int W=(q+63)/64;
            std::vector<u64> pre((size_t)(m+1)*W,0), suf((size_t)(m+1)*W,0);
            auto get=[&](const u64* b,int r){ return (b[r>>6]>>(r&63))&1; };
            auto setb=[&](u64* b,int r){ b[r>>6]|=1ULL<<(r&63); };
            setb(&pre[0],0);
            for(int i=0;i<m;++i){ u64* x=&pre[(size_t)i*W]; u64* y=&pre[(size_t)(i+1)*W]; memcpy(y,x,8*W); for(int r=0;r<q;++r) if(get(x,r)){ int t=r+cs[i]; if(t>=q) t-=q; setb(y,t); } }
            setb(&suf[(size_t)m*W],0);
            for(int i=m-1;i>=0;--i){ u64* x=&suf[(size_t)(i+1)*W]; u64* y=&suf[(size_t)i*W]; memcpy(y,x,8*W); for(int r=0;r<q;++r) if(get(x,r)){ int t=r+cs[i]; if(t>=q) t-=q; setb(y,t); } }
            for(int i=0;i<m;++i){
                int need=(q-cs[i])%q; bool f=false; const u64* x=&pre[(size_t)i*W]; const u64* y=&suf[(size_t)(i+1)*W];
                for(int r=0;r<q && !f;++r) if(get(x,r)){ int t=need-r; if(t<0) t+=q; if(get(y,t)) f=true; }
                if(!f){ a[ks[i]]=0; ch=true; }
            }
        }
    }
    return a;
}

// ------------------------------------------------------------------ exact check of a set (step 5)
static bool exactCheck(int n,const std::vector<int>& S,std::string& why){
    std::vector<char> in(K+1,0);
    for(int x: S){ if(x<1||x>K||in[x]){ why="not distinct / out of range"; return false; } in[x]=1; }
    for(int p: primes){ i64 r=0; int q=ppw[p]; for(int x=p;x<=K;x+=p) if(in[x]) r=(r+coefp(x,p))%q; if(r){ why="residue mod "+std::to_string(q)+" nonzero"; return false; } }
    // the sum is an integer (no prime in its denominator); bracket it in (n-1, n+1)
    i128 lo=0, hi=0; for(int x: S){ lo+=ONE/x; hi+=(ONE+x-1)/x; }
    if(!((i128)(n-1)*ONE < lo && hi < (i128)(n+1)*ONE)){ why="value not in (n-1,n+1)"; return false; }
    why="ok"; return true;
}

// ------------------------------------------------------------------ blocks (one per prime)
struct Blk {
    int p, E, R;
    std::vector<int> xs;     // elements in processing order: valuation descending
    std::vector<int> v;      // valuation of xs[k]
    std::vector<int> c;      // coefficient in the level-v state space (size p^v)
    std::vector<int> Rdig;   // base-p digits of R
    std::vector<int> pw;     // p^i, i=0..E
    size_t slotBase;         // offset of this block's weights in the global weight array
    size_t fwdSize;          // sum over k of p^v[k]
};
static std::vector<Blk> B;
static std::vector<std::vector<std::pair<int,int>>> slots;   // x -> (block, k)
static size_t NSLOT=0;
static i128 Dhi;

struct Scratch { std::vector<i64> fwd, cur, nb, g, h; };

// Exact per-prime minimum (step 4).  lam: weights by slot.  fix[x]: +1 x in E forced, -1 x not in E, 0 free.
// used[k]=1 marks an optimal set.  If probe: pin[k]/pout[k] = minimum with xs[k] forced in / out.
static i64 blockDP(const Blk& b,const i64* lam,const signed char* fix,char* used,i64* pin,i64* pout,Scratch& sc){
    const int p=b.p, E=b.E; const int M=b.xs.size();
    sc.fwd.resize(b.fwdSize);
    std::vector<i64>& cur=sc.cur; cur.assign(b.pw[E],INF); cur[0]=0; int curV=E;
    size_t off=0;
    std::vector<size_t> offs; offs.resize(M);
    for(int k=0;k<M;++k){
        int v=b.v[k];
        while(curV>v){ int want=b.Rdig[E-curV]; int nS=b.pw[curV-1]; for(int s=0;s<nS;++s) cur[s]=cur[s*p+want]; cur.resize(nS); --curV; }
        int S=b.pw[v]; offs[k]=off; memcpy(&sc.fwd[off],cur.data(),sizeof(i64)*S); off+=S;
        int x=b.xs[k]; int fx=fix[x]; if(fx==-1) continue;
        i64 w=lam[k]; int cc=b.c[k]; const i64* f=&sc.fwd[offs[k]];
        if(fx==1){ for(int s=0;s<S;++s){ int t=s+cc; if(t>=S) t-=S; cur[t]= f[s]>=INF? INF : f[s]+w; } }
        else { for(int s=0;s<S;++s){ if(f[s]>=INF) continue; int t=s+cc; if(t>=S) t-=S; i64 val=f[s]+w; if(val<cur[t]) cur[t]=val; } }
    }
    int lastV=curV;
    // final drop to level 0
    i64 best; { std::vector<i64> t=cur; int V=curV; while(V>0){ int want=b.Rdig[E-V]; int nS=b.pw[V-1]; for(int s=0;s<nS;++s) t[s]=t[s*p+want]; --V; } best=t[0]; }
    if(used) memset(used,0,M);
    if(pin){ for(int k=0;k<M;++k){ pin[k]=INF; pout[k]=INF; } }
    if(best>=INF) return INF;
    int sEnd=0; { int mul=1; for(int d=E-lastV; d<E; ++d){ sEnd+=b.Rdig[d]*mul; mul*=p; } }
    if(used){
        int s=sEnd, V=lastV; i64 val=best;
        for(int k=M-1;k>=0;--k){
            int v=b.v[k]; while(V<v){ s=s*p+b.Rdig[E-V-1]; ++V; }
            int x=b.xs[k]; int fx=fix[x]; if(fx==-1) continue;
            const i64* f=&sc.fwd[offs[k]]; int S=b.pw[v];
            if(fx!=1 && f[s]==val) continue;                       // excluded
            used[k]=1; s-=b.c[k]; if(s<0) s+=S; val-=lam[k];
        }
    }
    if(pin){
        std::vector<i64>& g=sc.g; std::vector<i64>& h=sc.h;
        g.assign(b.pw[lastV],INF); g[sEnd]=0; int V=lastV;
        for(int k=M-1;k>=0;--k){
            int v=b.v[k];
            while(V<v){ int nS=b.pw[V+1]; h.assign(nS,INF); int d=b.Rdig[E-V-1]; for(int s=0;s<b.pw[V];++s) if(g[s]<INF) h[s*p+d]=g[s]; g.swap(h); ++V; }
            int x=b.xs[k]; int cc=b.c[k]; int S=b.pw[v]; i64 w=lam[k]; int fx=fix[x];
            const i64* f=&sc.fwd[offs[k]];
            i64 bin=INF, bout=INF;
            for(int s=0;s<S;++s){ if(f[s]>=INF) continue; int t=s+cc; if(t>=S) t-=S;
                if(fx!=-1 && g[t]<INF){ i64 val=f[s]+w+g[t]; if(val<bin) bin=val; }
                if(fx!=1 && g[s]<INF){ i64 val=f[s]+g[s]; if(val<bout) bout=val; } }
            pin[k]=bin; pout[k]=bout;
            h.assign(S,INF);
            for(int s=0;s<S;++s){ i64 bst=INF; if(fx!=1) bst=g[s]; int t=s+cc; if(t>=S) t-=S; if(fx!=-1 && g[t]<INF && g[t]+w<bst) bst=g[t]+w; h[s]=bst; }
            g.swap(h);
        }
    }
    return best;
}

// ------------------------------------------------------------------ node evaluation
struct NodeState {
    std::vector<signed char> fix;   // per x
    std::vector<i64> lam;           // per slot
    int depth=0;
};
static int LARGEFIRST=0; static std::vector<char> isLargeLayer;
static int ROOTIT=6000, NODEIT=100, REIT=40, MAXOPT=4, STALL=30, DIVE=0, THREADS=1, VERBOSE=1;
static u64 MAXNODES=0;
static std::atomic<u64> nodes(0), lpPasses(0);
static std::atomic<bool> stopAll(false), budgetHit(false);
static std::mutex outMu;
static std::vector<int> foundS;
static std::chrono::steady_clock::time_point T0;
static long long ms(){ return std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-T0).count(); }
static i64 rootGap=0;
static std::string CERT, FIXFILE; static long long LASTREP=0; static std::atomic<int> maxDepth(0); static std::vector<i64> rootLamBest; static std::mutex certMu;

struct Eval { i128 LB; bool infeasible; std::vector<char> used; std::vector<i64> val; };

static void evalAll(const NodeState& nd,Eval& ev,Scratch& sc,std::vector<i64>* pin,std::vector<i64>* pout){
    ev.used.resize(NSLOT); ev.val.assign(B.size(),0); ev.LB=0; ev.infeasible=false;
    for(size_t i=0;i<B.size();++i){
        const Blk& b=B[i];
        i64 v=blockDP(b,&nd.lam[b.slotBase],nd.fix.data(),&ev.used[b.slotBase], pin? &(*pin)[b.slotBase]:nullptr, pout? &(*pout)[b.slotBase]:nullptr, sc);
        ev.val[i]=v; if(v>=INF){ ev.infeasible=true; } else ev.LB+=v;
    }
    ++lpPasses;
}
static bool consistent(const NodeState& nd,const Eval& ev){
    for(int x=2;x<=K;++x){ auto& sl=slots[x]; if(sl.size()<2) continue; int su=0; for(auto s: sl) su+=ev.used[B[s.first].slotBase+s.second]; if(su!=0 && su!=(int)sl.size()) return false; }
    return true;
}
// subgradient with adaptive Polyak target; returns best LB and leaves nd.lam at the best multipliers
static i128 optimize(NodeState& nd,int iters,Eval& best,Scratch& sc,bool& cons){
    Eval ev; i128 bestLB=-((i128)INF); std::vector<i64> bestLam=nd.lam; cons=false;
    i128 delta=0; int noImp=0;
    for(int it=0; it<iters; ++it){
        evalAll(nd,ev,sc,nullptr,nullptr);
        if(ev.infeasible){ best=ev; best.infeasible=true; return INF; }
        bool c=consistent(nd,ev);
        if(ev.LB>bestLB){ bestLB=ev.LB; bestLam=nd.lam; best=ev; cons=c; noImp=0; } else ++noImp;
        if(ev.LB>Dhi || c) break;
        if(delta==0){ delta=(Dhi-ev.LB)/2+1; }
        if(noImp>0 && noImp%STALL==0){ delta=delta/2+1; if(delta<1024) break; }
        i128 target=bestLB+delta, gg=0;
        std::vector<std::pair<size_t,int>> gs;
        for(int x=2;x<=K;++x){
            auto& sl=slots[x]; int k=sl.size(); if(k<2 || nd.fix[x]) continue;
            int su=0; for(auto s: sl) su+=ev.used[B[s.first].slotBase+s.second];
            if(su==0||su==k) continue;
            for(auto s: sl){ size_t id=B[s.first].slotBase+s.second; int g=k*ev.used[id]-su; if(g){ gs.push_back({id,g}); gg+=(i128)g*g; } }
        }
        if(gg==0) break;
        i64 step=(i64)((target-ev.LB)/gg); if(step<1) step=1;
        for(auto& g: gs) nd.lam[g.first]+=step*g.second;
    }
    nd.lam=bestLam;
    return bestLB;
}

static std::vector<int> setFromE(const std::vector<char>& inE){ std::vector<int> S; for(int x=1;x<=K;++x) if(adm[x] && !inE[x]) S.push_back(x); return S; }

// shared work stack
static std::mutex stMu; static std::condition_variable stCv;
static std::vector<NodeState> stackNodes; static int busy=0;

static void report(const char* tag,const NodeState& nd,i128 LB){
    if(!VERBOSE) return;
    std::lock_guard<std::mutex> lk(outMu);
    fprintf(stderr,"  %s node %llu depth %d LB-Dhi=%lld passes=%llu t=%lldms\n",tag,(unsigned long long)nodes.load(),nd.depth,(long long)(LB-Dhi),(unsigned long long)lpPasses.load(),ms());
}

// process one node; returns children (0, 1 or 2) through out
static void processNode(NodeState nd,Scratch& sc,std::vector<NodeState>& out){
    if(stopAll) return;
    u64 id=++nodes;
    { int d=maxDepth.load(); while(nd.depth>d && !maxDepth.compare_exchange_weak(d,nd.depth)){} }
    if(VERBOSE){ long long t=ms(); if(t-LASTREP>30000){ LASTREP=t; std::lock_guard<std::mutex> lk(outMu); fprintf(stderr,"  progress nodes=%llu passes=%llu maxdepth=%d depth=%d t=%lldms\n",(unsigned long long)id,(unsigned long long)lpPasses.load(),maxDepth.load(),nd.depth,t); } }
    if(MAXNODES && id>MAXNODES){ budgetHit=true; stopAll=true; return; }
    Eval ev; bool cons=false;
    i128 LB=0; int optRounds=0; bool dirty=true, fixedSinceOpt=false;
    std::vector<i64> pin(NSLOT), pout(NSLOT);
    i128 L2=0;
    for(;;){
        if(dirty){
            // (re-)optimise the multipliers: long at the root, NODEIT at a new node, REIT after fixings
            int it = (nd.depth==0 && optRounds==0)? ROOTIT : (optRounds==0? NODEIT : REIT);
            LB=optimize(nd, it, ev, sc, cons);
            if(nd.depth==0 && optRounds==0){ rootGap=(i64)(LB-Dhi); std::lock_guard<std::mutex> lk(certMu); rootLamBest=nd.lam; }
            ++optRounds; dirty=false; fixedSinceOpt=false;
            if(ev.infeasible || LB>Dhi){ if(id%200==0||nd.depth<3) report("closed",nd,LB); return; }
        }
        // reduced-cost fixing (step 5): forward/backward tables at the current multipliers
        evalAll(nd,ev,sc,&pin,&pout);
        if(ev.infeasible || ev.LB>Dhi) return;
        L2=ev.LB; if(L2>LB) LB=L2; cons=consistent(nd,ev);
        int changed=0;
        for(int x=2;x<=K;++x){
            if(!adm[x] || nd.fix[x]) continue;
            auto& sl=slots[x]; if(sl.empty()) continue;
            i128 lin=L2, lout=L2; bool infIn=false, infOut=false;
            for(auto s: sl){ size_t sid=B[s.first].slotBase+s.second; i64 opt=ev.val[s.first];
                if(pin[sid]>=INF) infIn=true; else lin+=pin[sid]-opt;
                if(pout[sid]>=INF) infOut=true; else lout+=pout[sid]-opt; }
            bool cutIn=infIn||lin>Dhi, cutOut=infOut||lout>Dhi;
            if(cutIn && cutOut) return;                                // no completion
            if(cutIn){ nd.fix[x]=-1; ++changed; } else if(cutOut){ nd.fix[x]=1; ++changed; }
        }
        if(changed){ fixedSinceOpt=true; continue; }                   // re-probe with the same multipliers
        if(fixedSinceOpt && optRounds<MAXOPT){ dirty=true; continue; }  // short re-optimisation, then probe again
        if(cons){
            std::vector<char> inE(K+1,0); i128 lossLo=0; int ne=0;
            for(int x=2;x<=K;++x){ auto& sl=slots[x]; if(sl.empty()) continue; if(ev.used[B[sl[0].first].slotBase+sl[0].second]){ inE[x]=1; lossLo+=ONE/x; ++ne; } }
            if(lossLo + ne + K + 1 < Dhi + ONE){
                std::vector<int> S=setFromE(inE); std::string why;
                if(exactCheck(NT,S,why)){ std::lock_guard<std::mutex> lk(outMu); if(foundS.empty()) foundS=S; stopAll=true; return; }
                else { std::lock_guard<std::mutex> lk(outMu); fprintf(stderr,"internal: consistent set failed exact check (%s)\n",why.c_str()); }
            }
        }
        // branching element: maximise the weaker child's bound among disagreeing elements
        int bestX=-1; i128 bestScore=-1; bool inFirst=true;
        for(int x=2;x<=K;++x){
            if(!adm[x] || nd.fix[x]) continue;
            auto& sl=slots[x]; if(sl.size()<2) continue;
            int su=0; for(auto s: sl) su+=ev.used[B[s.first].slotBase+s.second];
            if(su==0 || su==(int)sl.size()) continue;
            i128 lin=L2, lout=L2;
            for(auto s: sl){ size_t sid=B[s.first].slotBase+s.second; i64 opt=ev.val[s.first]; lin+=pin[sid]-opt; lout+=pout[sid]-opt; }
            i128 sc2 = DIVE ? (lin>lout? lin-lout : lout-lin) : (lin<lout? lin:lout);
            if(LARGEFIRST && isLargeLayer[x]) sc2+=(i128)1<<100;           // large-prime layer first
            if(sc2>bestScore){ bestScore=sc2; bestX=x; inFirst=(lin<=lout); }
        }
        if(bestX<0){
            if(cons){ return; }   // consistent but cost >= Delta+1: closed
            for(int x=2;x<=K && bestX<0;++x){ if(adm[x] && !nd.fix[x] && !slots[x].empty()) bestX=x; }
            if(bestX<0) return;
        }
        if(id%200==0||nd.depth<3) report("branch",nd,LB);
        NodeState a=nd, b2=nd; a.depth=b2.depth=nd.depth+1;
        int first = (DIVE && !inFirst) ? -1 : 1;
        a.fix[bestX]=first; b2.fix[bestX]=-first;
        out.push_back(std::move(b2)); out.push_back(std::move(a));       // a (first) is popped first
        return;
    }
}

static void worker(){
    Scratch sc;
    std::vector<NodeState> local;
    for(;;){
        if(local.empty()){
            std::unique_lock<std::mutex> lk(stMu);
            stCv.wait(lk,[]{ return stopAll || !stackNodes.empty() || busy==0; });
            if(stopAll || (stackNodes.empty() && busy==0)){ stCv.notify_all(); return; }
            local.push_back(std::move(stackNodes.back())); stackNodes.pop_back(); ++busy;
        }
        NodeState nd=std::move(local.back()); local.pop_back();
        std::vector<NodeState> ch; processNode(std::move(nd),sc,ch);
        for(auto& c: ch) local.push_back(std::move(c));
        // share work: give away the oldest local node if others are idle
        if(local.size()>1){
            std::lock_guard<std::mutex> lk(stMu);
            if(stackNodes.size()<(size_t)THREADS){ stackNodes.push_back(std::move(local.front())); local.erase(local.begin()); stCv.notify_one(); }
        }
        if(local.empty()){
            std::lock_guard<std::mutex> lk(stMu); --busy; stCv.notify_all();
        }
        if(stopAll){ std::lock_guard<std::mutex> lk(stMu); stCv.notify_all(); if(!local.empty()){ --busy; } return; }
    }
}

int main(int argc,char** argv){
    if(argc<4){ fprintf(stderr,"usage: %s prove|witness|check n K [set] [threads=T rootiters=I nodeiters=J stall=S maxnodes=N dive=1 quiet=1]\n",argv[0]); return 1; }
    std::string mode=argv[1]; NT=atoi(argv[2]); K=atoi(argv[3]); std::string setArg;
    for(int i=4;i<argc;++i){ std::string a=argv[i];
        if(a.rfind("threads=",0)==0) THREADS=atoi(a.c_str()+8);
        else if(a.rfind("rootiters=",0)==0) ROOTIT=atoi(a.c_str()+10);
        else if(a.rfind("nodeiters=",0)==0) NODEIT=atoi(a.c_str()+10);
        else if(a.rfind("stall=",0)==0) STALL=atoi(a.c_str()+6);
        else if(a.rfind("reiters=",0)==0) REIT=atoi(a.c_str()+8);
        else if(a.rfind("maxopt=",0)==0) MAXOPT=atoi(a.c_str()+7);
        else if(a.rfind("largefirst=",0)==0) LARGEFIRST=atoi(a.c_str()+11);
        else if(a.rfind("maxnodes=",0)==0) MAXNODES=strtoull(a.c_str()+9,0,10);
        else if(a.rfind("dive=",0)==0) DIVE=atoi(a.c_str()+5);
        else if(a.rfind("quiet=",0)==0) VERBOSE=!atoi(a.c_str()+6);
        else if(a.rfind("cert=",0)==0) CERT=a.substr(5);
        else if(a.rfind("fixfile=",0)==0) FIXFILE=a.substr(8);
        else setArg=a; }
    T0=std::chrono::steady_clock::now();
    std::vector<char> isp(K+1,1); isp[0]=0; if(K>=1) isp[1]=0;
    for(int i=2;(i64)i*i<=K;++i) if(isp[i]) for(int j=i*i;j<=K;j+=i) isp[j]=0;
    ppw.assign(K+1,0); pex.assign(K+1,0);
    for(int p=2;p<=K;++p) if(isp[p]){ primes.push_back(p); int q=1,e=0; while((i64)q*p<=K){ q*=p; ++e; } ppw[p]=q; pex[p]=e; }
    if(mode=="check"){
        std::vector<int> S; size_t pos=0; while(pos<setArg.size()){ size_t c=setArg.find(',',pos); if(c==std::string::npos) c=setArg.size(); S.push_back(atoi(setArg.substr(pos,c-pos).c_str())); pos=c+1; }
        int mx=0; for(int x: S) mx=std::max(mx,x); std::string why; bool ok=exactCheck(NT,S,why);
        printf("check n=%d K=%d |S|=%zu max=%d: %s (%s)\n",NT,K,S.size(),mx, ok&&mx==K?"VALID witness":"INVALID", why.c_str());
        return ok&&mx==K?0:1;
    }
    adm=candidateSet(K);
    bool needK=(mode=="witness");
    int nU=0; for(int x=1;x<=K;++x) nU+=adm[x];
    if(needK && !adm[K]){ printf("n=%d K=%d mode=%s NONE: %d is not a candidate (cannot occur in any set with integral sum) nodes=0\n",NT,K,mode.c_str(),K); return 0; }
    i128 SU=0; for(int x=1;x<=K;++x) if(adm[x]) SU+=(ONE+x-1)/x;
    Dhi=SU-(i128)NT*ONE;
    if(Dhi<0){ printf("n=%d K=%d mode=%s NONE: sum of all candidates is below n nodes=0\n",NT,K,mode.c_str()); return 0; }
    for(int p: primes){
        Blk b; b.p=p; b.E=pex[p]; int q=ppw[p]; i64 R=0;
        std::vector<int> ms; for(int d=p;d<=K;d+=p) if(adm[d]){ ms.push_back(d); R=(R+coefp(d,p))%q; }
        if(ms.empty()) continue;
        b.R=(int)R; b.Rdig.assign(b.E,0); { int r=b.R; for(int d=0;d<b.E;++d){ b.Rdig[d]=r%p; r/=p; } }
        b.pw.assign(b.E+1,1); for(int i=1;i<=b.E;++i) b.pw[i]=b.pw[i-1]*p;
        for(int v=b.E; v>=1; --v) for(int x: ms) if(vpow(x,p)==v){ b.xs.push_back(x); b.v.push_back(v); b.c.push_back(coefp(x,p)/b.pw[b.E-v]); }
        b.fwdSize=0; for(int v: b.v) b.fwdSize+=b.pw[v];
        b.slotBase=NSLOT; NSLOT+=b.xs.size();
        B.push_back(b);
    }
    isLargeLayer.assign(K+1,0); for(int p: primes) if((i64)p*p>K) for(int x=p;x<=K;x+=p) isLargeLayer[x]=1;
    slots.assign(K+1,{}); for(int i=0;i<(int)B.size();++i) for(int k=0;k<(int)B[i].xs.size();++k) slots[B[i].xs[k]].push_back({i,k});
    NodeState root; root.fix.assign(K+1,0); if(needK) root.fix[K]=-1;   // K stays in S
    if(!FIXFILE.empty()){
        // optional restriction to a subproblem (used for neighbourhood searches, never for proofs of the full claim):
        // lines "x s": s=+1 forces x into E (x not in S), s=-1 forces x out of E (x in S)
        FILE* f=fopen(FIXFILE.c_str(),"r"); int x,sg,cnt=0;
        while(f && fscanf(f,"%d %d",&x,&sg)==2){ if(x>=1 && x<=K && adm[x]){ root.fix[x]=(signed char)sg; ++cnt; } }
        if(f) fclose(f);
        fprintf(stderr,"fixfile %s: %d fixings (search restricted to a subproblem)\n",FIXFILE.c_str(),cnt);
    }
    root.lam.assign(NSLOT,0);
    for(int x=2;x<=K;++x) if(adm[x]){ i64 bb=ONE/x; int k=slots[x].size(); for(int t=0;t<k;++t){ auto s=slots[x][t]; root.lam[B[s.first].slotBase+s.second]=bb/k+(t==0?bb%k:0); } }
    fprintf(stderr,"n=%d K=%d mode=%s |U|=%d primes=%zu slots=%zu threads=%d Dhi=%lld\n",NT,K,mode.c_str(),nU,B.size(),NSLOT,THREADS,(long long)Dhi);
    stackNodes.push_back(std::move(root));
    std::vector<std::thread> th; for(int t=0;t<THREADS;++t) th.emplace_back(worker); for(auto& t: th) t.join();
    long long tms=ms();
    if(!foundS.empty()){
        auto& S=foundS; printf("n=%d K=%d mode=%s FOUND |S|=%zu nodes=%llu passes=%llu maxdepth=%d root_LB-Dhi=%lld time_ms=%lld S=",NT,K,mode.c_str(),S.size(),(unsigned long long)nodes.load(),(unsigned long long)lpPasses.load(),maxDepth.load(),(long long)rootGap,tms);
        for(size_t i=0;i<S.size();++i) printf(i?",%d":"%d",S[i]);
        printf("\n");
    } else if(budgetHit){
        printf("n=%d K=%d mode=%s UNDECIDED (node budget) nodes=%llu passes=%llu root_LB-Dhi=%lld time_ms=%lld\n",NT,K,mode.c_str(),(unsigned long long)nodes.load(),(unsigned long long)lpPasses.load(),(long long)rootGap,tms);
    } else {
        if(!CERT.empty() && nodes.load()==1 && rootGap>0){
            // root closure: the multipliers alone prove the claim; checked independently by verify_cert.py
            FILE* f=fopen(CERT.c_str(),"w");
            fprintf(f,"# A101877 lower-bound certificate: n K F  then lines  p x lambda  (sum over p of lambda <= floor(2^F/x))\n%d %d %d\n",NT,K,FR);
            for(auto& b: B) for(size_t k=0;k<b.xs.size();++k) fprintf(f,"%d %d %lld\n",b.p,b.xs[k],(long long)rootLamBest[b.slotBase+k]);
            fclose(f);
        }
        printf("n=%d K=%d mode=%s NONE (all nodes closed) nodes=%llu passes=%llu maxdepth=%d root_LB-Dhi=%lld time_ms=%lld\n",NT,K,mode.c_str(),(unsigned long long)nodes.load(),(unsigned long long)lpPasses.load(),maxDepth.load(),(long long)rootGap,tms);
    }
    return 0;
}
