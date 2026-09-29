// a101877.cpp -- exact computation of OEIS A101877.
//
//   a(n) = least k such that some set S of distinct positive integers with
//          max(S) = k has sum_{x in S} 1/x = n.
//
// No floating point is used anywhere: all arithmetic is on 64/128-bit integers.
//
// Usage
//   a101877 prove   n K     is there S in [1..K] with sum 1/x = n ?  "NONE" proves a(n) > K
//   a101877 witness n K     is there such S with K in S ?            prints S if found
//   a101877 count   n K     number of S with max(S) = K              (all witness sets)
//   a101877 check   n K s1,s2,...   exact verification of a given set
// Options (after the positional arguments): threads=T rootiters=I nodeiters=J maxnodes=N noimp=M cert=FILE dive=1
//
// ---------------------------------------------------------------------------------
// Mathematics
// (1) Integrality.  For a prime p <= K let p^E be the largest power of p that is
//     <= K.  For a finite S in [1..K],  sum 1/x  has v_p >= 0  iff
//        res_p(S) := sum_{x in S, p|x} p^(E - v_p(x)) * (x / p^v_p(x))^(-1)  == 0 (mod p^E).
// (2) Candidates U.  x is removed if, for some prime p | x, no set of (remaining)
//     multiples of p containing x has res_p == 0 (subset sum over residues);
//     repeated until nothing changes.  Every S with an integral sum lies in U.
// (3) Exclusion form.  Let Delta = sum_{x in U} 1/x - n.  For S in U put E = U \ S.
//     S has sum n  iff  (a) res_p(E) == res_p(U) =: R_p for every prime p, and
//     (b) sum_{x in E} 1/x = Delta.  Given (a), sum_S is an integer, so sum_E is
//     congruent to Delta mod 1; hence (b) can be replaced by (b') sum_E 1/x < Delta + 1,
//     and every residue-fixing E has sum_E = Delta or sum_E >= Delta + 1.
// (4) Lower bound (Lagrangian decomposition).  Split each 1/x among the primes
//     dividing x: integers lam[p][x] (any sign) with sum_p lam[p][x] = floor(2^F/x) <= 2^F/x.
//     For every residue-fixing E,
//        2^F * sum_E 1/x  >=  sum_p  min { sum_{x in T} lam[p][x] : T a set of multiples
//                                          of p in U with res_p(T) == R_p }.
//     If the bound exceeds 2^F * Delta, no S exists (by (3)).  The weights are
//     improved by subgradient steps.  The per-prime minimum is an exact dynamic
//     program over residues, organised by p-adic valuation: a multiple x with
//     v_p(x) = v only changes the top v base-p digits of the residue, so once all
//     multiples with valuation >= E - d are processed, digit d is final.  The state
//     at valuation level v is the top v digits (p^v values); total work ~ E * K.
// (5) Branch and bound.  Nodes fix some x in E or in S.  A node is closed when its
//     bound exceeds Delta.  Reduced-cost fixing: forward/backward tables give, for
//     every free x, the bound with x forced into or out of E; if that exceeds
//     Delta the opposite is fixed.  If all primes' optimal sets agree, their union
//     E is residue-fixing; if sum_E < Delta + 1 it is a solution (and is verified
//     again exactly).  Otherwise branch on an element on which the primes disagree.
// (6) Exact verification of a solution: all residues res_p(S) == 0 (exact integer
//     arithmetic for every prime p <= K) and the 2^-F fixed-point enclosure of
//     sum_S 1/x lies inside (n-1, n+1); an integer there equals n.
// ---------------------------------------------------------------------------------
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
typedef long long i64; typedef unsigned long long u64; typedef __int128 i128;

static const int FR = 48;                 // fixed point: 1/x ~ floor(2^48 / x)
static const i64 ONE = 1LL << FR;
static const i64 INF = (i64)4e18;

static i64 modinv(i64 a, i64 m){ i64 r0=m, r1=((a%m)+m)%m, s0=0, s1=1; while(r1){ i64 q=r0/r1, t=r0-q*r1; r0=r1; r1=t; t=s0-q*s1; s0=s1; s1=t; } if(r0!=1) return -1; s0%=m; if(s0<0) s0+=m; return s0; }

static int K, NT;
static std::vector<int> primes, ppow, pexp;
static int THREADS = 4, ROOTIT = 4000, NODEIT = 200, NOIMP = 80, DIVE = 0;
static u64 MAXNODES = 0;
static int vpow(int x,int p){ int v=0; while(x%p==0){ x/=p; ++v; } return v; }
static int coefp(int x,int p){ int q=ppow[p], v=0, r=x; while(r%p==0){ r/=p; ++v; } i64 pe=1; for(int i=0;i<v;++i) pe*=p; return (int)(((q/pe)%q)*modinv(r,q)%q); }

// ------------------------------------------------------------------ candidates
static std::vector<char> candidateSet(int K){
    std::vector<char> adm(K+1,1); adm[0]=0;
    for(bool ch=true; ch; ){
        ch=false;
        for(int p: primes){
            int q=ppow[p]; std::vector<int> ks, cs;
            for(int d=p; d<=K; d+=p) if(adm[d]){ ks.push_back(d); cs.push_back(coefp(d,p)); }
            int m=ks.size(); if(!m) continue;
            int W=(q+63)/64;
            std::vector<u64> pre((size_t)(m+1)*W,0), suf((size_t)(m+1)*W,0);
            auto get=[&](const u64* b,int r){ return (b[r>>6]>>(r&63))&1; };
            auto setb=[&](u64* b,int r){ b[r>>6]|=1ULL<<(r&63); };
            setb(&pre[0],0);
            for(int i=0;i<m;++i){ u64* a=&pre[(size_t)i*W]; u64* b=&pre[(size_t)(i+1)*W]; memcpy(b,a,8*W); for(int r=0;r<q;++r) if(get(a,r)){ int t=r+cs[i]; if(t>=q) t-=q; setb(b,t); } }
            setb(&suf[(size_t)m*W],0);
            for(int i=m-1;i>=0;--i){ u64* a=&suf[(size_t)(i+1)*W]; u64* b=&suf[(size_t)i*W]; memcpy(b,a,8*W); for(int r=0;r<q;++r) if(get(a,r)){ int t=r+cs[i]; if(t>=q) t-=q; setb(b,t); } }
            for(int i=0;i<m;++i){
                int need=(q-cs[i])%q; bool f=false; const u64* a=&pre[(size_t)i*W]; const u64* b=&suf[(size_t)(i+1)*W];
                for(int r=0;r<q && !f;++r) if(get(a,r)){ int t=need-r; if(t<0) t+=q; if(get(b,t)) f=true; }
                if(!f){ adm[ks[i]]=0; ch=true; }
            }
        }
    }
    return adm;
}

// ------------------------------------------------------------------ exact check of a set
static bool exactCheck(int n,const std::vector<int>& S,std::string& why){
    std::vector<char> in(K+1,0);
    for(int x: S){ if(x<1||x>K||in[x]){ why="not distinct / out of range"; return false; } in[x]=1; }
    for(int p: primes){ i64 r=0; int q=ppow[p]; for(int x=p;x<=K;x+=p) if(in[x]) r=(r+coefp(x,p))%q; if(r){ why="residue mod "+std::to_string(q)+" nonzero"; return false; } }
    i128 lo=0, hi=0; for(int x: S){ lo+=ONE/x; hi+=(ONE+x-1)/x; }
    // the sum is an integer (all residues 0) with lo <= 2^F*sum <= hi; it equals n iff inside (n-1, n+1)
    if(!((i128)(n-1)*ONE < lo && hi < (i128)(n+1)*ONE)){ why="value not in (n-1,n+1)"; return false; }
    why="ok"; return true;
}

// ------------------------------------------------------------------ problem data
struct Level { int v; std::vector<int> idx; };              // positions in xs with valuation v
struct PP { int p, q, E, R; std::vector<int> xs; std::vector<int> w; std::vector<Level> lev; std::vector<int> Rdig; };
static std::vector<PP> P;
static std::vector<std::vector<std::pair<int,int>>> slots;   // x -> (prime index, position in xs)
static std::vector<char> adm;
static i128 Dhi;                                            // >= 2^F * Delta

// Level DP for one prime.  lam: weights by position.  fix: per x (+1 must be in T, -1 must not, 0 free).
// Returns the minimum (INF if no valid T); used[pos]=1 marks an optimal T.
// If probe != nullptr: probe[pos] = (minimum with pos forced into T, minimum with pos forced out of T).
static i64 primeDP(int pi,const std::vector<i64>& lam,const std::vector<signed char>& fix,std::vector<char>& used,
                   std::vector<std::pair<i64,i64>>* probe){
    PP& a=P[pi]; int p=a.p;
    int nlev=a.lev.size();
    std::vector<int> order, levOf;
    for(int L=0;L<nlev;++L) for(int id: a.lev[L].idx){ order.push_back(id); levOf.push_back(L); }
    int M=order.size();
    std::vector<std::vector<i64>> before(probe? M:0);
    std::vector<std::vector<unsigned char>> take(M);
    std::vector<i64> cur; int curV=a.E;                     // state = top curV base-p digits of the residue
    { int nS=1; for(int i=0;i<a.E;++i) nS*=p; cur.assign(nS,INF); cur[0]=0; }
    auto dropTo=[&](int v){                                 // drop lowest digits (they must equal R's digits)
        while(curV>v){
            int want=a.Rdig[a.E-curV]; int nS=cur.size()/p; std::vector<i64> t(nS,INF);
            for(int s=0;s<(int)cur.size();++s){ if(cur[s]>=INF || s%p!=want) continue; if(cur[s]<t[s/p]) t[s/p]=cur[s]; }
            cur.swap(t); --curV;
        }
    };
    for(int k=0;k<M;++k){
        int v=a.lev[levOf[k]].v;
        dropTo(v);
        if(probe) before[k]=cur;
        int id=order[k]; int x=a.xs[id]; i64 w=lam[id]; int c=a.w[id]; int fx=fix[x];
        int S=cur.size(); take[k].assign(S,0);
        if(fx==-1) continue;
        std::vector<i64> nb(S,INF);
        if(fx==0) nb=cur;
        for(int s=0;s<S;++s){ if(cur[s]>=INF) continue; int t=s+c; if(t>=S) t-=S; i64 val=cur[s]+w; if(val<nb[t]){ nb[t]=val; take[k][t]=1; } }
        cur.swap(nb);
    }
    int lastV=curV;
    std::vector<i64> lastCur=cur;
    dropTo(0);
    i64 best=cur[0];
    used.assign(a.xs.size(),0);
    if(probe) probe->assign(a.xs.size(),{INF,INF});
    if(best>=INF) return INF;
    int sEnd=0; { int mul=1; for(int d=a.E-lastV; d<a.E; ++d){ sEnd+=a.Rdig[d]*mul; mul*=p; } }
    { // backtrack
        int s=sEnd, V=lastV;
        for(int k=M-1;k>=0;--k){
            int v=a.lev[levOf[k]].v;
            while(V<v){ s=s*p+a.Rdig[a.E-V-1]; ++V; }
            int id=order[k]; int S=take[k].size();
            if(fix[a.xs[id]]!=-1 && take[k][s]){ used[id]=1; s-=a.w[id]; if(s<0) s+=S; }
        }
    }
    if(probe){
        std::vector<i64> g(lastCur.size(),INF); g[sEnd]=0;
        int V=lastV;
        for(int k=M-1;k>=0;--k){
            int v=a.lev[levOf[k]].v;
            while(V<v){
                int nS=g.size()*p; std::vector<i64> h(nS,INF); int d=a.Rdig[a.E-V-1];
                for(int s=0;s<(int)g.size();++s){ if(g[s]<INF) h[s*p+d]=g[s]; }
                g.swap(h); ++V;
            }
            int id=order[k]; int x=a.xs[id]; int c=a.w[id]; int S=g.size(); i64 w=lam[id]; int fx=fix[x];
            const std::vector<i64>& f=before[k];
            i64 bin=INF, bout=INF;
            for(int s=0;s<S;++s){ if(f[s]>=INF) continue; int t=s+c; if(t>=S) t-=S;
                if(fx!=-1 && g[t]<INF){ i64 val=f[s]+w+g[t]; if(val<bin) bin=val; }
                if(fx!=1 && g[s]<INF){ i64 val=f[s]+g[s]; if(val<bout) bout=val; } }
            (*probe)[id]={bin,bout};
            std::vector<i64> h(S,INF);
            for(int s=0;s<S;++s){ i64 bst=INF; if(fx!=1) bst=g[s]; int t=s+c; if(t>=S) t-=S; if(fx!=-1 && g[t]<INF && g[t]+w<bst) bst=g[t]+w; h[s]=bst; }
            g.swap(h);
        }
    }
    return best;
}

// ------------------------------------------------------------------ bound at a node
static void allDP(const std::vector<std::vector<i64>>& lam,const std::vector<signed char>& fix,std::vector<std::vector<char>>& used,std::vector<i64>& val,
                  std::vector<std::vector<std::pair<i64,i64>>>* probes){
    int np=P.size(); used.resize(np); val.assign(np,0);
    std::atomic<int> next(0);
    auto worker=[&](){ for(;;){ int i=next++; if(i>=np) break; val[i]=primeDP(i,lam[i],fix,used[i], probes? &(*probes)[i] : nullptr); } };
    if(THREADS<=1) worker(); else { std::vector<std::thread> th; for(int t=0;t<THREADS;++t) th.emplace_back(worker); for(auto& t: th) t.join(); }
}
static bool consistentUse(const std::vector<std::vector<char>>& used){
    for(int x=2;x<=K;++x){ auto& sl=slots[x]; if(sl.size()<2) continue; int su=0; for(auto s: sl) su+=used[s.first][s.second]; if(su!=0 && su!=(int)sl.size()) return false; }
    return true;
}
static i64 subgradient(std::vector<std::vector<i64>>& lam,const std::vector<signed char>& fix,int iters,std::vector<std::vector<char>>& usedOut,bool& cons,bool& infeasible){
    std::vector<std::vector<char>> used; std::vector<i64> val;
    i64 bestLB=-INF; std::vector<std::vector<i64>> bestLam=lam; cons=false; infeasible=false;
    int noImp=0;
    for(int it=0; it<iters; ++it){
        allDP(lam,fix,used,val,nullptr);
        i128 LB=0; for(size_t i=0;i<val.size();++i){ if(val[i]>=INF){ infeasible=true; return INF; } LB+=val[i]; }
        bool c=consistentUse(used);
        if((i64)LB>bestLB){ bestLB=(i64)LB; bestLam=lam; usedOut=used; cons=c; noImp=0; } else ++noImp;
        if(LB>Dhi || c) break;
        if(noImp>NOIMP) break;
        // subgradient within each x: k*used - sum(used); Polyak step towards a target above Delta
        i128 target=Dhi + Dhi/64 + 1, gg=0;
        std::vector<std::pair<std::pair<int,int>,int>> gs;
        for(int x=2;x<=K;++x){
            auto& sl=slots[x]; int k=sl.size(); if(k<2 || fix[x]) continue;
            int su=0; for(auto s: sl) su+=used[s.first][s.second];
            if(su==0||su==k) continue;
            for(auto s: sl){ int v=k*used[s.first][s.second]-su; if(v){ gs.push_back({s,v}); gg+=(i128)v*v; } }
        }
        if(gg==0) break;
        i64 step=(i64)((target-LB)/gg); if(step<1) step=1;
        for(auto& g: gs) lam[g.first.first][g.first.second]+= step*g.second;
    }
    lam=bestLam;
    return bestLB;
}

// ------------------------------------------------------------------ branch and bound
static bool COUNT=false;
static u64 nodes=0, solutions=0;
static std::vector<std::vector<int>> found;
static i64 rootLB=0;
static std::vector<signed char> fixv;
static bool budgetExceeded=false;
static std::string CERT;                                    // file for a root-closure certificate
static std::vector<std::vector<i64>> rootLam;

static std::vector<int> setFromE(const std::vector<char>& inE){ std::vector<int> S; for(int x=1;x<=K;++x) if(adm[x] && !inE[x]) S.push_back(x); return S; }

static void bb(std::vector<std::vector<i64>> lam,int depth){
    if(!COUNT && !found.empty()) return;
    if(MAXNODES && nodes>=MAXNODES){ budgetExceeded=true; return; }
    ++nodes;
    std::vector<std::vector<char>> used; bool cons, infeas;
    i64 LB=subgradient(lam,fixv,depth==0?ROOTIT:NODEIT,used,cons,infeas);
    if(depth==0){ rootLB=LB; rootLam=lam; }
    if(nodes%50==0 || depth<2) fprintf(stderr,"  node %llu depth %d LB-Dhi=%lld%s\n",nodes,depth,(long long)((i128)LB-Dhi),cons?" consistent":"");
    if(infeas || (i128)LB>Dhi) return;
    // reduced-cost fixing with forward/backward tables
    std::vector<std::vector<std::pair<i64,i64>>> probes(P.size());
    std::vector<i64> val; std::vector<std::vector<char>> u2;
    allDP(lam,fixv,u2,val,&probes);
    i128 L2=0; for(auto v: val){ if(v>=INF) return; L2+=v; }
    std::vector<int> changed;
    int bestX=-1; i128 bestScore=-1; bool bestInFirst=true;
    for(int x=2;x<=K;++x){
        if(!adm[x] || fixv[x]) continue;
        auto& sl=slots[x]; if(sl.empty()) continue;
        i128 lin=L2, lout=L2; bool infIn=false, infOut=false;
        for(auto s: sl){ auto pr=probes[s.first][s.second]; i64 opt=val[s.first];
            if(pr.first>=INF) infIn=true; else lin+=pr.first-opt;
            if(pr.second>=INF) infOut=true; else lout+=pr.second-opt; }
        bool cutIn = infIn || lin>Dhi, cutOut = infOut || lout>Dhi;
        if(cutIn && cutOut){ for(int y: changed) fixv[y]=0; return; }       // node infeasible
        if(cutIn){ fixv[x]=-1; changed.push_back(x); continue; }           // x cannot be in E
        if(cutOut){ fixv[x]=1; changed.push_back(x); continue; }           // x must be in E
        int su=0; for(auto s: sl) su+=used[s.first][s.second];
        if(sl.size()>=2 && su!=0 && su!=(int)sl.size()){
            // proving: maximise the weaker child's bound; diving (witness search): pick the most
            // one-sided element and follow its cheaper side
            i128 sc = DIVE ? (lin>lout? lin-lout : lout-lin) : (lin<lout? lin:lout);
            if(sc>bestScore){ bestScore=sc; bestX=x; bestInFirst=(lin<=lout); }
        }
    }
    if(!changed.empty()){ bb(lam,depth+1); for(int y: changed) fixv[y]=0; return; }   // re-solve with the fixings
    if(cons){
        std::vector<char> inE(K+1,0); i128 lossLo=0; int ne=0;
        for(int x=2;x<=K;++x){ auto& sl=slots[x]; if(sl.empty()) continue; if(used[sl[0].first][sl[0].second]){ inE[x]=1; lossLo+=ONE/x; ++ne; } }
        // true loss*2^F <= lossLo + ne ; Delta*2^F >= Dhi - |U| ; we need loss < Delta + 1
        if(lossLo + ne + K + 1 < Dhi + ONE){
            std::vector<int> S=setFromE(inE); std::string why;
            if(exactCheck(NT,S,why)){ ++solutions; found.push_back(S); if(!COUNT) return; }
            else fprintf(stderr,"internal: consistent set failed exact check (%s)\n",why.c_str());
        }
        if(!COUNT) return;
        // counting: other solutions may exist in this subtree; branch on any free element
        if(bestX<0){ for(int x=2;x<=K;++x) if(adm[x] && !fixv[x] && !slots[x].empty()){ bestX=x; break; } }
        if(bestX<0) return;                                               // everything fixed
    }
    if(bestX<0){ for(int x=2;x<=K && bestX<0;++x){ auto& sl=slots[x]; if(sl.size()<2||fixv[x]) continue; int su=0; for(auto s: sl) su+=used[s.first][s.second]; if(su!=0&&su!=(int)sl.size()) bestX=x; } }
    if(bestX<0){ fprintf(stderr,"internal: nothing to branch on\n"); return; }
    // proving: explore "x in E" first; diving: the side with the smaller bound first
    int first = (DIVE && !bestInFirst) ? -1 : 1;
    for(int side: {first,-first}){ fixv[bestX]=side; bb(lam,depth+1); fixv[bestX]=0; if(!COUNT && !found.empty()) return; if(budgetExceeded) return; }
}

int main(int argc,char** argv){
    if(argc<4){ fprintf(stderr,"usage: %s prove|witness|count|check n K [set] [threads=T rootiters=I nodeiters=J maxnodes=N]\n",argv[0]); return 1; }
    std::string mode=argv[1]; NT=atoi(argv[2]); K=atoi(argv[3]);
    std::string setArg;
    for(int i=4;i<argc;++i){ std::string a=argv[i];
        if(a.rfind("threads=",0)==0) THREADS=atoi(a.c_str()+8);
        else if(a.rfind("rootiters=",0)==0) ROOTIT=atoi(a.c_str()+10);
        else if(a.rfind("nodeiters=",0)==0) NODEIT=atoi(a.c_str()+10);
        else if(a.rfind("maxnodes=",0)==0) MAXNODES=strtoull(a.c_str()+9,0,10);
        else if(a.rfind("cert=",0)==0) CERT=a.substr(5);
        else if(a.rfind("noimp=",0)==0) NOIMP=atoi(a.c_str()+6);
        else if(a.rfind("dive=",0)==0) DIVE=atoi(a.c_str()+5);
        else setArg=a; }
    auto t0=std::chrono::steady_clock::now();
    std::vector<char> isp(K+1,1); isp[0]=0; if(K>=1) isp[1]=0;
    for(int i=2;(i64)i*i<=K;++i) if(isp[i]) for(int j=i*i;j<=K;j+=i) isp[j]=0;
    ppow.assign(K+1,0); pexp.assign(K+1,0);
    for(int p=2;p<=K;++p) if(isp[p]){ primes.push_back(p); int q=1,e=0; while((i64)q*p<=K){ q*=p; ++e; } ppow[p]=q; pexp[p]=e; }
    if(mode=="check"){
        std::vector<int> S; size_t pos=0; while(pos<setArg.size()){ size_t c=setArg.find(',',pos); if(c==std::string::npos) c=setArg.size(); S.push_back(atoi(setArg.substr(pos,c-pos).c_str())); pos=c+1; }
        int mx=0; for(int x: S) mx=std::max(mx,x);
        std::string why; bool ok=exactCheck(NT,S,why);
        printf("check n=%d K=%d |S|=%zu max=%d: %s (%s)\n",NT,K,S.size(),mx, ok&&mx==K?"VALID witness":"INVALID", why.c_str());
        return 0;
    }
    adm=candidateSet(K);
    bool needK=(mode=="witness"||mode=="count"); COUNT=(mode=="count");
    int nU=0; for(int x=1;x<=K;++x) nU+=adm[x];
    if(needK && !adm[K]){ printf("n=%d K=%d mode=%s NONE: %d is not a candidate (cannot occur in any set with integral sum)\n",NT,K,mode.c_str(),K); return 0; }
    i128 SU=0; for(int x=1;x<=K;++x) if(adm[x]) SU+=(ONE+x-1)/x;
    Dhi=SU-(i128)NT*ONE;
    if(Dhi<0){ printf("n=%d K=%d mode=%s NONE: sum of all candidates is below n\n",NT,K,mode.c_str()); return 0; }
    for(int p: primes){
        PP a; a.p=p; a.q=ppow[p]; a.E=pexp[p]; int R=0;
        for(int d=p;d<=K;d+=p) if(adm[d]){ a.xs.push_back(d); int c=coefp(d,p); R=(R+c)%a.q; }
        if(a.xs.empty()) continue;
        a.R=R; a.Rdig.assign(a.E,0); { int r=R; for(int d=0;d<a.E;++d){ a.Rdig[d]=r%p; r/=p; } }
        a.w.assign(a.xs.size(),0);
        for(int v=a.E; v>=1; --v){
            Level L; L.v=v; int pe=1; for(int t=0;t<a.E-v;++t) pe*=p;
            for(int i=0;i<(int)a.xs.size();++i) if(vpow(a.xs[i],p)==v){ L.idx.push_back(i); a.w[i]=coefp(a.xs[i],p)/pe; }
            if(!L.idx.empty()) a.lev.push_back(L);
        }
        P.push_back(a);
    }
    slots.assign(K+1,{}); for(int i=0;i<(int)P.size();++i) for(int j=0;j<(int)P[i].xs.size();++j) slots[P[i].xs[j]].push_back({i,j});
    std::vector<std::vector<i64>> lam(P.size()); for(int i=0;i<(int)P.size();++i) lam[i].assign(P[i].xs.size(),0);
    for(int x=2;x<=K;++x) if(adm[x]){ i64 b=ONE/x; int k=slots[x].size(); for(int t=0;t<k;++t){ auto s=slots[x][t]; lam[s.first][s.second]=b/k+(t==0?b%k:0); } }
    fixv.assign(K+1,0); if(needK) fixv[K]=-1;                // K must stay in S
    fprintf(stderr,"n=%d K=%d mode=%s |U|=%d primes with multiples=%zu threads=%d\n",NT,K,mode.c_str(),nU,P.size(),THREADS);
    bb(lam,0);
    auto t1=std::chrono::steady_clock::now(); long long ms=std::chrono::duration_cast<std::chrono::milliseconds>(t1-t0).count();
    if(COUNT){
        printf("n=%d K=%d mode=count solutions=%llu%s nodes=%llu time_ms=%lld\n",NT,K,solutions,budgetExceeded?" (node budget exceeded: lower bound)":"",nodes,ms);
    } else if(!found.empty()){
        auto& S=found[0]; printf("n=%d K=%d mode=%s FOUND |S|=%zu nodes=%llu time_ms=%lld S=",NT,K,mode.c_str(),S.size(),nodes,ms);
        for(size_t i=0;i<S.size();++i){ printf(i?",%d":"%d",S[i]); }
        printf("\n");
    } else if(budgetExceeded){
        printf("n=%d K=%d mode=%s UNDECIDED (node budget exceeded) nodes=%llu root_LB-Delta_hi=%lld time_ms=%lld\n",NT,K,mode.c_str(),nodes,(long long)((i128)rootLB-Dhi),ms);
    } else {
        if(!CERT.empty() && nodes==1){
            // certificate: the weights of the closing root bound; checked independently by verify_cert.py
            FILE* f=fopen(CERT.c_str(),"w");
            fprintf(f,"# A101877 lower-bound certificate: n K F  then lines  p x lambda  (sum over p of lambda <= floor(2^F/x))\n%d %d %d\n",NT,K,FR);
            for(size_t i=0;i<P.size();++i) for(size_t j=0;j<P[i].xs.size();++j) fprintf(f,"%d %d %lld\n",P[i].p,P[i].xs[j],(long long)rootLam[i][j]);
            fclose(f);
        }
        printf("n=%d K=%d mode=%s NONE (all branch-and-bound nodes closed) nodes=%llu root_LB-Delta_hi=%lld time_ms=%lld\n",NT,K,mode.c_str(),nodes,(long long)((i128)rootLB-Dhi),ms);
    }
    return 0;
}
