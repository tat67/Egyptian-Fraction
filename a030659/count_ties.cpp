// Exact enumeration of all optimal expansions for one k.
//
// Counts every set S of k distinct positive integers with max(S) = M and
// sum_{d in S} 1/d = 1, and reports the lexicographically smallest S (in
// increasing order).  Written independently of the CP-SAT code.
//
// Exactness.  Let L be the product of p^E over the small primes p (p*p <= M),
// p^E the largest power of p that is <= M.  Every block option below (its sum
// has v_p >= 0 for its large prime p, and its other factors are small) and every
// other candidate has a reciprocal sum that is an integer multiple of 1/L, so
// the remaining sum is tracked exactly as an integer Rint = L*R (L < 2^96 for
// M <= 1000).  A set is accepted iff Rint reaches exactly 0.  Floating point is
// used only for pruning, with a margin EPS = 1e-12 far above the accumulated
// rounding error (< 1e-15), so no solution is ever lost.
//
// Residues.  For every small prime q, sum_{d in S, q|d} q^(E-v_q(d)) *
// (d/q^v_q(d))^(-1) mod q^E is tracked; it must be 0 once every multiple of q
// has been decided (this is v_q(sum) >= 0).  Used for pruning only.
//
// Candidates.  d is dropped if, for some prime p | d, no set of multiples of p
// in [1, M] containing d has residue 0 mod p^E (necessary condition; computed
// by a subset-sum over residues).
//
// Search.  For each large prime p (p*p > M) all multiples of p form one block;
// the admissible choices for a block are exactly the subsets J of multiples
// with residue 0 mod p ("options"), enumerated up front.  Stages are the large
// blocks (largest p first), then every remaining candidate on its own, grouped
// by largest prime factor q (largest q first, increasing inside a group).
// Pruning (all necessary conditions):
//  * for each stage s and count c, the least and greatest reciprocal sum of c
//    further elements (group knapsack over the remaining stages) must bracket R;
//    options that fail this against all other stages are discarded up front;
//  * inside the group of q: some number t of further group elements must reach
//    residue 0 for q with a sum that the stages after the group can complement
//    (per-group table of least / greatest sum by residue and count);
//  * at the start of each group: for every smaller prime, the remaining
//    candidates must be able to clear its residue with exactly c elements and
//    sum R (per-prime table of least / greatest sum by residue and count).
//
// Memo.  The number of completions from stage s depends only on (s, c, Rint)
// (the residues are determined by Rint), so it is memoised at block stages, at
// the start of each group and at every 4th stage.  A second pass walks only
// through states with a non-zero count to find the lexicographically smallest
// solution (skipped if there are more than 2e7 solutions).
//
// Time limit.  With a time limit, a run that does not finish prints
// "count>=N": N counts every solution already accounted for (at its leaf or at
// the first memo hit on its path, so each exactly once) - a proven lower bound.
//
// Usage: count_ties k M [log2_memo_slots [time_limit_s]]
//        (default 2^27 slots of 24 bytes, about 3.2 GB at most)
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
#include <bitset>
#include <csignal>
#include <unistd.h>
typedef long double LD;
typedef unsigned __int128 u128;
typedef unsigned long long u64;
static int M, K;
static const LD EPS = 1e-12L, INF = 1e30L;

static std::vector<int> primes;
static int pw[4000];
static long long modinv(long long a, long long m){
    long long r0=m, r1=((a%m)+m)%m, s0=0, s1=1;
    while(r1){ long long q=r0/r1, t=r0-q*r1; r0=r1; r1=t; t=s0-q*s1; s0=s1; s1=t; }
    if(r0!=1) return -1;
    s0%=m; if(s0<0) s0+=m; return s0;
}
static int coef(int d, int p){
    int q=pw[p], v=0, r=d; while(r%p==0){ r/=p; ++v; }
    long long pe=1; for(int i=0;i<v;++i) pe*=p;
    return (int)((q/pe)%q * modinv(r,q) % q);
}
typedef std::bitset<1024> BS;
static BS rot(const BS& b, int s, int q){
    if(s==0) return b;
    BS r=(b<<s)|(b>>(q-s)); BS mask; for(int i=0;i<q;++i) mask[i]=1; return r&mask;
}

// small primes (p*p <= M): residues tracked during search
static std::vector<int> sp;                 // small primes
static std::vector<int> spmod;              // p^E
static int spidx[4000];

struct Opt { int cnt; LD cost; u128 N; std::vector<int> elems; std::vector<std::pair<int,int>> rs; };
struct Stage {
    bool block;                              // large-prime block or single element
    int d;                                   // single element
    u128 N;                                  // single: L/d
    std::vector<std::vector<Opt>> byCnt;     // block: options grouped by count, sorted by cost
    std::vector<std::pair<int,int>> rs;      // single: residue terms (small prime idx, coef)
    std::vector<int> checkAfter;             // small prime idxs to test after this stage
    int q=-1;                                // single: small prime idx of its block (largest prime factor)
    BS reach;                                // single: residues mod q^E reachable by this and later block elements
    int blockEnd=-1, tcap=0;                 // single: first stage after its group; max count in the group suffix
    std::vector<double> bmin, bmax;          // single: [r*(tcap+1)+t] least / greatest sum of t elements
                                             // from this stage to the group end with residue r (mod q^E)
};
static std::vector<Stage> st;
static std::vector<std::vector<LD>> mn, mx;  // mn[s][c], mx[s][c] for stages >= s
static std::vector<int> res;
static std::vector<int> chosen, best;
static long long nsol=0, nodes=0;
static int NS;

static u128 Lsm;                             // product of p^E over small primes
static const LD LDL_INV_DUMMY=0;
static int sM=-1;                               // stage of the block holding M (if any)
static LD invM=0;
static LD toR(u128 x){ return (LD)x/(LD)Lsm; }
static void record(){
    std::vector<int> a=chosen; std::sort(a.begin(),a.end());
    if(best.empty() || a<best) best=a;
}
static inline bool checks(const std::vector<int>& ca){
    for(int t: ca) if(res[t]) return false; return true;
}
// ---- memo: open addressing.  Rint < L < 2^100 for M <= 1000, so (s+1, c) are packed
// into the top bits of a 128-bit key (never 0 for a used slot); 24 bytes per entry ----
struct Ent { u64 lo, hi, v; };
static std::vector<Ent> tab; static u64 tabmask, tabused=0, tabcap;
static inline void mkkey(int s,int c,u128 r,u64& lo,u64& hi){
    u128 key = r | ((u128)(((u64)(s+1)<<12)|(u64)c) << 100);
    lo=(u64)key; hi=(u64)(key>>64);
}
static inline u64 hsh(u64 lo, u64 hi){
    u64 h=lo*0x9E3779B97F4A7C15ULL ^ (hi+0x632BE59BD9B4E019ULL)*0xC2B2AE3D27D4EB4FULL;
    h^=h>>29; h*=0xBF58476D1CE4E5B9ULL; h^=h>>32; return h;
}
static bool mget(int s,int c,u128 r,u64& v){
    u64 lo,hi; mkkey(s,c,r,lo,hi); u64 i=hsh(lo,hi)&tabmask;
    while(tab[i].hi|tab[i].lo){ if(tab[i].lo==lo && tab[i].hi==hi){ v=tab[i].v; return true; } i=(i+1)&tabmask; }
    return false;
}
static u64 MAXSLOTS=1ULL<<27;              // memo size cap (argv[3] = log2 of slots)
static void grow(){
    std::vector<Ent> old; old.swap(tab);
    u64 ns=(tabmask+1)*2; tab.assign(ns,Ent{0,0,0}); tabmask=ns-1; tabcap=(u64)(0.7*ns); tabused=0;
    for(auto& e: old) if(e.hi|e.lo){ u64 i=hsh(e.lo,e.hi)&tabmask; while(tab[i].hi|tab[i].lo) i=(i+1)&tabmask; tab[i]=e; ++tabused; }
}
static void mput(int s,int c,u128 r,u64 v){
    if(tabused>=tabcap){ if(tabmask+1<MAXSLOTS) grow(); else return; }   // at the cap: stop memoising
    u64 lo,hi; mkkey(s,c,r,lo,hi); u64 i=hsh(lo,hi)&tabmask;
    while(tab[i].hi|tab[i].lo){ if(tab[i].lo==lo && tab[i].hi==hi){ tab[i].v=v; return; } i=(i+1)&tabmask; }
    tab[i]={lo,hi,v}; ++tabused;
}
static bool ENUM=false;
static std::vector<char> firstInGroup;
// Running number of solutions already accounted for (each exactly once: a solution
// is counted at its leaf or at the first memo hit on its path).  If the time limit
// (argv[4] seconds) expires, this is printed as a lower bound.
static u64 found=0;
static int KK, MM;
// Future tables at group starts: for stage s (first of a group) and small prime index t,
// fmin/fmax[s][t][r*(K+1)+c] = least / greatest sum of c elements from stages >= s whose
// residues for prime t add up to r (mod p^E).  Empty vector = no table.
static std::vector<std::vector<std::vector<double>>> fmin, fmax;                          // second pass: enumerate solutions
static u64 dfs(int s, u128 Rn, int c){
    ++nodes;
    if(c==0){
        if(Rn!=0) return 0;
        for(size_t t=0;t<res.size();++t) if(res[t]){ fprintf(stderr,"residue mismatch\n"); exit(2); }
        if(ENUM){ ++nsol; record(); } else ++found;
        return 1;
    }
    if(s==NS) return 0;
    LD R=toR(Rn) - (s<=sM ? invM : 0.0L);         // value still to be covered by the stages >= s
    if(R < mn[s][c]-EPS || R > mx[s][c]+EPS) return 0;
    Stage& S=st[s];
    if(!S.block){
        int q=S.q, m=spmod[q]; int rr=(m-res[q])%m;
        if(!S.reach[rr]) return 0;
        // joint test: t more elements of this group with the right residue, the rest after the group
        bool ok=false; int e=S.blockEnd; const double* lo=&S.bmin[(size_t)rr*(S.tcap+1)]; const double* hi=&S.bmax[(size_t)rr*(S.tcap+1)];
        for(int t=0;t<=S.tcap && t<=c && !ok;++t){
            if(lo[t]>1e29) continue;
            LD a=R-(LD)hi[t], b=R-(LD)lo[t];
            if(b >= mn[e][c-t]-EPS && a <= mx[e][c-t]+EPS) ok=true;
        }
        if(!ok) return 0;
    }
    if(!S.block && firstInGroup[s]){
        for(size_t t=0;t<fmin[s].size();++t){
            if(fmin[s][t].empty()) continue;
            int m=spmod[t]; int rr=(m-res[t])%m;
            double lo=fmin[s][t][(size_t)rr*(K+1)+c], hi=fmax[s][t][(size_t)rr*(K+1)+c];
            if(lo>1e29 || R<(LD)lo-EPS || R>(LD)hi+EPS) return 0;
        }
    }
    u64 mv;
    // memo at block stages, at the first stage of each group, and at every 4th stage
    bool memoHere = S.block || firstInGroup[s] || (s%4)==0;
    if(memoHere && mget(s,c,Rn,mv)){ if(!ENUM){ found+=mv; return mv; } if(mv==0) return 0; }
    u64 tot=0;
    if(!S.block){
        if(S.N<=Rn){
            for(auto& t: S.rs) res[t.first]=(res[t.first]+t.second)%spmod[t.first];
            if(checks(S.checkAfter)){ chosen.push_back(S.d); tot+=dfs(s+1,Rn-S.N,c-1); chosen.pop_back(); }
            for(auto& t: S.rs) res[t.first]=(res[t.first]-t.second+spmod[t.first])%spmod[t.first];
        }
        if(checks(S.checkAfter)) tot+=dfs(s+1,Rn,c);
    } else {
        for(int t=0;t<(int)S.byCnt.size() && t<=c;++t){
            auto& v=S.byCnt[t]; if(v.empty()) continue;
            LD lo=R-mx[s+1][c-t]-EPS, hi=R-mn[s+1][c-t]+EPS;
            auto it=std::lower_bound(v.begin(),v.end(),lo,[](const Opt& o, LD x){ return o.cost<x; });
            for(; it!=v.end() && it->cost<=hi; ++it){
                if(it->N>Rn) continue;
                for(auto& r: it->rs) res[r.first]=(res[r.first]+r.second)%spmod[r.first];
                if(checks(S.checkAfter)){
                    for(int e: it->elems) chosen.push_back(e);
                    tot+=dfs(s+1,Rn-it->N,c-t);
                    chosen.resize(chosen.size()-it->elems.size());
                }
                for(auto& r: it->rs) res[r.first]=(res[r.first]-r.second+spmod[r.first])%spmod[r.first];
            }
        }
    }
    if(!ENUM && memoHere) mput(s,c,Rn,tot);
    return tot;
}

// group-knapsack combine: out[c] = min/max over t of opt[t] + nxt[c-t]
static void combine(const std::vector<LD>& omin, const std::vector<LD>& omax,
                    const std::vector<LD>& nmin, const std::vector<LD>& nmax,
                    std::vector<LD>& rmin, std::vector<LD>& rmax){
    rmin.assign(K+1,INF); rmax.assign(K+1,-INF);
    for(int t=0;t<(int)omin.size() && t<=K;++t){ if(omin[t]>=INF) continue;
        for(int c=t;c<=K;++c){
            if(nmin[c-t]<INF) rmin[c]=std::min(rmin[c],omin[t]+nmin[c-t]);
            if(nmax[c-t]>-INF) rmax[c]=std::max(rmax[c],omax[t]+nmax[c-t]);
        }}
}

int main(int argc, char** argv){
    K=atoi(argv[1]); M=atoi(argv[2]); if(argc>3) MAXSLOTS=1ULL<<atoi(argv[3]);
    KK=K; MM=M;
    if(argc>4){ signal(SIGALRM,[](int){ printf("%d %d count>=%llu PARTIAL (time limit)\n",KK,MM,found); fflush(stdout); _exit(0); }); alarm(atoi(argv[4])); }
    std::vector<char> isp(M+1,1); isp[0]=0; isp[1]=0;
    for(int i=2;i*i<=M;++i) if(isp[i]) for(int j=i*i;j<=M;j+=i) isp[j]=0;
    for(int p=2;p<=M;++p) if(isp[p]){ primes.push_back(p); int q=1; while(q*p<=M) q*=p; pw[p]=q; }
    // admissibility
    std::vector<char> adm(M+1,1); adm[0]=0; adm[1]=0;   // 1 cannot occur for k >= 2
    for(int p: primes){
        int q=pw[p]; std::vector<int> ks, cs;
        for(int d=p; d<=M; d+=p){ ks.push_back(d); cs.push_back(coef(d,p)); }
        int m=ks.size();
        std::vector<BS> pre(m+1), suf(m+1);
        pre[0][0]=1; for(int i=0;i<m;++i) pre[i+1]=pre[i]|rot(pre[i],cs[i],q);
        suf[m][0]=1; for(int i=m-1;i>=0;--i) suf[i]=suf[i+1]|rot(suf[i+1],cs[i],q);
        for(int i=0;i<m;++i){
            int need=(q-cs[i])%q; bool f=false;
            for(int r=0;r<q&&!f;++r) if(pre[i][r] && suf[i+1][((need-r)%q+q)%q]) f=true;
            if(!f) adm[ks[i]]=0;
        }
    }
    if(!adm[M]){ printf("%d %d count=0 nodes=0 lexmin=\n",K,M); return 0; }
    for(int p: primes) if((long long)p*p<=M){ spidx[p]=sp.size(); sp.push_back(p); spmod.push_back(pw[p]); }
    res.assign(sp.size(),0);
    Lsm=1; for(int q: spmod) Lsm*=(u128)q;
    invM=1.0L/M;
    auto smallTerms=[&](int d){ std::vector<std::pair<int,int>> r;
        for(int p: sp){ if(d%p==0){ int c=coef(d,p); if(c) r.push_back({spidx[p],c}); } } return r; };
    // forced element M
    for(auto& t: smallTerms(M)) res[t.first]=(res[t.first]+t.second)%spmod[t.first];
    LD R0=1.0L-1.0L/M; int K0=K-1;
    int lpfM; { int r=M, g=1; for(int p: sp) while(r%p==0){ r/=p; g=p; } lpfM = r>1 ? r : g; }
    bool Mlarge = (long long)lpfM*lpfM > M;
    u128 Rn0 = Mlarge ? Lsm : Lsm - Lsm/M;         // exact: 1/M is added with its block option
    // relaxation used to discard hopeless options at creation: sorted reciprocals
    std::vector<LD> allw; for(int d=2; d<M; ++d) if(adm[d]) allw.push_back(1.0L/d);
    std::sort(allw.begin(),allw.end());
    // large blocks
    std::vector<char> inBlock(M+1,0);
    for(int ti=(int)primes.size()-1; ti>=0; --ti){
        int p=primes[ti]; if((long long)p*p<=M) break;
        std::vector<int> items; bool hasM=false;
        for(int j=M/p;j>=1;--j){ int d=p*j; inBlock[d]=1; if(d==M){ hasM=true; continue; } if(adm[d]) items.push_back(d); }
        if(items.empty() && !hasM) continue;
        Stage S; S.block=true; S.d=0;
        int m=items.size();
        // sums of the c smallest / largest reciprocals among candidates outside this block
        std::vector<LD> ow; for(LD x: allw){ bool in=false; for(int d: items) if(1.0L/d==x) { in=true; break; } if(!in) ow.push_back(x); }
        std::vector<LD> omn(ow.size()+1,0), omx(ow.size()+1,0);
        for(size_t i=0;i<ow.size();++i){ omn[i+1]=omn[i]+ow[i]; omx[i+1]=omx[i]+ow[ow.size()-1-i]; }
        int base = hasM ? (int)(modinv(M/p,p)) : 0;
        // enumerate subsets with residue (base + sum inv(j)) == 0 mod p
        std::vector<int> iv(m); for(int i=0;i<m;++i) iv[i]=modinv(items[i]/p,p);
        long long lim=1LL<<m;
        for(long long mask=0; mask<lim; ++mask){
            int r=base; for(int i=0;i<m;++i) if(mask>>i&1){ r+=iv[i]; if(r>=p) r-=p; }
            if(r!=0) continue;
            Opt o; o.cnt=0; o.cost=0;
            for(int i=0;i<m;++i) if(mask>>i&1){ o.cnt++; o.cost+=1.0L/items[i]; }
            { int cr=K0-o.cnt; if(cr<0 || cr>(int)ow.size()) continue;
              LD rest=R0-o.cost; if(rest<omn[cr]-EPS || rest>omx[cr]+EPS) continue; }
            std::vector<int> smallacc(sp.size(),0);
            u128 sumJ = hasM ? Lsm/(M/p) : 0;
            for(int i=0;i<m;++i) if(mask>>i&1){
                o.elems.push_back(items[i]); sumJ += Lsm/(items[i]/p);
                for(auto& t: smallTerms(items[i])) smallacc[t.first]=(smallacc[t.first]+t.second)%spmod[t.first];
            }
            if(sumJ%p){ fprintf(stderr,"block value not divisible\n"); return 3; }
            o.N=sumJ/p;
            for(size_t t=0;t<sp.size();++t) if(smallacc[t]) o.rs.push_back({(int)t,smallacc[t]});
            if((int)S.byCnt.size()<=o.cnt) S.byCnt.resize(o.cnt+1);
            S.byCnt[o.cnt].push_back(o);
        }
        if(hasM && S.byCnt.empty()){ printf("%d %d count=0 nodes=0 lexmin=\n",K,M); return 0; }
        if(hasM) sM=st.size();
        st.push_back(S);
    }
    // single elements: grouped by largest prime factor q (small primes, largest q
    // first), increasing inside each group; M itself is already chosen
    auto lpf=[&](int d){ int r=d, g=1; for(int p: sp){ while(r%p==0){ r/=p; g=p; } } return r>1? r: g; };
    for(int qi=(int)sp.size()-1; qi>=0; --qi){
        int q=sp[qi]; int start=st.size();
        for(int d=2; d<=M-1; ++d) if(adm[d] && !inBlock[d] && lpf(d)==q){
            Stage S; S.block=false; S.d=d; S.N=Lsm/d; S.rs=smallTerms(d); S.q=qi; st.push_back(S); }
        // reachable residues mod q^E from each position to the end of the group
        int m=spmod[qi]; BS cur; cur[0]=1;
        for(int s2=(int)st.size()-1; s2>=start; --s2){
            int c=0; for(auto& t: st[s2].rs) if(t.first==qi) c=t.second;
            cur=cur|rot(cur,c,m); st[s2].reach=cur;
        }
    }
    NS=st.size();
    // per-stage option min/max cost by count
    auto stageMinMax=[&](const Stage& S, std::vector<LD>& omin, std::vector<LD>& omax){
        if(!S.block){ omin={0.0L,1.0L/S.d}; omax=omin; return; }
        omin.assign(S.byCnt.size(),INF); omax.assign(S.byCnt.size(),-INF);
        for(size_t t=0;t<S.byCnt.size();++t) for(auto& o: S.byCnt[t]){ omin[t]=std::min(omin[t],o.cost); omax[t]=std::max(omax[t],o.cost); }
    };
    // filter options: prefix (stages < s) and suffix (stages > s) knapsack bounds
    for(int pass=0; pass<2; ++pass){
        std::vector<std::vector<LD>> pmn(NS+1), pmx(NS+1), smn(NS+2), smx(NS+2);
        std::vector<LD> z(K+1,INF), zx(K+1,-INF); z[0]=0; zx[0]=0;
        pmn[0]=z; pmx[0]=zx;
        for(int s=0;s<NS;++s){ std::vector<LD> a,b; stageMinMax(st[s],a,b); combine(a,b,pmn[s],pmx[s],pmn[s+1],pmx[s+1]); }
        smn[NS]=z; smx[NS]=zx;
        for(int s=NS-1;s>=0;--s){ std::vector<LD> a,b; stageMinMax(st[s],a,b); combine(a,b,smn[s+1],smx[s+1],smn[s],smx[s]); }
        for(int s=0;s<NS;++s){
            if(!st[s].block) continue;
            // rest = prefix(s) + suffix(s+1)
            std::vector<LD> rmn,rmx; combine(pmn[s],pmx[s],smn[s+1],smx[s+1],rmn,rmx);
            for(size_t t=0;t<st[s].byCnt.size();++t){
                auto& v=st[s].byCnt[t]; std::vector<Opt> keep;
                for(auto& o: v){
                    int cr=K0-(int)t; if(cr<0) continue;
                    LD rest=R0-o.cost;
                    if(rmn[cr]<INF && rest>=rmn[cr]-EPS && rest<=rmx[cr]+EPS) keep.push_back(o);
                }
                std::sort(keep.begin(),keep.end(),[](const Opt& a,const Opt& b){ return a.cost<b.cost; });
                v.swap(keep);
            }
        }
        if(pass==1){ mn=smn; mx=smx; }
    }
    // per-group suffix tables (residue, count) -> least / greatest sum
    for(int a=0;a<NS;){
        if(st[a].block){ ++a; continue; }
        int q=st[a].q, b=a; while(b<NS && !st[b].block && st[b].q==q) ++b;
        int m=spmod[q];
        int cap=std::min(b-a,K);
        std::vector<double> cmin((size_t)m*(cap+1),1e30), cmax((size_t)m*(cap+1),-1e30);
        cmin[0]=0; cmax[0]=0;                         // empty suffix: residue 0, count 0
        for(int s2=b-1;s2>=a;--s2){
            int c2=0; for(auto& t: st[s2].rs) if(t.first==q) c2=t.second;
            double w=1.0/st[s2].d;
            std::vector<double> nmin=cmin, nmax=cmax;
            for(int r=0;r<m;++r) for(int t=0;t<cap;++t){
                double v1=cmin[(size_t)r*(cap+1)+t]; if(v1>1e29) continue;
                double v2=cmax[(size_t)r*(cap+1)+t];
                size_t j=(size_t)((r+c2)%m)*(cap+1)+t+1;
                if(v1+w<nmin[j]) nmin[j]=v1+w;
                if(v2+w>nmax[j]) nmax[j]=v2+w;
            }
            cmin.swap(nmin); cmax.swap(nmax);
            st[s2].bmin=cmin; st[s2].bmax=cmax; st[s2].tcap=cap; st[s2].blockEnd=b;
        }
        a=b;
    }
    // residue checks: after the last stage containing a multiple of each small prime
    std::vector<int> last(sp.size(),-1);
    for(int s=0;s<NS;++s){
        if(st[s].block){ for(auto& v: st[s].byCnt) for(auto& o: v) for(auto& r: o.rs) last[r.first]=std::max(last[r.first],s);
                         for(auto& v: st[s].byCnt) for(auto& o: v) for(int e: o.elems) for(int p: sp) if(e%p==0) last[spidx[p]]=std::max(last[spidx[p]],s); }
        else for(int p: sp) if(st[s].d%p==0) last[spidx[p]]=s;
    }
    std::vector<int> early;
    for(size_t t=0;t<sp.size();++t){ if(last[t]>=0) st[last[t]].checkAfter.push_back(t); else early.push_back(t); }
    for(int t: early) if(res[t]){ printf("%d %d count=0 nodes=0 lexmin=\n",K,M); return 0; }
    if(Mlarge && sM<0){ printf("%d %d count=0 nodes=0 lexmin=\n",K,M); return 0; }
    if(Lsm>>100){ fprintf(stderr,"L too large for packed memo keys\n"); return 5; }
    tab.assign(1ULL<<16, Ent{0,0,0}); tabmask=(1ULL<<16)-1; tabcap=(u64)(0.7*(1ULL<<16));
    firstInGroup.assign(NS,0);
    for(int s=0;s<NS;++s) if(!st[s].block && (s==0 || st[s-1].block || st[s-1].q!=st[s].q)) firstInGroup[s]=1;
    // future tables (backward knapsack over the single-element stages, one pass per small prime)
    fmin.assign(NS,{}); fmax.assign(NS,{});
    for(int s=0;s<NS;++s) if(firstInGroup[s]){ fmin[s].assign(sp.size(),{}); fmax[s].assign(sp.size(),{}); }
    for(size_t t=0;t<sp.size();++t){
        int m=spmod[t]; size_t W=K+1;
        std::vector<double> cmn((size_t)m*W,1e30), cmx((size_t)m*W,-1e30);
        cmn[0]=0; cmx[0]=0;
        bool any=false;                               // does a multiple of this prime lie ahead?
        for(int s=NS-1;s>=0 && !st[s].block;--s){
            int cx=0; for(auto& u: st[s].rs) if(u.first==(int)t) cx=u.second;
            if(st[s].d%sp[t]==0) any=true;
            double w=1.0/st[s].d;
            for(int c=K-1;c>=0;--c) for(int r=0;r<m;++r){
                double v=cmn[(size_t)r*W+c]; if(v>1e29) continue;
                size_t j=(size_t)((r+cx)%m)*W+c+1;
                if(v+w<cmn[j]) cmn[j]=v+w;
                double v2=cmx[(size_t)r*W+c]+w; if(v2>cmx[j]) cmx[j]=v2;
            }
            if(firstInGroup[s] && any && sp[t]<=sp[st[s].q]){ fmin[s][t]=cmn; fmax[s][t]=cmx; }
        }
    }
    chosen.push_back(M);
    u64 total=dfs(0, Rn0, K0);
    long long nodes1=nodes;
    const u64 ENUM_LIMIT=20000000ULL;
    if(total>0 && total<=ENUM_LIMIT){
        ENUM=true; nodes=0; dfs(0, Rn0, K0);
        if((u64)nsol!=total){ fprintf(stderr,"enumeration count %lld != %llu\n",nsol,total); return 4; }
    }
    printf("%d %d count=%llu nodes=%lld memo=%llu lexmin=", K, M, total, nodes1, tabused);
    if(total>ENUM_LIMIT) printf("SKIPPED");
    for(size_t i=0;i<best.size();++i) printf(i?",%d":"%d", best[i]);
    printf("\n");
}
