// a101877.cpp -- exact search for OEIS A101877.
//
// a(n) = least k such that some finite set S of distinct positive integers with
// max(S) = k has sum_{x in S} 1/x = n.
//
// No floating point is used anywhere: all arithmetic is on integers.
//
// Modes
//   a101877 witness n K   : is there S in [1..K] with K in S and sum 1/x = n?
//                           prints the first witness found (or "NONE", a proof).
//   a101877 count   n K   : number of such S (all witness sets with max = K).
//   a101877 none    n K   : is there any S in [1..K] with sum 1/x = n?  "NONE" is a
//                           proof that a(n) > K.
//   optional trailing arg: log2 of the memo table size cap (default 24 slots)
//
// Method
// 1. Exact reformulation.  For every prime p <= K let p^E be the largest power
//    of p that is <= K.  sum_{x in S} 1/x is an integer iff for every p
//        res_p(S) = sum_{x in S, p|x} p^(E-v_p(x)) * (x/p^v_p(x))^(-1)  == 0 (mod p^E).
// 2. Candidates.  x is dropped if for some prime p | x no set of multiples of p
//    in the candidate set containing x has res_p == 0 (subset-sum over residues);
//    repeated until stable.  Any solution uses candidates only.
// 3. Stages, by largest prime factor, largest first:
//    * a large prime p (p*p > K) whose multiples p*j are few: one stage whose
//      choices ("options") are the subsets with sum inv(j) == 0 (mod p);
//    * a large prime with many multiples, and every small prime q: a group of
//      single-element stages (smallest element first); the residue for the
//      group's prime must be 0 at the end of the group, and all multiples of that
//      prime lie in the group or in earlier stages.
//    * the element 1 last.
// 4. Exact bookkeeping.  Let L = product of q^E over the small primes q
//    (q*q <= K).  An option of a large block and every small-prime element has a
//    value that is an integer multiple of 1/L (for an option: (sum L/j)/p, exact
//    because the option's sum has v_p >= 0).  Inside an element-wise large group
//    the scale is 1/(pL) and it returns to 1/L at the group end (the residue 0
//    condition makes the division exact).  The remaining target R = n - (sum so
//    far) is kept as an exact multi-precision integer, and a set is accepted iff
//    R reaches exactly 0 with all residues 0.
// 5. Pruning (necessary conditions only):
//    * R must lie in [0, MX(s)], MX(s) = greatest value the remaining stages can
//      contribute;
//    * inside a group: some completion of the group with the required residue
//      and a value v must leave R - v in [0, MX(end of group)] (per-stage table of
//      the least and greatest value by residue).
//    Bounds use 2^-FR fixed point with directed rounding: the value of 1/x is
//    represented by the pair (floor, ceil); R is tracked by exact bignum and by a
//    fixed-point interval.  A branch is cut only if the interval proves it dead.
// 6. Memo.  The completion count of a state depends only on (stage, exact R), so
//    dead states (and, in count mode, counts) are memoised.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <algorithm>
#include <string>
#include <unordered_map>
typedef unsigned __int128 u128;
typedef __int128 i128;
typedef unsigned long long u64;
typedef long long i64;

// ---------------------------------------------------------------- bignum
static int NL = 4;                                  // number of 64-bit limbs in use
static const int MAXL = 24;                         // up to 1536 bits
struct Big { u64 a[MAXL]; };
static inline void bzero(Big& x){ memset(x.a,0,sizeof(u64)*NL); }
static inline bool bisz(const Big& x){ for(int i=0;i<NL;++i) if(x.a[i]) return false; return true; }
static inline int bcmp(const Big& x,const Big& y){ for(int i=NL-1;i>=0;--i){ if(x.a[i]!=y.a[i]) return x.a[i]<y.a[i]?-1:1; } return 0; }
static inline void badd(Big& x,const Big& y){ u128 c=0; for(int i=0;i<NL;++i){ c+=(u128)x.a[i]+y.a[i]; x.a[i]=(u64)c; c>>=64; } if(c){ fprintf(stderr,"bignum overflow\n"); exit(3);} }
static inline void bsub(Big& x,const Big& y){ u64 br=0; for(int i=0;i<NL;++i){ u128 t=(u128)x.a[i]-y.a[i]-br; x.a[i]=(u64)t; br=(t>>64)?1:0; } if(br){ fprintf(stderr,"bignum underflow\n"); exit(3);} }
static inline void bmul(Big& x,u64 m){ u128 c=0; for(int i=0;i<NL;++i){ c+=(u128)x.a[i]*m; x.a[i]=(u64)c; c>>=64; } if(c){ fprintf(stderr,"bignum overflow (mul)\n"); exit(3);} }
static inline u64 bdivmod(Big& x,u64 d){ u128 r=0; for(int i=NL-1;i>=0;--i){ r=(r<<64)|x.a[i]; x.a[i]=(u64)(r/d); r%=d; } return (u64)r; }
static inline u64 bmod(const Big& x,u64 d){ u128 r=0; for(int i=NL-1;i>=0;--i){ r=((r<<64)|x.a[i])%d; } return (u64)r; }
static inline int bbits(const Big& x){ for(int i=NL-1;i>=0;--i) if(x.a[i]) return 64*i+64-__builtin_clzll(x.a[i]); return 0; }
static inline u64 bhash(const Big& x){ u64 h=0x9E3779B97F4A7C15ULL; for(int i=0;i<NL;++i){ h^=x.a[i]+0x632BE59BD9B4E019ULL+(h<<6)+(h>>2); h*=0xBF58476D1CE4E5B9ULL; } return h^(h>>31); }

// ---------------------------------------------------------------- fixed point
// FR fractional bits; values (<= ~12) fit comfortably in i128.
static const int FR = 118;
static const i128 SAFE = 4096;                      // > accumulated rounding (ulps) in any option
static inline i128 fp_floor_recip(u64 x){ return (i128)(((u128)1<<FR)/x); }
static inline i128 fp_ceil_recip(u64 x){ return (i128)((((u128)1<<FR)+x-1)/x); }

// ---------------------------------------------------------------- number theory
static i64 modinv(i64 a,i64 m){ i64 r0=m,r1=((a%m)+m)%m,s0=0,s1=1; while(r1){ i64 q=r0/r1,t=r0-q*r1; r0=r1; r1=t; t=s0-q*s1; s0=s1; s1=t; } if(r0!=1) return -1; s0%=m; if(s0<0) s0+=m; return s0; }

static int K, NTARGET;
static std::vector<int> primes, ppow;                // ppow[p] = p^E
static std::vector<int> lpf;                         // largest prime factor
static int coefp(int x,int p){ int q=ppow[p],v=0,r=x; while(r%p==0){ r/=p; ++v; } i64 pe=1; for(int i=0;i<v;++i) pe*=p; return (int)(((q/pe)%q)*modinv(r,q)%q); }

// cyclic-shift bitsets over Z/m
struct BS { int m; std::vector<u64> w; BS(int m_=1):m(m_),w((m_+63)/64,0){} bool get(int i)const{ return w[i>>6]>>(i&63)&1; } void set(int i){ w[i>>6]|=1ULL<<(i&63); } };
static BS rot_or(const BS& b,int s){                 // b | (b shifted by s mod m)
    BS r=b; if(s==0) return r;
    for(int i=0;i<b.m;++i) if(b.get(i)){ int t=i+s; if(t>=b.m) t-=b.m; r.set(t); }
    return r;
}

// ---------------------------------------------------------------- stages
struct Opt { Big N; i128 lo, hi; std::vector<int> elems; std::vector<std::pair<int,int>> rs; };
struct Stage {
    int kind;                 // 0 = option block, 1 = single element, 2 = element "1"
    int prime;                // block prime / group prime
    int x;                    // single element
    Big N;                    // single: value in current units (1/L or 1/(pL))
    i128 lo, hi;              // fixed-point bounds of 1/x
    std::vector<std::pair<int,int>> rs;   // residue contributions (small prime index, coef)
    int gres=-1;              // single in element-wise large group: coef inv(j) mod p
    std::vector<Opt> opts;    // block options (sorted by value, descending)
    std::vector<int> bjs; bool bhasK=false; i128 bestlo=-1, besthi=-1;
    // group info (singles)
    int gid=-1, gstart=-1, gend=-1, gmod=0, gsp=-1;   // gsp: small prime index of group prime (-1 for large)
    bool largeGroup=false;
    std::vector<i128> tmin, tmax;         // per residue: least / greatest value of group suffix (fixed point)
    bool forced=false;        // element K when it must be included
};
static std::vector<Stage> st;
static int NS;
static std::vector<i128> MXhi;            // upper bound on value obtainable from stages >= s
static std::vector<std::vector<std::pair<std::vector<i128>,std::vector<i128>>>> fut;  // [stage][small prime] -> (min,max) by residue
static std::vector<int> sp, spmod; static std::vector<int> spidx;
static Big Lsm;
static std::vector<int> res;               // residues for small primes
static int lgres=0;                        // residue inside current element-wise large group
static bool COUNT=false;
static std::vector<int> chosen;
static std::vector<int> firstWitness;
static bool found=false;
static u64 nodes=0;
static std::vector<u64> nodesAt;
static u64 NODELIMIT=0;

// memo: (stage, R) -> count (u64); open addressing, flat storage with stride NL+2:
// [ (stage+1) , value , limbs of R ... ]; stage+1 == 0 marks an empty slot.  Grows to a cap.
static std::vector<u64> mtab; static u64 mslots=0, mused=0, mcapslots=0; static int MSTR=0;
static inline u64 mh(int s,const Big& R){ return bhash(R)^((u64)(s+1)*0x9E3779B97F4A7C15ULL); }
static void minit(u64 slots){ MSTR=NL+2; mslots=slots; mtab.assign(slots*MSTR,0); mused=0; }
static bool mget(int s,const Big& R,u64& v){
    u64 h=mh(s,R)&(mslots-1);
    while(mtab[h*MSTR]){ u64* e=&mtab[h*MSTR]; if(e[0]==(u64)(s+1) && memcmp(e+2,R.a,8*NL)==0){ v=e[1]; return true; } h=(h+1)&(mslots-1); }
    return false;
}
static void mins(int s,const Big& R,u64 v){
    u64 h=mh(s,R)&(mslots-1);
    while(mtab[h*MSTR]){ u64* e=&mtab[h*MSTR]; if(e[0]==(u64)(s+1) && memcmp(e+2,R.a,8*NL)==0){ e[1]=v; return; } h=(h+1)&(mslots-1); }
    u64* e=&mtab[h*MSTR]; e[0]=(u64)(s+1); e[1]=v; memcpy(e+2,R.a,8*NL); ++mused;
}
static void mput(int s,const Big& R,u64 v){
    if(mused*10>=mslots*7){
        if(mslots>=mcapslots) return;                  // at the cap: stop memoising
        std::vector<u64> old; old.swap(mtab); u64 os=mslots; minit(os*2);
        for(u64 i=0;i<os;++i){ u64* e=&old[i*MSTR]; if(e[0]){ Big b; bzero(b); memcpy(b.a,e+2,8*NL); mins((int)e[0]-1,b,e[1]); } }
    }
    mins(s,R,v);
}

// R: exact remaining target (units 1/L, or 1/(pL) inside an element-wise large group)
// Rlo/Rhi: fixed-point interval containing the true remaining target (as a real number)
static u64 dfs(int s, Big& R, i128 Rlo, i128 Rhi){
    ++nodes; if(s<(int)nodesAt.size()) ++nodesAt[s];
    if(NODELIMIT && nodes>NODELIMIT){ fprintf(stderr,"node limit\n"); return 0; }
    if(Rhi<0) return 0;
    if(s==NS){
        if(!bisz(R)) return 0;
        for(size_t t=0;t<res.size();++t) if(res[t]){ fprintf(stderr,"internal: residue mismatch at exact solution\n"); exit(4); }
        if(!found){ found=true; firstWitness=chosen; }
        return 1;
    }
    if(Rlo>MXhi[s]) return 0;
    Stage& S=st[s];
    // group feasibility table
    if(S.kind==1){
        int m=S.gmod; int cur = S.largeGroup ? lgres : res[S.gsp];
        int need=(m-cur)%m;
        i128 tmx=S.tmax[need], tmn=S.tmin[need];
        if(tmx<0) return 0;                                  // residue not reachable
        // need v in [tmn,tmx] with Rtrue - v in [0, MXhi[gend]]
        if(Rlo - tmx > MXhi[S.gend]) return 0;
        if(Rhi - tmn < 0) return 0;
    }
    if(S.kind==1 && !S.largeGroup && s==S.gstart && !fut[s].empty()){
        for(size_t t=0;t<fut[s].size();++t){
            auto& pr=fut[s][t]; if(pr.second.empty()) continue;
            int m=spmod[t]; int need=(m-res[t])%m;
            i128 hi=pr.second[need], lo=pr.first[need];
            if(hi<0 || Rlo>hi || Rhi<lo) return 0;
        }
    }
    bool memoHere = (S.kind==0) || (S.kind==1 && (s==S.gstart || (s&3)==0));
    u64 mv;
    if(memoHere && mget(s,R,mv)){ if(mv==0 || COUNT) return mv; }
    u64 tot=0;
    if(S.kind==2){                                        // element 1: include or not
        for(int inc=1;inc>=0;--inc){
            if(inc){ if(bcmp(S.N,R)>0) continue; bsub(R,S.N); chosen.push_back(1); tot+=dfs(s+1,R,Rlo-S.hi,Rhi-S.lo); chosen.pop_back(); badd(R,S.N); }
            else tot+=dfs(s+1,R,Rlo,Rhi);
            if(found && !COUNT) break;
        }
    } else if(S.kind==0){
        for(auto& o: S.opts){
            if(Rlo - o.hi > MXhi[s+1] + SAFE) break;          // sorted by exact value: later options are smaller
            if(Rlo - o.hi > MXhi[s+1]) continue;
            if(bcmp(o.N,R)>0) continue;
            for(auto& r: o.rs) res[r.first]=(res[r.first]+r.second)%spmod[r.first];
            bsub(R,o.N); for(int e: o.elems) chosen.push_back(e);
            tot+=dfs(s+1,R,Rlo-o.hi,Rhi-o.lo);
            chosen.resize(chosen.size()-o.elems.size()); badd(R,o.N);
            for(auto& r: o.rs) res[r.first]=(res[r.first]-r.second+spmod[r.first])%spmod[r.first];
            if(found && !COUNT) break;
        }
    } else {
        // entering an element-wise large group: switch units to 1/(pL)
        bool enter = S.largeGroup && s==S.gstart;
        bool leave = S.largeGroup && s+1==S.gend;
        if(enter){ bmul(R,S.prime); lgres=0; }
        for(int inc=1;inc>=0;--inc){
            if(S.forced && !inc) continue;
            if(inc){
                if(bcmp(S.N,R)>0) continue;
                bsub(R,S.N);
                for(auto& r: S.rs) res[r.first]=(res[r.first]+r.second)%spmod[r.first];
                int save=lgres; if(S.largeGroup) lgres=(lgres+S.gres)%S.gmod;
                bool ok=true;
                if(leave){ if(lgres!=0) ok=false; else { u64 rem=bdivmod(R,S.prime); if(rem){ fprintf(stderr,"internal: block not divisible\n"); exit(4);} } }
                if(!S.largeGroup && s+1==S.gend && res[S.gsp]!=0) ok=false;
                if(ok){ chosen.push_back(S.x); tot+=dfs(s+1,R,Rlo-S.hi,Rhi-S.lo); chosen.pop_back(); }
                if(leave && lgres==0) bmul(R,S.prime);
                lgres=save;
                for(auto& r: S.rs) res[r.first]=(res[r.first]-r.second+spmod[r.first])%spmod[r.first];
                badd(R,S.N);
            } else {
                bool ok=true;
                if(leave){ if(lgres!=0) ok=false; else { u64 rem=bdivmod(R,S.prime); if(rem){ fprintf(stderr,"internal: block not divisible\n"); exit(4);} } }
                if(!S.largeGroup && s+1==S.gend && res[S.gsp]!=0) ok=false;
                if(ok) tot+=dfs(s+1,R,Rlo,Rhi);
                if(leave && lgres==0) bmul(R,S.prime);
            }
            if(found && !COUNT) break;
        }
        if(enter){ u64 rem=bdivmod(R,S.prime); (void)rem; }
    }
    if(memoHere) mput(s,R,tot);
    return tot;
}

int main(int argc,char** argv){
    if(argc<4){ fprintf(stderr,"usage: %s witness|count|none n K [memo_log2]\n",argv[0]); return 1; }
    std::string mode=argv[1]; NTARGET=atoi(argv[2]); K=atoi(argv[3]);
    int mlog = argc>4 ? atoi(argv[4]) : 24;
    bool needK = (mode!="none"); COUNT = (mode=="count");
    // primes, largest prime factors
    std::vector<char> isp(K+1,1); isp[0]=0; if(K>=1) isp[1]=0;
    for(int i=2;(i64)i*i<=K;++i) if(isp[i]) for(int j=i*i;j<=K;j+=i) isp[j]=0;
    ppow.assign(K+1,0); lpf.assign(K+1,1);
    for(int p=2;p<=K;++p) if(isp[p]){ primes.push_back(p); int q=1; while((i64)q*p<=K) q*=p; ppow[p]=q; for(int j=p;j<=K;j+=p) lpf[j]=p; }
    // candidates: iterate the per-prime subset-sum test to a fixed point
    std::vector<char> adm(K+1,1); adm[0]=0;
    for(bool changed=true; changed; ){
        changed=false;
        for(int p: primes){
            int q=ppow[p]; std::vector<int> ks, cs;
            for(int d=p; d<=K; d+=p) if(adm[d]){ ks.push_back(d); cs.push_back(coefp(d,p)); }
            int m=ks.size(); if(!m) continue;
            std::vector<BS> pre(m+1,BS(q)), suf(m+1,BS(q));
            pre[0].set(0); for(int i=0;i<m;++i) pre[i+1]=rot_or(pre[i],cs[i]);
            suf[m].set(0); for(int i=m-1;i>=0;--i) suf[i]=rot_or(suf[i+1],cs[i]);
            for(int i=0;i<m;++i){
                int need=(q-cs[i])%q; bool f=false;
                for(int r=0;r<q && !f;++r) if(pre[i].get(r) && suf[i+1].get(((need-r)%q+q)%q)) f=true;
                if(!f){ adm[ks[i]]=0; changed=true; }
            }
        }
    }
    if(needK && !adm[K]){ printf("n=%d K=%d: K is not a candidate -> NONE\n",NTARGET,K); return 0; }
    // small primes and L
    int r0=1; while((i64)(r0+1)*(r0+1)<=K) ++r0;
    spidx.assign(K+1,-1);
    for(int p: primes) if(p<=r0){ spidx[p]=sp.size(); sp.push_back(p); spmod.push_back(ppow[p]); }
    // size bignum: bits(L) + bits(max prime) + margin
    int bitsL=0; for(int q: spmod){ int b=0; while((1LL<<b)<=q) ++b; bitsL+=b; }
    NL = (bitsL + 64 /*large prime scale*/ + 16 /*n and sums*/ + 63)/64 + 1;
    if(NL>MAXL){ fprintf(stderr,"L too large (%d bits)\n",bitsL); return 2; }
    bzero(Lsm); Lsm.a[0]=1; for(int q: spmod) bmul(Lsm,q);
    res.assign(sp.size(),0);
    auto smallTerms=[&](int x){ std::vector<std::pair<int,int>> r; for(size_t t=0;t<sp.size();++t){ int q=sp[t]; if(q>x) break; if(x%q==0){ int c=coefp(x,q); if(c) r.push_back({(int)t,c}); } } return r; };
    auto Lover=[&](int x){ Big b=Lsm; u64 rem=bdivmod(b,x); if(rem){ fprintf(stderr,"internal: L/x not exact (x=%d)\n",x); exit(4);} return b; };
    // ---- build stages
    const int OPTMAX=18;
    for(int ti=(int)primes.size()-1; ti>=0; --ti){
        int p=primes[ti]; if(p<=r0) break;
        std::vector<int> js; bool hasK=false;
        for(int j=1;(i64)j*p<=K;++j) if(adm[p*j]){ js.push_back(j); if(needK && p*j==K) hasK=true; }
        if(js.empty()) continue;
        int m=js.size();
        if(m<=OPTMAX){
            Stage S; S.kind=0; S.prime=p; S.x=0; S.bjs=js; S.bhasK=hasK;
            st.push_back(S);                          // options are filled in after the slack is known
        } else {
            int g0=st.size();
            for(int i=0;i<m;++i){
                Stage S; S.kind=1; S.prime=p; S.x=p*js[i]; S.largeGroup=true; S.gmod=p; S.gres=modinv(js[i],p);
                S.N=Lover(js[i]);                              // units 1/(pL)
                S.lo=fp_floor_recip(S.x); S.hi=fp_ceil_recip(S.x); S.rs=smallTerms(S.x);
                S.forced = needK && S.x==K;
                st.push_back(S);
            }
            for(int s=g0;s<(int)st.size();++s){ st[s].gstart=g0; st[s].gend=st.size(); }
        }
    }
    for(int t=(int)sp.size()-1;t>=0;--t){
        int q=sp[t]; int g0=st.size();
        for(int x=2;x<=K;++x) if(adm[x] && lpf[x]==q){
            Stage S; S.kind=1; S.prime=q; S.x=x; S.largeGroup=false; S.gmod=spmod[t]; S.gsp=t;
            S.N=Lover(x); S.lo=fp_floor_recip(x); S.hi=fp_ceil_recip(x); S.rs=smallTerms(x);
            S.forced = needK && x==K;
            st.push_back(S);
        }
        for(int s=g0;s<(int)st.size();++s){ st[s].gstart=g0; st[s].gend=st.size(); }
        if(g0==(int)st.size()){
            // no element with this largest prime factor: residue must already be 0 when we get here;
            // enforce with an empty check stage is unnecessary because residues of q come only from
            // earlier stages; checked at the final leaf (all residues 0) and by R == 0.
        }
    }
    if(adm[1]){ Stage S; S.kind=2; S.prime=1; S.x=1; S.N=Lsm; S.lo=fp_floor_recip(1); S.hi=fp_ceil_recip(1); st.push_back(S); }
    NS=st.size();
    // ---- option blocks: pass 1 best value per block, pass 2 keep options within the global slack
    auto enumBlock=[&](Stage& S, bool store, i128 thr){
        int p=S.prime; auto& js=S.bjs; int m=js.size();
        std::vector<int> iv(m); for(int i=0;i<m;++i) iv[i]=modinv(js[i],p);
        int kidx=-1; if(S.bhasK) for(int i=0;i<m;++i) if(p*js[i]==K) kidx=i;
        std::vector<i128> flo(m), fhi(m); for(int i=0;i<m;++i){ flo[i]=fp_floor_recip(p*js[i]); fhi[i]=fp_ceil_recip(p*js[i]); }
        for(u64 mask=0; mask<(1ULL<<m); ++mask){
            if(kidx>=0 && !(mask>>kidx&1)) continue;
            i64 r=0; i128 lo=0, hi=0;
            for(int i=0;i<m;++i) if(mask>>i&1){ r+=iv[i]; lo+=flo[i]; hi+=fhi[i]; }
            if(r%p) continue;
            if(!store){ if(hi>S.besthi) S.besthi=hi; if(lo>S.bestlo) S.bestlo=lo; continue; }
            if(hi<thr) continue;
            Opt o; Big sum; bzero(sum); o.lo=lo; o.hi=hi; std::vector<int> acc(sp.size(),0);
            for(int i=0;i<m;++i) if(mask>>i&1){
                int x=p*js[i]; o.elems.push_back(x); badd(sum,Lover(js[i]));
                for(auto& t: smallTerms(x)) acc[t.first]=(acc[t.first]+t.second)%spmod[t.first];
            }
            u64 rem=bdivmod(sum,p); if(rem){ fprintf(stderr,"internal: option not divisible\n"); exit(4); }
            o.N=sum;
            for(size_t t=0;t<sp.size();++t) if(acc[t]) o.rs.push_back({(int)t,acc[t]});
            S.opts.push_back(o);
        }
    };
    i128 tot_hi=0;
    for(auto& S: st){
        if(S.kind==0){ enumBlock(S,false,0); if(S.besthi<0){ printf("n=%d K=%d: block %d has no admissible choice -> NONE\n",NTARGET,K,S.prime); return 0; } tot_hi+=S.besthi; }
        else tot_hi+=S.hi;
    }
    i128 slack = tot_hi - (((i128)NTARGET)<<FR);   // >= true (max total - n)
    fprintf(stderr,"global slack (upper bound) = %lld / 2^%d\n",(long long)(slack>>(FR-40)),40);
    if(slack<0){ printf("n=%d K=%d mode=%s NONE (sum of block maxima and all other candidates < n) nodes=0\n",NTARGET,K,mode.c_str()); return 0; }
    for(auto& S: st) if(S.kind==0){
        enumBlock(S,true,S.bestlo - slack - SAFE);
        std::sort(S.opts.begin(),S.opts.end(),[](const Opt& a,const Opt& b){ return bcmp(a.N,b.N)>0; });
    }
    // ---- group tables and MX
    for(int a=0;a<NS;){
        if(st[a].kind!=1){ ++a; continue; }
        int b=st[a].gend, m=st[a].gmod;
        std::vector<i128> cmn(m,(i128)-1), cmx(m,(i128)-1);    // -1 = unreachable (values are >= 0)
        cmn[0]=0; cmx[0]=0;
        for(int s=b-1;s>=a;--s){
            int c = st[s].largeGroup ? st[s].gres : 0;
            if(!st[s].largeGroup) for(auto& u: st[s].rs) if(u.first==st[s].gsp) c=u.second;
            std::vector<i128> nmn=cmn, nmx=cmx;
            for(int r=0;r<m;++r){
                if(cmx[r]<0) continue;
                int t=(r+c)%m;
                i128 lo=cmn[r]+st[s].lo, hi=cmx[r]+st[s].hi;
                if(st[s].forced){ /* forced include: handled by leaving only the include branch */ }
                if(nmx[t]<0){ nmn[t]=lo; nmx[t]=hi; } else { if(lo<nmn[t]) nmn[t]=lo; if(hi>nmx[t]) nmx[t]=hi; }
            }
            if(st[s].forced){               // the element must be taken: only "include" transitions
                std::vector<i128> fmn(m,(i128)-1), fmx(m,(i128)-1);
                for(int r=0;r<m;++r){ if(cmx[r]<0) continue; int t=(r+c)%m; fmn[t]=cmn[r]+st[s].lo; fmx[t]=cmx[r]+st[s].hi; }
                nmn=fmn; nmx=fmx;
            }
            cmn.swap(nmn); cmx.swap(nmx);
            st[s].tmin=cmn; st[s].tmax=cmx;
        }
        a=b;
    }
    MXhi.assign(NS+1,0);
    for(int s2=NS-1;s2>=0;--s2){
        Stage& S=st[s2];
        if(S.kind==0) MXhi[s2]=MXhi[s2+1]+S.opts[0].hi;      // options sorted, [0] is the largest
        else if(S.kind==2) MXhi[s2]=MXhi[s2+1]+S.hi;
        else if(S.largeGroup && s2==S.gstart){ i128 b=S.tmax[0]; if(b<0){ printf("n=%d K=%d: group %d cannot reach residue 0 -> NONE\n",NTARGET,K,S.prime); return 0; } MXhi[s2]=MXhi[S.gend]+b; }
        else MXhi[s2]=MXhi[s2+1]+S.hi;
    }
    // large groups: inner stages use the plain element sums; the group start uses tmax[0]
    for(int s2=NS-1;s2>=0;--s2){ Stage& S=st[s2]; if(S.kind==1 && S.largeGroup && s2!=S.gstart){ i128 acc=MXhi[S.gend]; for(int u=S.gend-1;u>=s2;--u) acc+=st[u].hi; MXhi[s2]=acc; } }
    // (b) future tables at the start of each small-prime group: for every small prime t that still
    // has a multiple at or after this stage, least / greatest value of a subset of all remaining
    // single stages whose residue for t is r.
    fut.assign(NS,{});
    {
        std::vector<int> starts; for(int s2=0;s2<NS;++s2) if(st[s2].kind==1 && !st[s2].largeGroup && s2==st[s2].gstart) starts.push_back(s2);
        int firstSmall = starts.empty()? NS : starts[0];
        for(size_t t=0;t<sp.size();++t){
            int m=spmod[t];
            std::vector<i128> cmn(m,(i128)-1), cmx(m,(i128)-1); cmn[0]=0; cmx[0]=0;
            bool any=false;
            for(int s2=NS-1;s2>=firstSmall;--s2){
                Stage& S=st[s2];
                int c=0; for(auto& u: S.rs) if(u.first==(int)t) c=u.second;
                if(S.x%sp[t]==0) any=true;
                std::vector<i128> nmn=cmn, nmx=cmx;
                for(int r=0;r<m;++r){ if(cmx[r]<0) continue; int to=(r+c)%m; i128 lo=cmn[r]+S.lo, hi=cmx[r]+S.hi;
                    if(nmx[to]<0){ nmn[to]=lo; nmx[to]=hi; } else { if(lo<nmn[to]) nmn[to]=lo; if(hi>nmx[to]) nmx[to]=hi; } }
                if(S.forced){ std::vector<i128> fmn(m,(i128)-1), fmx(m,(i128)-1);
                    for(int r=0;r<m;++r){ if(cmx[r]<0) continue; int to=(r+c)%m; fmn[to]=cmn[r]+S.lo; fmx[to]=cmx[r]+S.hi; } nmn=fmn; nmx=fmx; }
                cmn.swap(nmn); cmx.swap(nmx);
                if(S.kind==1 && !S.largeGroup && s2==S.gstart && any){
                    if(fut[s2].empty()) fut[s2].resize(sp.size());
                    fut[s2][t].first=cmn; fut[s2][t].second=cmx;
                }
            }
        }
    }
    // ---- memo
    mcapslots=1ULL<<mlog; minit(1ULL<<12);
    // ---- initial state
    Big R=Lsm; bmul(R,(u64)NTARGET);
    i128 Rlo=((i128)NTARGET)<<FR, Rhi=Rlo;
    int nblocks=0,nopts=0,ngroups=0; for(auto& x: st){ if(x.kind==0){ ++nblocks; nopts+=x.opts.size(); } }
    for(int s=0;s<NS;++s) if(st[s].kind==1 && s==st[s].gstart) ++ngroups;
    int ncand=0; for(int x=1;x<=K;++x) ncand+=adm[x];
    fprintf(stderr,"n=%d K=%d mode=%s candidates=%d stages=%d option-blocks=%d (options %d) groups=%d L=%d bits limbs=%d\n",
            NTARGET,K,mode.c_str(),ncand,NS,nblocks,nopts,ngroups,bitsL,NL);
    nodesAt.assign(NS+1,0);
    if(getenv("NODELIMIT")) NODELIMIT=strtoull(getenv("NODELIMIT"),0,10);
    u64 total=dfs(0,R,Rlo,Rhi);
    if(getenv("PROFILE")){
        u64 blk=0; std::vector<std::pair<int,u64>> g;
        for(int s2=0;s2<NS;++s2){ if(st[s2].kind==0) blk+=nodesAt[s2]; else if(st[s2].kind==1){ if(s2==st[s2].gstart) g.push_back({st[s2].prime*(st[s2].largeGroup?-1:1),0}); g.back().second+=nodesAt[s2]; } }
        fprintf(stderr,"nodes in option blocks: %llu\n",blk);
        for(auto& x: g) if(x.second) fprintf(stderr,"  group %s%d: %llu\n",x.first<0?"large ":"",x.first<0?-x.first:x.first,x.second);
    }
    if(COUNT){
        printf("n=%d K=%d count=%llu nodes=%llu memo=%llu\n",NTARGET,K,total,nodes,mused);
    } else if(found){
        std::sort(firstWitness.begin(),firstWitness.end());
        printf("n=%d K=%d mode=%s FOUND size=%zu nodes=%llu witness=",NTARGET,K,mode.c_str(),firstWitness.size(),nodes);
        for(size_t i=0;i<firstWitness.size();++i) printf(i?",%d":"%d",firstWitness[i]);
        printf("\n");
    } else {
        printf("n=%d K=%d mode=%s NONE nodes=%llu memo=%llu\n",NTARGET,K,mode.c_str(),nodes,mused);
    }
    return 0;
}
