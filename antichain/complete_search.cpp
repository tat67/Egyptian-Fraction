// complete_search.cpp -- exact, integer-only search for antichain representations  1 = sum 1/n,  |T| = K,
// of the form  T = M u R :  M = K-J "main" elements (squarefree semiprimes <= L),  R = J "tiny" elements (> L), J in {2,3,4}.
// For every main set M with 1 - J/(L+1) <= sum(M) < 1 the program finds ALL completions R (any integers > L),
// by the classical bounded Egyptian-fraction recursion for the first J-2 tiny elements and an exact two-term solver.
//   two-term lemma : 1/y+1/z = a/D (reduced), y<=z  ==>  z >= a/2            (quick rejection)
//   two-term solver: all solutions are  y = h*w, z = h*(D/w)*(w/yp)  with  w | D, yp | w, gcd(yp,D/w)=1, a | yp + D/w.
#include <bits/stdc++.h>
#include <thread>
#include <atomic>
#include <mutex>
using namespace std;
typedef unsigned __int128 u128; typedef unsigned long long u64;
static string s128(u128 x){ if(x==0) return "0"; string s; while(x){ s+=char('0'+(int)(x%10)); x/=10;} reverse(s.begin(),s.end()); return s; }
static u64 gcd64(u64 a,u64 b){ while(b){ u64 t=a%b; a=b; b=t;} return a; }
struct U256 { u128 hi, lo; };
static U256 mul128(u128 a,u128 b){ u64 a0=(u64)a,a1=(u64)(a>>64),b0=(u64)b,b1=(u64)(b>>64); u128 p00=(u128)a0*b0,p01=(u128)a0*b1,p10=(u128)a1*b0,p11=(u128)a1*b1; u128 mid=(p00>>64)+(u64)p01+(u64)p10; U256 r; r.lo=((u128)(u64)mid<<64)|(u64)p00; r.hi=p11+(p01>>64)+(p10>>64)+(mid>>64); return r; }
static bool lt256(const U256&a,const U256&b){ return a.hi<b.hi||(a.hi==b.hi&&a.lo<b.lo); }
static U256 sub256(const U256&a,const U256&b){ U256 r; r.lo=a.lo-b.lo; r.hi=a.hi-b.hi-(a.lo<b.lo?1:0); return r; }
static bool divmod256(U256 n,u128 d,u128&q,u128&rem){ if(n.hi>=d) return false; u128 r=n.hi,qq=0; for(int i=127;i>=0;i--){ bool top=(r>>127)&1; r=(r<<1)|((n.lo>>i)&1); if(top||r>=d){ r-=d; qq|=((u128)1<<i);} } q=qq; rem=r; return true; }
static inline int bits128(u128 x){ u64 h=(u64)(x>>64); if(h) return 128-__builtin_clzll(h); u64 l=(u64)x; return l?64-__builtin_clzll(l):0; }
static inline bool fastdiv(const U256&B,u128 A,u128&q,u128&rem){ // exact floor(B/A), remainder, when quotient < 2^62
  int sh=bits128(A)-62; if(sh<0) sh=0; u128 Ah=A>>sh; U256 Bs; if(sh==0) Bs=B; else { Bs.lo=(B.lo>>sh)|(B.hi<<(128-sh)); Bs.hi=B.hi>>sh; }
  if(Bs.hi) return false; u128 qe=Bs.lo/Ah; if(qe>>62) return false; if(qe>=2) qe-=2; else qe=0;
  U256 P=mul128(qe,A); if(lt256(B,P)) return false; U256 R=sub256(B,P); int it=0; U256 AA; AA.hi=0; AA.lo=A;
  while((R.hi||R.lo>=A)&&it<8){ R=sub256(R,AA); qe++; it++; } if(R.hi||R.lo>=A) return false; q=qe; rem=R.lo; return true; }
static u64 mod256_64(const U256&n,u64 m){ u128 r=n.hi%m; r=((r<<64)|(u64)(n.lo>>64))%m; r=((r<<64)|(u64)n.lo)%m; return (u64)r; }
static U256 div256_64(const U256&n,u64 d){ U256 r; u64 a3=(u64)(n.hi>>64),a2=(u64)n.hi,a1=(u64)(n.lo>>64),a0=(u64)n.lo; u128 c=a3; u64 q3=(u64)(c/d); c=((c%d)<<64)|a2; u64 q2=(u64)(c/d); c=((c%d)<<64)|a1; u64 q1=(u64)(c/d); c=((c%d)<<64)|a0; u64 q0=(u64)(c/d); r.hi=((u128)q3<<64)|q2; r.lo=((u128)q1<<64)|q0; return r; }
static U256 mul256_128(const U256&a,u128 b,bool&ovf){ U256 lo=mul128(a.lo,b); U256 hi=mul128(a.hi,b); U256 r; r.lo=lo.lo; r.hi=lo.hi+hi.lo; if(hi.hi||r.hi<lo.hi) ovf=true; return r; }
static bool isPrimePower(u64 n){ for(u64 p=2;p*p<=n;p++) if(n%p==0){ while(n%p==0) n/=p; return n==1; } return true; }

// ---------------- global problem data ----------------
static int L, KK, J, MSIZE; static vector<int> PR; static vector<u64> PT;
static vector<int> itemN, itemP, itemQ; static int NI; static vector<u128> vup, vdn; static const u128 ONE=((u128)1)<<96; static u128 WINUP;
static vector<vector<u128>> bestup;
struct PF { u64 p; int e; };
static void factor64(u64 x,vector<PF>&out){ out.clear(); for(u64 p:PT){ if(p*p>x) break; if(x%p==0){ int e=0; while(x%p==0){ x/=p; e++; } out.push_back({p,e}); } } if(x>1) out.push_back({x,1}); }
struct Stats { atomic<long long> cliqueCut{0}, typedCalls{0}, part2{0}, scan2{0}, smallCut{0}; atomic<long long> leaves{0}, windowOut{0}, overflow{0}, cliqueBig{0}, solved{0}, cand1{0}, cand2{0}, slowTwo{0}, unresolved{0}, sols{0}, nonpos{0}; };
static Stats ST; static mutex outmx;

static u128 XMAX=((u128)1)<<31;   // inner ranges longer than this are not scanned; the case is logged as UNRESOLVED
struct Solver {
  vector<int> M; vector<char> inM; // inM[n] for n<=L
  u128 a, D; vector<PF> fD;         // r = a/D reduced, factorisation of D
  vector<unsigned char> flags; vector<u64> gb;
  Solver(){ inM.assign(L+1,0); }
  bool compat64(u64 n){ for(int m:M) if(n%(u64)m==0) return false; return true; }
  bool compat256(const U256&z){ for(int m:M) if(mod256_64(z,(u64)m)==0) return false; return true; }
  void unresolved(const char*why,const vector<u64>&prev){ ST.unresolved++; lock_guard<mutex> lk(outmx); printf("UNRESOLVED %s prev:",why); for(u64 v:prev) printf(" %llu",v); printf(" core:"); for(int m:M) printf(" %d",m); printf("\n"); fflush(stdout); }
  void report(const vector<u64>&prev,u64 y,const U256&Z){ lock_guard<mutex> lk(outmx); ST.sols++; printf("SOLUTION size=%d :",(int)M.size()+(int)prev.size()+2); for(int m:M) printf(" %d",m); printf(" |"); for(u64 v:prev) printf(" %llu",v); printf(" %llu %s%s\n",y,Z.hi?"HI:":"",s128(Z.lo).c_str()); fflush(stdout); }
  // ---- exact two-term solver: all (y,z), prev.back() < y < z, with 1/y + 1/z = A/B.   f = factorisation of B. ----
  // Reduced a2/D2.  Every solution is y = h*w, z = y*D2/(w*yp) with w | D2, yp | w, gcd(yp,D2/w)=1, yp = a2*h - D2/w >= 1,
  // hence a2*y - D2 = w*yp <= w^2 and y in (D2/a2, D2/a2 + w^2/a2].  With y0 = floor(D2/a2)+1, rho = a2*y0 - D2:
  //   (1) y = y0 :  solution  <=>  rho | D2*y0   (then rho = w*yp <= gcd(y0,D2)^2 : cheap pre-test);
  //   (2) y > y0 :  needs a divisor w of D2 with w | y and w^2 >= a2*(y-y0) + rho > a2, i.e. w > sqrt(a2); enumerated by DFS.
  // Compatibility (necessary): neither w nor D2/w is divisible by an element of M.
  void finish(const vector<u64>&prev,u64 y,const U256&D2,u128 E){ // z = D2*y/E must be an integer
    bool ovf=false; U256 P=mul256_128(D2,(u128)y,ovf); if(ovf){ unresolved("P",prev); return; }
    U256 Z; u128 zr; divfull(P,E,Z,zr); if(zr!=0) return; if(!(Z.hi||Z.lo>(u128)y)) return;
    if(!compat64(y)||!compat256(Z)) return; for(u64 pv:prev){ if(y%pv==0||mod256_64(Z,pv)==0) return; } if(mod256_64(Z,y)==0) return;
    if(isPrimePower(y)) return; report(prev,y,Z); }
  static void divfull(const U256&n,u128 d,U256&q,u128&rem){ u128 r=0; q.hi=0; q.lo=0; for(int i=255;i>=0;i--){ bool top=(r>>127)&1; u128 bit=(i>=128)?((n.hi>>(i-128))&1):((n.lo>>i)&1); r=(r<<1)|bit; if(top||r>=d){ r-=d; if(i>=128) q.hi|=((u128)1<<(i-128)); else q.lo|=((u128)1<<i); } } rem=r; }
  static u64 isqrt_ceil(u128 a){ u128 lo=0,hi=((u128)1)<<63; while(lo<hi){ u128 mid=(lo+hi)/2; if(mid*mid>=a) hi=mid; else lo=mid+1; } return (u64)lo; }
  static const u64 SCANT=400;
  void twoTermDiv(const vector<u64>&prev,u128 A,U256 B,vector<PF> f){
    ST.slowTwo++;
    u128 a2=A; U256 D2=B; for(auto&u:f){ int c=0; while(c<u.e && a2%(u128)u.p==0){ a2/=(u128)u.p; c++; } if(c){ u.e-=c; for(int i=0;i<c;i++) D2=div256_64(D2,u.p); } }
    u128 q,rem; if(!fastdiv(D2,a2,q,rem)){ if(!divmod256(D2,a2,q,rem)){ unresolved("q",prev); return; } } if(q>>60){ unresolved("y0big",prev); return; }
    u64 y0=(u64)q+1; u128 rho=a2-rem; u64 last=prev.empty()?(u64)L:prev.back();
    if(y0>last){ u64 gm=gcd64(y0,mod256_64(D2,y0)); if(rho<=(u128)gm*gm) finish(prev,y0,D2,rho); }          // (1)
    u128 y2=(u128)(2*y0)*(2*y0); if(a2>y2) return;                                                             // (2) impossible: w <= y < 2*y0
    ST.part2++;
    // (2a) few candidates: y = y0+k needs (y0+k)^2 >= E_k = rho + k*a2 (as E_k = w*yp <= w^2 <= y^2).  If y0^2/a2 is small the
    //      admissible k form a short initial range (E_k - y^2 is increasing there), scanned with the pre-test gcd(y,D2)^2 >= E_k.
    { u128 kap=((u128)y0*y0)/a2; if(kap<=SCANT && a2>(u128)8*y0){ ST.scan2++;
        for(u64 k=1;;k++){ u64 y=y0+k; u128 E=rho+(u128)k*a2; if((u128)y*y<E||y>=2*y0) break; if(y<=last) continue;
          u64 gm=gcd64(y,mod256_64(D2,y)); if((u128)gm*gm>=E) finish(prev,y,D2,E); }
        return; } }
    vector<PF> g; for(auto&u:f) if(u.e>0) g.push_back(u); sort(g.begin(),g.end(),[](const PF&x,const PF&y){return x.p>y.p;}); int n=g.size(); if(n>60){ unresolved("manyprimes",prev); return; }
    vector<u64> adj(n,0); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++){ u128 pq=(u128)g[i].p*g[j].p; if(pq<=(u128)L && inM[(int)pq]){ adj[i]|=1ull<<j; adj[j]|=1ull<<i; } }
    u64 wmin=isqrt_ceil(a2), wmax=2*y0; vector<u128> suf(n+1,1); for(int i=n-1;i>=0;i--){ u128 t=suf[i+1]; for(int k=0;k<g[i].e;k++){ if(t<(((u128)1)<<64)) t*=g[i].p; } suf[i]=t; }
    vector<int> fexp(n,0);
    function<void(int,u64,u64,u64)> rec=[&](int i,u64 w,u64 inW,u64 inC){
      if((u128)w*suf[i]<(u128)wmin) return;
      if(i==n){ // multiples y of w in (y0, y0 + w^2/a2]
        u128 span=((u128)w*w)/a2; u64 h=y0/w+1;
        for(;;h++){ u128 yy=(u128)h*w; if(yy>(u128)y0+span||yy>(u128)wmax) break; u64 y=(u64)yy; if(y<=last) continue;
          u128 E=rho+(u128)(y-y0)*a2; if(E%(u128)w!=0) continue; u128 yp=E/(u128)w; if(yp>(u128)w) break; if((u128)w%yp!=0) continue;
          bool cop=true; for(int k=0;k<n;k++) if(fexp[k]<g[k].e && yp%(u128)g[k].p==0){ cop=false; break; } if(!cop) continue;
          finish(prev,y,D2,E); }
        return; }
      for(int fc=0; fc<=g[i].e; fc++){ if(fc>0){ if(w>wmax/g[i].p) break; w*=g[i].p; }
        bool inw=(fc>0), inc=(fc<g[i].e); if(inw&&(adj[i]&inW)) break; if(inc&&(adj[i]&inC)) continue;
        fexp[i]=fc; rec(i+1,w,inW|(inw?1ull<<i:0),inC|(inc?1ull<<i:0)); }
      fexp[i]=0; };
    rec(0,1,0,0);
  }
  // one more tiny element x in (lo,hi], then the exact two-term step.  r' = a1/D1 with factorisation f1; prev = earlier tiny elements
  void lastThree(const vector<u64>&prev,u128 a1,u128 D1,const vector<PF>&f1){
    u128 lo=D1/a1; u64 last=prev.empty()?(u64)L:prev.back(); if(lo<last) lo=last; u128 hi=3*D1/a1; if(lo>=hi) return; if(hi>XMAX){ unresolved("range",prev); return; }
    // --- clique rule: primes of D1 that are pairwise adjacent (p*q in M) lie in pairwise different tiny elements, and every prime of D1
    //     divides at least one of the 3 remaining elements.  >=4 such primes: impossible.  Exactly 3 (each to the first power in D1):
    //     each of x,y,z contains exactly one of them, alone, so x = q*m with m = (D1/q)*a1^{-1} (mod q) for one clique prime q.
    if(!getenv("NOCLIQUE")){ int n=f1.size(); vector<int> best,cur; function<void(int)> rc=[&](int st){ if(cur.size()>best.size()) best=cur; if(best.size()>=4) return; for(int v=st;v<n;v++){ bool ok=true; for(int w:cur){ u128 pq=(u128)f1[v].p*f1[w].p; if(!(pq<=(u128)L && inM[(int)pq])){ ok=false; break; } } if(ok){ cur.push_back(v); rc(v+1); cur.pop_back(); if(best.size()>=4) return; } } };
      rc(0);
      if(best.size()>=4){ ST.cliqueCut++; return; }
      if(best.size()==3 && f1[best[0]].e==1 && f1[best[1]].e==1 && f1[best[2]].e==1){ ST.typedCalls++;
        vector<u64> pv2=prev; pv2.push_back(0); vector<PF> fx, fall;
        for(int bi=0;bi<3;bi++){ u64 qv=f1[best[bi]].p; u64 dq=(u64)((D1/(u128)qv)%qv), aq=(u64)(a1%qv); u64 inv=0; for(u64 t=1;t<qv;t++) if((aq*t)%qv==1){ inv=t; break; } u64 tq=(dq*inv)%qv; u64 mod=qv*qv, res=qv*tq;
          u64 x=(u64)lo+1; { u64 r0=x%mod; x+=(res+mod-r0)%mod; }
          for(;x<=(u64)hi;x+=mod){ ST.cand2++; if(!compat64(x)) continue;
            u128 A=a1*x-D1; U256 B=mul128(D1,x); u128 q,rem; if(!fastdiv(B,A,q,rem)){ if(!divmod256(B,A,q,rem)||(q>>62)){ pv2.back()=x; unresolved("div",pv2); continue; } }
            u128 y0=q+1,e=A-rem; u128 g=1; { u128 At=A; for(auto&u:f1) if(x%u.p==0){ int c=u.e; u64 xt=x; while(xt%u.p==0){ xt/=u.p; c++; } while(c>0 && At%(u128)u.p==0){ At/=(u128)u.p; if(!(g>>100)) g*=u.p; c--; } } }
            if(!(y0>>50)&&!(g>>20)){ if(e>=2*g*y0*y0) continue; }
            bool bad=false; for(u64 pv:prev) if(x%pv==0){ bad=true; break; } if(bad) continue; if(isPrimePower(x)) continue;
            factor64(x,fx); fall=f1; for(auto&t:fx){ bool found=false; for(auto&u:fall) if(u.p==t.p){ u.e+=t.e; found=true; break; } if(!found) fall.push_back(t); }
            pv2.back()=x; twoTermDiv(pv2,A,B,fall); } }
        return; } }
    const u64 SEG=1u<<15; if(flags.size()<SEG){ flags.assign(SEG,0); gb.assign(SEG,1); }
    vector<u64> pp; for(auto&u:f1){ u64 pw=1; for(int i=0;i<u.e;i++){ if(pw<(1ull<<40)) pw*=u.p; } pp.push_back(u.p); pp.push_back(pw); }
    vector<u64> pv2=prev; pv2.push_back(0); vector<PF> fx, fall;
    // quotient q = floor(D1*x/(a1*x-D1)) and remainder are updated incrementally for x -> x+1 once x - D1/a1 >= (D1/a1)/3
    // (then q drops by at most ~9 per step); below that threshold they are computed from scratch for the admissible x only.
    u64 xthr=(u64)lo+(u64)(lo/3)+2; int ba1=bits128(a1); bool valid=false; u128 q=0,rem=0,A=0;
    for(u64 base=(u64)lo+1; base<=(u64)hi; base+=SEG){ u64 len=min<u64>(SEG,(u64)hi-base+1); memset(flags.data(),0,len); for(u64 i=0;i<len;i++) gb[i]=1;
      for(int m:M){ u64 r0=base%(u64)m; u64 st=r0?(u64)m-r0:0; for(u64 i=st;i<len;i+=(u64)m) flags[i]=1; }
      for(size_t k=0;k<pp.size();k+=2){ u64 p=pp[k],pw=pp[k+1]; u64 r0=base%p; u64 st=r0?p-r0:0; for(u64 i=st;i<len;i+=p) if(gb[i]<(1ull<<31)) gb[i]*=pw; }
      ST.cand2+=len;
      for(u64 i=0;i<len;i++){ u64 x=base+i; bool have=false;
        if(x>=xthr && valid && bits128(q)+ba1<=120 && !(D1>>120) && !(A>>120)){
          A+=a1; __int128 t=(__int128)rem+(__int128)D1-(__int128)(q*a1); int it=0; while(t<0&&it<16){ t+=(__int128)A; q--; it++; }
          if(t>=0 && t<(__int128)A){ rem=(u128)t; have=true; } else valid=false; }
        if(!have){ if(x<xthr && flags[i]){ valid=false; continue; }
          A=a1*x-D1; U256 B=mul128(D1,x); if(!fastdiv(B,A,q,rem)){ if(!divmod256(B,A,q,rem)||(q>>62)){ valid=false; if(!flags[i]){ pv2.back()=x; unresolved("div",pv2); } continue; } }
          valid=true; }
        if(flags[i]) continue;
        u128 y0=q+1,e=A-rem; u128 gbnd=1; if(gb[i]>1){ if(gb[i]>>31) gbnd=(u128)gb[i]*gb[i]; else { u64 g2=gb[i]*gb[i]; gbnd=gcd64((u64)(A%g2),g2); } }
        if(!(y0>>50)&&!(gbnd>>20)){ if(e>=2*gbnd*y0*y0) continue; }   // two-term lemma: no solution with this x
        bool bad=false; for(u64 pv:prev) if(x%pv==0){ bad=true; break; } if(bad) continue; if(isPrimePower(x)) continue;
        factor64(x,fx); fall=f1; for(auto&t:fx){ bool found=false; for(auto&u:fall) if(u.p==t.p){ u.e+=t.e; found=true; break; } if(!found) fall.push_back(t); }
        pv2.back()=x; twoTermDiv(pv2,A,mul128(D1,x),fall); } }
  }
  void solve(){
    ST.solved++; vector<u64> prev;
    if(J==2){ U256 B; B.hi=0; B.lo=D; twoTermDiv(prev,a,B,fD); return; }
    if(J==3){ lastThree(prev,a,D,fD); return; }
    // J==4 : first tiny element n1 in (max(L,D/a), 4D/a]
    u128 lo=D/a; if(lo<(u128)L) lo=L; u128 hi=4*D/a; if(hi>>40){ unresolved("range1",prev); return; }
    vector<PF> fx,f1;
    u64 only=getenv("N1ONLY")?strtoull(getenv("N1ONLY"),0,10):0;
    for(u64 n1=(u64)lo+1;n1<=(u64)hi;n1++){ if(only&&n1!=only) continue; if(!compat64(n1)||isPrimePower(n1)) continue; ST.cand1++;
      U256 an=mul128(a,n1); U256 Dn=mul128(D,n1); if(an.hi||Dn.hi){ prev.assign(1,n1); unresolved("ovf1",prev); prev.clear(); continue; } if(an.lo<=D) continue; u128 A1=an.lo-D, D1=Dn.lo;
      factor64(n1,fx); f1=fD; for(auto&t:fx){ bool found=false; for(auto&u:f1) if(u.p==t.p){ u.e+=t.e; found=true; break; } if(!found) f1.push_back(t); }
      for(auto&u:f1){ while(u.e>0 && A1%(u128)u.p==0){ A1/=(u128)u.p; D1/=(u128)u.p; u.e--; } }
      vector<PF> f2; for(auto&u:f1) if(u.e>0) f2.push_back(u);
      prev.assign(1,n1); lastThree(prev,A1,D1,f2); prev.clear(); }
  }
};

// ---------------- core enumeration (parallel) ----------------
struct Task { int pos,cnt; u128 sup,sdn; vector<int> chosen; };
static vector<Task> tasks; static int SPLIT;
static void gen(int pos,int cnt,u128 sup,u128 sdn,vector<int>&ch){
  if(cnt==MSIZE||pos==SPLIT){ tasks.push_back({pos,cnt,sup,sdn,ch}); return; }
  if(pos==NI||NI-pos<MSIZE-cnt) return; if(sup+bestup[pos][MSIZE-cnt]+WINUP<ONE) return;
  if(sdn+vdn[pos]<=ONE){ ch.push_back(pos); gen(pos+1,cnt+1,sup+vup[pos],sdn+vdn[pos],ch); ch.pop_back(); }
  gen(pos+1,cnt,sup,sdn,ch);
}
static const int SMALLP[6]={2,3,5,7,11,13};
static vector<array<signed char,6>> itemRes; // itemRes[i][k] = (n_i/p_k)^{-1} mod p_k if p_k | n_i, else 0
struct Worker { Solver S; vector<int> ch; vector<int> pcnt; int rs[6]={0,0,0,0,0,0}; // prime usage counts (index in PR); residue sums at small primes
  vector<int> pidx; Worker(){ pcnt.assign(PR.size(),0); pidx.assign(L+1,-1); for(size_t i=0;i<PR.size();i++) pidx[PR[i]]=i; }
  void leaf(){
    // cheap pre-test: the unsatisfied primes among 2,3,5,7,11,13 that are pairwise adjacent need pairwise different tiny elements
    { int us[6],nu=0; for(int k=0;k<6;k++) if(rs[k]%SMALLP[k]!=0) us[nu++]=SMALLP[k];
      if(nu>J){ // look for J+1 pairwise adjacent ones
        int best=0; for(int mask=1;mask<(1<<nu);mask++){ int c=__builtin_popcount(mask); if(c<=best) continue; bool ok=true; for(int i=0;i<nu&&ok;i++) if(mask>>i&1) for(int j=i+1;j<nu;j++) if((mask>>j&1) && !S.inM[us[i]*us[j]]){ ok=false; break; } if(ok) best=c; }
        if(best>J){ ST.smallCut++; return; } } }
    // exact r = 1 - sum 1/n  with den = product of the primes used (all items squarefree semiprimes)
    u128 den=1; bool ovf=false; for(size_t i=0;i<PR.size();i++) if(pcnt[i]){ if(den>(((u128)1)<<120)/PR[i]){ ovf=true; break; } den*=PR[i]; }
    if(ovf){ ST.overflow++; lock_guard<mutex> lk(outmx); printf("OVERFLOW core:"); for(int p:ch) printf(" %d",itemN[p]); printf("\n"); return; }
    u128 num=0; for(int p:ch) num+=den/(u128)itemN[p];
    if(num>=den){ ST.nonpos++; if(num==den){ lock_guard<mutex> lk(outmx); printf("SOLUTION size=%d (main only):",MSIZE); for(int p:ch) printf(" %d",itemN[p]); printf("\n"); } return; }
    u128 R=den-num; // window: R/den <= J/(L+1)
    { U256 l=mul128(R,(u128)(L+1)); U256 r4=mul128(den,(u128)J); if(lt256(r4,l)){ ST.windowOut++; return; } }
    ST.leaves++;
    S.fD.clear(); u128 a=R, D=den; for(size_t i=0;i<PR.size();i++) if(pcnt[i]){ if(a%(u128)PR[i]==0){ a/=(u128)PR[i]; D/=(u128)PR[i]; } else S.fD.push_back({(u64)PR[i],1}); }
    S.a=a; S.D=D; S.M.clear(); for(int p:ch) S.M.push_back(itemN[p]);
    // clique test among unsatisfied primes: more than J pairwise adjacent ones => impossible
    { int u=S.fD.size(); vector<int> best,cur; function<void(int)> rec=[&](int st){ if((int)cur.size()>(int)best.size()) best=cur; if((int)best.size()>J) return; for(int v=st;v<u;v++){ bool ok=true; for(int w:cur){ u64 pq=S.fD[v].p*S.fD[w].p; if(!(pq<=(u64)L && S.inM[pq])){ ok=false; break; } } if(ok){ cur.push_back(v); rec(v+1); cur.pop_back(); } } };
      rec(0); if((int)best.size()>J){ ST.cliqueBig++; return; } }
    S.solve();
  }
  void dfs(int pos,int cnt,u128 sup,u128 sdn){
    if(cnt==MSIZE){ leaf(); return; }
    if(pos==NI||NI-pos<MSIZE-cnt) return; if(sup+bestup[pos][MSIZE-cnt]+WINUP<ONE) return;
    if(sdn+vdn[pos]<=ONE){ inc(pos,1); dfs(pos+1,cnt+1,sup+vup[pos],sdn+vdn[pos]); inc(pos,-1); }
    dfs(pos+1,cnt,sup,sdn);
  }
  void inc(int pos,int d){ if(d>0){ ch.push_back(pos); S.inM[itemN[pos]]=1; } else { ch.pop_back(); S.inM[itemN[pos]]=0; } pcnt[pidx[itemP[pos]]]+=d; pcnt[pidx[itemQ[pos]]]+=d; if(itemP[pos]<=13){ const auto&r=itemRes[pos]; for(int k=0;k<6;k++) rs[k]+=d*r[k]; } }
  void run(const Task&t){ for(int p:t.chosen) inc(p,1); dfs(t.pos,t.cnt,t.sup,t.sdn); for(size_t i=0;i<t.chosen.size();i++) inc(t.chosen[t.chosen.size()-1-i],-1); }
};
int main(int argc,char**argv){
  if(argc<4){ fprintf(stderr,"usage: ac L K J [threads] [itemcap]\n"); return 1; }
  if(getenv("XMAXBITS")) XMAX=((u128)1)<<atoi(getenv("XMAXBITS"));
  L=atoi(argv[1]); KK=atoi(argv[2]); J=atoi(argv[3]); int nth=argc>4?atoi(argv[4]):4; int itemcap=argc>5?atoi(argv[5]):L; MSIZE=KK-J;
  { vector<char> s(1<<20,1); for(u64 i=2;i<(1u<<20);i++) if(s[i]){ PT.push_back(i); for(u64 j=i*i;j<(1u<<20);j+=i) s[j]=0; } }
  for(int i=2;i<=L;i++){ bool ok=true; for(int j=2;j*j<=i;j++) if(i%j==0) ok=false; if(ok) PR.push_back(i); }
  vector<array<int,3>> its; for(size_t i=0;i<PR.size();i++) for(size_t j=i+1;j<PR.size();j++){ long long n=(long long)PR[i]*PR[j]; if(n<=itemcap) its.push_back({(int)n,PR[i],PR[j]}); }
  sort(its.begin(),its.end()); for(auto&t:its){ itemN.push_back(t[0]); itemP.push_back(t[1]); itemQ.push_back(t[2]); vup.push_back((ONE+t[0]-1)/t[0]); vdn.push_back(ONE/t[0]); }
  NI=its.size(); WINUP=((u128)J*ONE+L)/(L+1)+1;
  itemRes.assign(NI,array<signed char,6>{0,0,0,0,0,0}); for(int i=0;i<NI;i++) for(int k=0;k<6;k++){ int p=SMALLP[k]; if(itemN[i]%p==0){ int c=(itemN[i]/p)%p; int inv=0; for(int t=1;t<p;t++) if((c*t)%p==1) inv=t; itemRes[i][k]=(signed char)inv; } }
  bestup.assign(NI+1,vector<u128>(MSIZE+2,0)); for(int pos=NI-1;pos>=0;pos--) for(int t=1;t<=MSIZE+1;t++) bestup[pos][t]=(pos+t<=NI)?bestup[pos+1][t-1]+vup[pos]:0;
  SPLIT=min(NI,argc>6?atoi(argv[6]):60);
  if(getenv("COREFILE")){ ifstream f(getenv("COREFILE")); string line; map<int,int> pos; for(int i=0;i<NI;i++) pos[itemN[i]]=i;
    while(getline(f,line)){ istringstream is(line); int x; Task t; t.pos=NI; t.cnt=0; t.sup=0; t.sdn=0; bool ok=true; while(is>>x){ if(!pos.count(x)){ ok=false; break; } t.chosen.push_back(pos[x]); t.cnt++; } if(ok&&t.cnt==MSIZE) tasks.push_back(t); }
  } else { vector<int> ch; gen(0,0,0,0,ch); }
  fprintf(stderr,"L=%d K=%d J=%d MSIZE=%d items=%d tasks=%zu\n",L,KK,J,MSIZE,NI,tasks.size());
  atomic<size_t> ticket(0); vector<thread> th; auto t0=chrono::steady_clock::now();
  for(int t=0;t<nth;t++) th.emplace_back([&](){ Worker W; while(true){ size_t id=ticket++; if(id>=tasks.size()) break; W.run(tasks[id]);
    if(id%2000==0){ long long el=chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now()-t0).count(); fprintf(stderr,"  task %zu/%zu  %llds smallCut=%lld leaves=%lld cliqueBig=%lld solved=%lld cand2=%lld slowTwo=%lld unresolved=%lld sols=%lld\n",id,tasks.size(),el,(long long)ST.smallCut,(long long)ST.leaves,(long long)ST.cliqueBig,(long long)ST.solved,(long long)ST.cand2,(long long)ST.slowTwo,(long long)ST.unresolved,(long long)ST.sols); } } });
  for(auto&x:th) x.join();
  long long el=chrono::duration_cast<chrono::seconds>(chrono::steady_clock::now()-t0).count();
  fprintf(stderr,"DONE %llds leaves(in window)=%lld windowOut=%lld nonpos=%lld overflow=%lld cliqueBig(>J)=%lld solved=%lld cand1=%lld cand2=%lld slowTwo=%lld unresolved=%lld sols=%lld cliqueCut=%lld typedCalls=%lld part2=%lld scan2=%lld smallCut=%lld\n",el,(long long)ST.leaves,(long long)ST.windowOut,(long long)ST.nonpos,(long long)ST.overflow,(long long)ST.cliqueBig,(long long)ST.solved,(long long)ST.cand1,(long long)ST.cand2,(long long)ST.slowTwo,(long long)ST.unresolved,(long long)ST.sols,(long long)ST.cliqueCut,(long long)ST.typedCalls,(long long)ST.part2,(long long)ST.scan2,(long long)ST.smallCut);
}
