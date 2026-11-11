// plain_search.cpp -- constructive search for antichain representations 1 = sum_{n in T} 1/n with |T| = K.
// Exact integer arithmetic only (unsigned __int128); no floating point.
//
// T = C u F, where
//   C ("core")   : K-J squarefree semiprimes p*q with p < q <= B whose reciprocal sum lies in [1 - 1/W, 1);
//   F ("fixers") : at most J squarefree integers with >= 3 prime factors, all dividing D, where r = 1 - sum(C) = a/D in lowest
//                  terms; the prime set of each fixer is independent in the graph of C (so no element of C divides it),
//                  and no fixer divides another.
// Writing c = D/n for a fixer n, the fixers are exactly sets of divisors c of D with  sum c = a,  which is searched
// exhaustively in decreasing order of c (the largest c is >= a/J).  Every set printed has reciprocal sum exactly 1.
//
//   g++ -O2 -pthread -o plain_search plain_search.cpp
//   ./plain_search 61 43 4 600 4        # B=61, K=43, J=4, W=600, 4 threads : prints twelve 43-element solutions
#include <bits/stdc++.h>
#include <thread>
#include <atomic>
#include <mutex>
using namespace std;
typedef unsigned __int128 u128;
static vector<int> PR; static int NP;
static vector<int> itemP, itemQ, itemN; static vector<u128> val; static u128 D0;
static int NI, M, J; static u128 WIN; static vector<vector<u128>> best; static u128 NMAX;
static string s128(u128 x){ if(x==0) return "0"; string s; while(x){ s+=char('0'+(int)(x%10)); x/=10;} reverse(s.begin(),s.end()); return s; }
static u128 gcd128(u128 a,u128 b){ while(b){ u128 t=a%b; a=b; b=t;} return a; }
struct Core { bitset<256> in; u128 N; };
static vector<Core> cores; static bitset<256> curin;
static void dfs(int pos,int cnt,u128 N){
  if(cnt==M){ if(N>=D0-WIN && N<D0){ cores.push_back({curin,N}); } return; }
  if(pos==NI) return; int need=M-cnt; if(NI-pos<need) return;
  if(N+best[pos][need] < D0-WIN) return;
  u128 N2=N+val[pos]; if(N2<D0){ curin[pos]=1; dfs(pos+1,cnt+1,N2); curin[pos]=0; }
  dfs(pos+1,cnt,N);
}
struct Solver {
  vector<int> up; vector<unsigned> adj; int u; u128 D; bool odd; 
  vector<u128> cs; vector<unsigned> ms; // valid fixers: c = D/n ascending, mask
  vector<int> chosen; vector<vector<int>> out; long long work=0; long long cap;
  void gen(int idx,u128 prod,unsigned mask,unsigned forb,int cnt,vector<pair<u128,unsigned>>&res){
    if(idx<0){ if(cnt>=3) res.push_back({prod,mask}); return; }
    gen(idx-1,prod,mask,forb,cnt,res);
    if(!(forb>>idx&1)){ u128 np=prod*(u128)up[idx]; if(np<=NMAX) gen(idx-1,np,mask|(1u<<idx),forb|adj[idx],cnt+1,res); }
  }
  void build(){ vector<pair<u128,unsigned>> r; gen(u-1,1,0,0,0,r); sort(r.begin(),r.end(),[](const pair<u128,unsigned>&a,const pair<u128,unsigned>&b){return a.first>b.first;});
    for(auto&x:r){ cs.push_back(D/x.first); ms.push_back(x.second);} }
  int lb(u128 x,int hi){ return lower_bound(cs.begin(),cs.begin()+hi,x)-cs.begin(); } // first idx with c>=x
  bool nested(int i){ for(int j:chosen){ unsigned a=ms[i],b=ms[j]; if((a&b)==a||(a&b)==b) return true; } return false; }
  void solve(u128 rem,int left,int hiIdx){ // sum of <=left c's with index < hiIdx equals rem
    if(work>cap) return;
    if(odd && ((rem&1)!=(u128)(left&1))) left--;
    if(left<=0) return;
    int top=lb(rem,hiIdx); // indices < top have c < rem
    if(top<hiIdx && cs[top]==rem){ if(!nested(top)){ chosen.push_back(top); out.push_back(chosen); chosen.pop_back(); } }
    if(left==1) return;
    u128 clo=(rem+left-1)/left; int lo=lb(clo,top);
    if(left==2 || (odd && left==3)){ // exactly two terms (if odd && left==3 then rem is odd... handled: left parity matched => 3 terms allowed)
    }
    if(left==2){ for(int i=top-1;i>=lo;i--){ work++; u128 c2=rem-cs[i]; int k=lb(c2,i); if(k<i && cs[k]==c2){ if(!nested(i)){ chosen.push_back(i); if(!nested(k)){ chosen.push_back(k); out.push_back(chosen); chosen.pop_back(); } chosen.pop_back(); } } } return; }
    for(int i=top-1;i>=lo;i--){ work++; if(nested(i)) continue; chosen.push_back(i); solve(rem-cs[i],left-1,i); chosen.pop_back(); if(work>cap) return; }
  }
};
int main(int argc,char**argv){
  int B=atoi(argv[1]); int K=atoi(argv[2]); J=atoi(argv[3]); long long W=atoll(argv[4]); int nth=argc>5?atoi(argv[5]):4; long long cap=argc>6?atoll(argv[6]):2000000000LL; 
  int maxitem=argc>8?atoi(argv[8]):1000000;
  NMAX=1; { // NMAX = 10^k from arg (integer power of ten exponent)
    int e=argc>7?atoi(argv[7]):30; for(int i=0;i<e;i++) NMAX*=10; }
  for(int i=2;i<=B;i++){bool ok=true;for(int j=2;j*j<=i;j++)if(i%j==0)ok=false; if(ok)PR.push_back(i);} NP=PR.size();
  D0=1; for(int p:PR) D0*=(u128)p;
  vector<array<int,3>> its; for(int i=NP-1;i>=1;i--) for(int j=0;j<i;j++) if(PR[i]*PR[j]<=maxitem) its.push_back({i,j,PR[i]*PR[j]});
  sort(its.begin(),its.end(),[](const array<int,3>&a,const array<int,3>&b){return a[2]<b[2];});
  for(auto&t:its){ itemP.push_back(t[0]); itemQ.push_back(t[1]); itemN.push_back(t[2]); val.push_back(D0/(u128)t[2]); }
  NI=its.size(); M=K-J; WIN=D0/(u128)W;
  best.assign(NI+1, vector<u128>(M+2,0));
  for(int pos=NI-1;pos>=0;pos--) for(int t=1;t<=M+1;t++) best[pos][t]= (pos+t<=NI)? best[pos+1][t-1]+val[pos] : 0;
  dfs(0,0,0);
  fprintf(stderr,"B=%d NI=%d K=%d J=%d M=%d window=1/%lld cores=%zu\n",B,NI,K,J,M,W,cores.size());
  atomic<size_t> ticket(0); atomic<long long> sols(0), capped(0); mutex mx; vector<thread> th;
  for(int t=0;t<nth;t++) th.emplace_back([&](){ while(true){ size_t id=ticket++; if(id>=cores.size()) break; Core&c=cores[id];
      u128 R=D0-c.N; u128 g=gcd128(R,D0); Solver S; S.D=D0/g; u128 a=R/g; S.cap=cap;
      for(int i=0;i<NP;i++) if(S.D%(u128)PR[i]==0) S.up.push_back(PR[i]); S.u=S.up.size(); S.adj.assign(S.u,0); S.odd=(S.D&1);
      map<int,int> idx; for(int i=0;i<S.u;i++) idx[S.up[i]]=i;
      for(int i=0;i<NI;i++) if(c.in[i]){ auto x=idx.find(PR[itemP[i]]); auto y=idx.find(PR[itemQ[i]]); if(x!=idx.end()&&y!=idx.end()){ S.adj[x->second]|=1u<<y->second; S.adj[y->second]|=1u<<x->second; } }
      S.build(); S.solve(a,J,(int)S.cs.size());
      if(S.work>cap) capped++;
      if(!S.out.empty()){ lock_guard<mutex> lk(mx); for(auto&v:S.out){ sols++; printf("SOLUTION size=%d :",(int)(M+v.size())); for(int i=0;i<NI;i++) if(c.in[i]) printf(" %d",itemN[i]); printf(" |"); for(int x:v) printf(" %s",s128(S.D/S.cs[x]).c_str()); printf("\n"); } fflush(stdout); }
      if(id%200==0){ fprintf(stderr,"  core %zu/%zu sols=%lld capped=%lld (u=%d fixers=%zu work=%lld)\n",id,cores.size(),(long long)sols,(long long)capped,S.u,S.cs.size(),S.work); }
  }});
  for(auto&x:th) x.join();
  fprintf(stderr,"done cores=%zu sols=%lld capped=%lld\n",cores.size(),(long long)sols,(long long)capped);
}
