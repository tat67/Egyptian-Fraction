# Upper estimate of the number of big-prime star configurations whose loss fits the h = 1 budget
# (README section 3).  Float arithmetic: used only for this size estimate, never for a decision.
import sys, math
from sympy import primerange, factorint
K,A,Y,sigma=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),float(sys.argv[4])
B=int(sys.argv[5]) if len(sys.argv)>5 else math.isqrt(Y)
lam=1/A
budget=sigma-lam+1/(Y+1)   # h=1 band upper end (largest budget)
STEP=1e-5; NB=int(budget/STEP)+1
def ispp(n): return len(factorint(n))==1
total=[0]*NB; total[0]=1
nstars=[]
for P in sorted(primerange(B+1, Y//2+1), reverse=True):
    ms=list(range(2,Y//P+1))
    WP=sum(1/(P*q)-lam for q in ms if q in set(primerange(2,ms[-1]+1)) and P*q<A)
    # enumerate antichains of ms with loss<=budget
    dist=[0]*NB; cnt=0
    def rec(i,chosen,val):
        global cnt
        if i==len(ms):
            loss=WP-val
            if loss<=budget+1e-12:
                dist[max(0,int(loss/STEP))]+=1
            return
        m=ms[i]
        # bound: max further value = sum of positive w for remaining
        rest=sum(max(0,1/(P*mm)-lam) for mm in ms[i:])
        if WP-(val+rest)>budget: return
        rec(i+1,chosen,val)
        if all(m%c for c in chosen):
            rec(i+1,chosen+[m],val+1/(P*m)-lam)
    rec(0,[],0.0)
    nstars.append((P,sum(dist)))
    new=[0]*NB
    for i,t in enumerate(total):
        if t:
            for j,d in enumerate(dist):
                if d and i+j<NB: new[i+j]+=t*d
    total=new
print("K",K,"A",A,"Y",Y,"B",B,"budget(h=1)",round(budget,6))
print("stars per prime (first 15 smallest primes):",sorted(nstars)[:15])
print("star configurations with total big loss <= budget: %.3e"%sum(total))
for frac in [0.25,0.5,0.75]:
    print(" with loss <= %.4f: %.3e"%(budget*frac,sum(total[:int(NB*frac)])))
