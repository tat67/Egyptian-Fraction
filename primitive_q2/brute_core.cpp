// brute_core.cpp -- independent enumerator for validation.
// Lists every primitive C subset of {n in [6,Y] : n not a prime power} with |C| = j and
//   1 - h/(Y+1) <= sum_{n in C} 1/n <= 1,   h = K - j,  for every j with 0 <= h <= hmax.
// Plain depth-first search in increasing order of n.  Bound: sum of the r largest remaining
// reciprocals of elements not comparable to a chosen element.  Integer fixed point (2^96) with
// directed rounding; the caller re-checks every candidate with exact fractions.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned __int128 u128; typedef unsigned long long u64;
static const u128 S = (u128)1 << 96;
int K, hmax; u64 Y; vector<u64> U; vector<u128> rLow, rUp; vector<vector<int>> comp; vector<int> blk; vector<int> cur;
u64 nodes = 0, out = 0;
u128 lowTarget[64];
bool qualifies(int cnt, u128 sLow, u128 sUp) {
  int h = K - cnt; if (h < 0 || h > hmax) return false;
  if (sLow > S) return false;
  return sUp >= lowTarget[h];
}
void dfs(int i, int cnt, u128 sLow, u128 sUp) {
  nodes++;
  if (sLow > S || cnt >= K) return;
  // can any extension by elements k >= i reach a qualifying size?
  bool any = false; u128 acc = sUp; int taken = 0;
  for (int k = i; k < (int)U.size() && cnt + taken < K; k++) if (!blk[k]) {
    acc += rUp[k]; taken++;
    int h = K - (cnt + taken); if (h <= hmax && acc >= lowTarget[h]) { any = true; break; }
  }
  if (!any) return;
  for (int k = i; k < (int)U.size(); k++) if (!blk[k]) {
    for (int f : comp[k]) blk[f]++; cur.push_back(k);
    u128 nl = sLow + rLow[k], nu = sUp + rUp[k];
    if (qualifies(cnt + 1, nl, nu)) { out++; for (int x : cur) printf("%llu ", (u64)U[x]); printf("\n"); }
    dfs(k + 1, cnt + 1, nl, nu);
    cur.pop_back(); for (int f : comp[k]) blk[f]--;
  }
}
int main(int argc, char** argv) {
  K = atoi(argv[1]); Y = strtoull(argv[2], 0, 10); hmax = atoi(argv[3]);
  for (u64 n = 6; n <= Y; n++) { u64 m = n, p = 2; while (m % p) p++; while (m % p == 0) m /= p; if (m != 1) U.push_back(n); }
  int m = U.size(); comp.assign(m, {}); blk.assign(m, 0);
  for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++) if (U[b] % U[a] == 0) { comp[a].push_back(b); comp[b].push_back(a); }
  for (u64 n : U) { rLow.push_back(S / n); rUp.push_back((S + n - 1) / n); }
  for (int h = 0; h <= hmax; h++) lowTarget[h] = S - (S * (u128)h) / (Y + 1) - 1;  // slightly below the true target
  dfs(0, 0, 0, 0);
  fprintf(stderr, "brute: K=%d Y=%llu hmax=%d nodes=%llu candidates=%llu\n", K, (u64)Y, hmax, (u64)nodes, (u64)out);
}
