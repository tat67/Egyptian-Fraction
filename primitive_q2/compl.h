// compl.h -- exact completion of a core by h "huge" elements (all > Y).
// Given delta = a/b (lowest terms, b's factorization known), find every set H of h integers,
// all > Y, with sum_{x in H} 1/x = a/b, such that no element of H is a multiple of a core element
// and H is primitive.  (Prime powers need no test: a verified solution cannot contain one.)
#pragma once
#include <bits/stdc++.h>
#include "gmpz.h"
typedef std::vector<std::pair<Z,int>> Fac;

struct Completer {
  std::vector<unsigned long long> core;         // core elements
  unsigned long long Y = 0;
  unsigned long long halfEntries = 0, omegaSum = 0, fastCalls = 0, slowCalls = 0, prefilterTested = 0, prefilterRejected = 0; long long nSol = 0; unsigned long long calls = 0, pairsTried = 0, n1Tried = 0, unresolved = 0;
  std::vector<std::string> sols;
  std::function<void(const std::string&)> onSolution;

  bool admissible(const Z& n, const std::vector<Z>& chosen) const {
    for (auto c : core) if (divisibleU(n, c)) return false;
    for (const Z& c : chosen) if (divisible(n, c) || divisible(c, n)) return false;
    return true;
  }
  void verify(const std::vector<Z>& H) {
    std::vector<Z> T; for (auto n : core) T.push_back(Z(n)); for (auto& h : H) T.push_back(h);
    Z num(0), den(1);
    for (auto& n : T) { num = num * n + den; den = den * n; Z g = gcd(num, den); num = divexact(num, g); den = divexact(den, g); }
    bool ok = cmp(num, den) == 0;
    for (size_t i = 0; i < T.size(); i++) for (size_t j = 0; j < T.size(); j++) if (i != j && divisible(T[j], T[i])) ok = false;
    for (auto& t : T) if (cmpu(t, 2) < 0) ok = false;
    nSol++;
    std::string s = "SOLUTION |T|=" + std::to_string(T.size()) + " exact_sum_1_and_primitive=" + std::to_string((int)ok) + " :";
    for (auto n : core) s += " " + std::to_string(n);
    for (auto& h : H) s += " " + h.str();
    sols.push_back(s); if (onSolution) onSolution(s);
  }
  // all x<y, x > lowerExcl, with 1/x + 1/y = a/b.  Parametrization: g = gcd(x,y), x = g x', y = g y',
  // gcd(x',y') = 1, x'y' | b, a | x'+y', g = (b/(x'y'))(x'+y')/a.  Meet in the middle on x'/y' mod a.
  // all x<y, x > lowerExcl, with 1/x + 1/y = a/b.  g = gcd(x,y), x = g x', y = g y', gcd(x',y') = 1,
  // x'y' | b, a | x'+y', g = r (x'+y')/a with r = b/(x'y').  For each prime power p^e of b the
  // placement is (v_p(x'), v_p(y')) in {(f,0), (0,f)}, 0 <= f <= e; p then has exponent f + (e-f) = e
  // ... in x when placed in x' or r, etc.  Sound pruning: x and y must not be multiples of a core
  // element, so two primes on the same side may not form (with the exponents present) a multiple of a
  // core element.  The "anchor" primes (<= 13) are placed first; the rest by meet in the middle on
  // x'/y' (mod a), filtered by the anchor placement.
  void twoTerm(const Z& a, const Z& b, const Fac& bf0, const Z& lowerExcl, std::vector<Z>& chosen) {
    Fac bf = bf0;
    std::stable_sort(bf.begin(), bf.end(), [](const std::pair<Z,int>& x, const std::pair<Z,int>& y) {
      bool ax = cmpu(x.first, 13) <= 0, ay = cmpu(y.first, 13) <= 0; return ax > ay; });
    int m = bf.size(), na = 0; while (na < m && cmpu(bf[na].first, 13) <= 0) na++;
    std::vector<unsigned long long> pv(m, 0); for (int i = 0; i < m; i++) if (bf[i].first.fitsU64()) pv[i] = bf[i].first.u64v();
    auto conflict = [&](int i, int ei, int j, int ej) {   // some core element p_i^s p_j^t, 1<=s<=ei, 1<=t<=ej
      if (!pv[i] || !pv[j]) return false;
      unsigned long long x = pv[i];
      for (int s1 = 1; s1 <= ei && x <= Y; s1++, x *= pv[i]) { unsigned long long y = pv[j];
        for (int s2 = 1; s2 <= ej && x * y <= Y; s2++, y *= pv[j]) if (coreSet.count(x * y)) return true; }
      return false;
    };
    // option o for prime i: 0..2e ; returns (exponent in x, exponent in y, fx, fy)
    auto optExp = [&](int i, int o, int& inX, int& inY, int& fx, int& fy) {
      int e = bf[i].second; fx = 0; fy = 0; if (o >= 1 && o <= e) fx = o; else if (o > e) fy = o - e;
      int rp = e - fx - fy; inX = fx + rp; inY = fy + rp; };
    bool aOne = cmpu(a, 1) == 0;
    auto inv = [&](const Z& v) { Z r; if (!__gmpz_invert(r.v, v.v, a.v)) { fprintf(stderr, "noninvertible mod a\n"); exit(6); } return r; };
    std::vector<int> ax(m, 0), ay(m, 0);   // current exponents in x, y (for conflict tests)
    struct Ent { Z x, y; std::vector<signed char> ex, ey; };
    std::function<void(int, Z, Z)> anchors = [&](int i, Z xa, Z ya) {
      if (i < na) {
        for (int o = 0; o <= 2 * bf[i].second; o++) {
          int inX, inY, fx, fy; optExp(i, o, inX, inY, fx, fy);
          bool ok = true;
          for (int j = 0; j < i && ok; j++) { if (inX && ax[j] && conflict(i, inX, j, ax[j])) ok = false; if (inY && ay[j] && conflict(i, inY, j, ay[j])) ok = false; }
          if (!ok) continue;
          ax[i] = inX; ay[i] = inY; Z nx = xa, ny = ya; for (int t = 0; t < fx; t++) nx = nx * bf[i].first; for (int t = 0; t < fy; t++) ny = ny * bf[i].first;
          anchors(i + 1, nx, ny); ax[i] = 0; ay[i] = 0;
        }
        return;
      }
      // meet in the middle over the non-anchor primes [na, m)
      int mid = na + (m - na) / 2;
      auto enumHalf = [&](int lo, int hi, std::vector<Ent>& out) {
        out.clear(); std::vector<signed char> ex(m, 0), ey(m, 0);
        std::function<void(int, Z, Z)> rec = [&](int k, Z xv, Z yv) {
          if (k == hi) { Ent e; e.x = xv; e.y = yv; e.ex.assign(ex.begin() + lo, ex.begin() + hi); e.ey.assign(ey.begin() + lo, ey.begin() + hi); out.push_back(e); return; }
          for (int o = 0; o <= 2 * bf[k].second; o++) {
            int inX, inY, fx, fy; optExp(k, o, inX, inY, fx, fy);
            bool ok = true;
            for (int j = 0; j < na && ok; j++) { if (inX && ax[j] && conflict(k, inX, j, ax[j])) ok = false; if (inY && ay[j] && conflict(k, inY, j, ay[j])) ok = false; }
            for (int j = lo; j < k && ok; j++) { if (inX && ex[j] && conflict(k, inX, j, ex[j])) ok = false; if (inY && ey[j] && conflict(k, inY, j, ey[j])) ok = false; }
            if (!ok) continue;
            ex[k] = inX; ey[k] = inY; Z nx = xv, ny = yv; for (int t = 0; t < fx; t++) nx = nx * bf[k].first; for (int t = 0; t < fy; t++) ny = ny * bf[k].first;
            rec(k + 1, nx, ny); ex[k] = 0; ey[k] = 0;
          }
        };
        rec(lo, Z(1), Z(1));
      };
      std::vector<Ent> L1, L2; enumHalf(na, mid, L1); enumHalf(mid, m, L2); halfEntries += L1.size() + L2.size(); omegaSum += m;
      std::unordered_map<std::string, std::vector<int>> idx;
      if (!aOne) for (int t = 0; t < (int)L1.size(); t++) idx[mod(xa * L1[t].x * inv(ya * L1[t].y), a).str()].push_back(t);
      std::vector<int> all; if (aOne) { all.resize(L1.size()); std::iota(all.begin(), all.end(), 0); }
      for (auto& q2 : L2) {
        const std::vector<int>* cand = &all;
        if (!aOne) { Z k = mod(a - mod(q2.y * inv(q2.x), a), a); auto it = idx.find(k.str()); if (it == idx.end()) continue; cand = &it->second; }
        for (int t : *cand) {
          pairsTried++;
          bool ok = true;
          for (int u = na; u < mid && ok; u++) for (int v = mid; v < m && ok; v++) {
            int uX = L1[t].ex[u - na], uY = L1[t].ey[u - na], vX = q2.ex[v - mid], vY = q2.ey[v - mid];
            if (uX && vX && conflict(u, uX, v, vX)) ok = false;
            if (uY && vY && conflict(u, uY, v, vY)) ok = false;
          }
          if (!ok) continue;
          Z xp = xa * L1[t].x * q2.x, yp = ya * L1[t].y * q2.y;
          if (cmp(xp, yp) >= 0) continue;
          Z s = xp + yp; if (!divisible(s, a)) continue;
          Z g = divexact(divexact(b, xp * yp) * s, a);
          Z x = g * xp, y = g * yp;
          if (cmp(x, lowerExcl) <= 0) continue;
          if (!admissible(x, chosen)) continue; chosen.push_back(x);
          if (admissible(y, chosen)) { chosen.push_back(y); verify(chosen); chosen.pop_back(); }
          chosen.pop_back();
        }
      }
    };
    if (useFast) { if (twoTermFast(a, b, bf, lowerExcl, chosen, pv, na)) { fastCalls++; return; } }
    slowCalls++;
    anchors(0, Z(1), Z(1));
  }
  // 128-bit version of the same enumeration (identical candidates); returns false if not applicable.
  bool useFast = true;
  static unsigned long long mulmod(unsigned long long x, unsigned long long y, unsigned long long m) { return (unsigned long long)((unsigned __int128)x * y % m); }
  static unsigned long long invmod64(unsigned long long v, unsigned long long m) { __int128 t = 0, nt = 1, r = m, nr = v % m;
    while (nr) { __int128 q = r / nr, tmp = t - q * nt; t = nt; nt = tmp; tmp = r - q * nr; r = nr; nr = tmp; }
    if (r != 1) return 0; if (t < 0) t += m; return (unsigned long long)t; }
  // 128-bit modular helpers (m < 2^125)
  static unsigned __int128 mulmod128(unsigned __int128 x, unsigned __int128 y, unsigned __int128 m) {
    if ((x >> 62) == 0 && (y >> 62) == 0 && (m >> 124) == 0) return (x * y) % m;
    unsigned __int128 r = 0; x %= m; y %= m;
    while (y) { if (y & 1) { r += x; if (r >= m) r -= m; } x += x; if (x >= m) x -= m; y >>= 1; }
    return r;
  }
  static unsigned __int128 invmod128(unsigned __int128 v, unsigned __int128 m) {
    // extended Euclid with nonnegative bookkeeping (coefficients reduced mod m)
    unsigned __int128 r0 = m, r1 = v % m, t0 = 0, t1 = 1;
    while (r1) { unsigned __int128 q = r0 / r1, r2 = r0 - q * r1; unsigned __int128 t2 = (t0 + m - mulmod128(q % m, t1, m)) % m; r0 = r1; r1 = r2; t0 = t1; t1 = t2; }
    if (r0 != 1) return 0; return t0;
  }
  bool twoTermFast(const Z& a, const Z& b, const Fac& bf, const Z& lowerExcl, std::vector<Z>& chosen, const std::vector<unsigned long long>& pv, int na) {
    typedef unsigned __int128 u128;
    Z lim(1); for (int i = 0; i < 5; i++) lim = lim * (1UL << 25);          // 2^125
    if (cmp(a, lim) >= 0 || cmp(b, lim) >= 0) return false;
    auto fromZ = [](const Z& z) { u128 r = 0; Z t = z; u128 sh = 1; while (t.sgn() > 0) { unsigned long long lo = modU(t, 1UL << 32); r += sh * lo; sh <<= 32; Z q; __gmpz_fdiv_q_2exp(q.v, t.v, 32); t = q; } return r; };
    u128 am = fromZ(a);
    int m = bf.size(); std::vector<u128> pz(m); for (int i = 0; i < m; i++) { if (!bf[i].first.fitsU64()) return false; pz[i] = bf[i].first.u64v(); }
    bool aOne = (am == 1);
    std::vector<std::vector<u128>> powP(m), powPinv(m);
    if (!aOne) for (int i = 0; i < m; i++) { int e = bf[i].second; powP[i].assign(e + 1, 1); powPinv[i].assign(e + 1, 1);
      u128 pr = pz[i] % am, pi = invmod128(pr, am); if (pi == 0) return false;
      for (int f = 1; f <= e; f++) { powP[i][f] = mulmod128(powP[i][f - 1], pr, am); powPinv[i][f] = mulmod128(powPinv[i][f - 1], pi, am); } }
    // conflict table: ct[i][j][ei][ej] for exponents up to the exponents in b
    int emax = 1; for (auto& pe : bf) emax = std::max(emax, pe.second);
    int E1 = emax + 1;
    std::vector<char> ct((size_t)m * m * E1 * E1, 0);
    if (coreMark.size() != Y + 1) { coreMark.assign(Y + 1, 0); }
    for (auto c : core) if (c <= Y) coreMark[c] = 1;
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (i != j && pv[i] && pv[j] && pv[i] <= Y && pv[j] <= Y)
      for (int ei = 1; ei <= bf[i].second; ei++) for (int ej = 1; ej <= bf[j].second; ej++) {
        bool c = false; unsigned long long x = pv[i];
        for (int s1 = 1; s1 <= ei && x <= Y && !c; s1++, x *= pv[i]) { unsigned long long y = pv[j];
          for (int s2 = 1; s2 <= ej && x * y <= Y; s2++, y *= pv[j]) if (coreMark[x * y]) { c = true; break; } }
        ct[(((size_t)i * m + j) * E1 + ei) * E1 + ej] = c;
      }
    for (auto c : core) if (c <= Y) coreMark[c] = 0;
    auto conflict = [&](int i, int ei, int j, int ej) { return ct[(((size_t)i * m + j) * E1 + ei) * E1 + ej] != 0; };
    auto optExp = [&](int i, int o, int& inX, int& inY, int& fx, int& fy) {
      int e = bf[i].second; fx = 0; fy = 0; if (o >= 1 && o <= e) fx = o; else if (o > e) fy = o - e;
      int rp = e - fx - fy; inX = fx + rp; inY = fy + rp; };
    std::vector<int> ax(m, 0), ay(m, 0);
    std::function<void(int, u128, u128)> anchorsF = [&](int i, u128 xa, u128 ya) {
      if (i < na) {
        for (int o = 0; o <= 2 * bf[i].second; o++) {
          int inX, inY, fx, fy; optExp(i, o, inX, inY, fx, fy); bool ok = true;
          for (int j = 0; j < i && ok; j++) { if (inX && ax[j] && conflict(i, inX, j, ax[j])) ok = false; if (inY && ay[j] && conflict(i, inY, j, ay[j])) ok = false; }
          if (!ok) continue;
          ax[i] = inX; ay[i] = inY; u128 nx = xa, ny = ya; for (int t = 0; t < fx; t++) nx *= pz[i]; for (int t = 0; t < fy; t++) ny *= pz[i];
          anchorsF(i + 1, nx, ny); ax[i] = 0; ay[i] = 0;
        }
        return;
      }
      int mid = na + (m - na) / 2;
      // keys: half 1 carries k1 = x-part * (y-part)^{-1}; half 2 carries k2 = (x-part)^{-1} * y-part.
      // x' + y' == 0 (mod a)  <=>  (xa x1)(ya y1)^{-1} == -(y2 x2^{-1})  <=>  ka * k1 == -k2   (mod a)
      auto enumHalf = [&](int lo, int hi, bool second, std::vector<u128>& X, std::vector<u128>& Yv, std::vector<u128>& K, std::vector<signed char>& EX, std::vector<signed char>& EY) {
        X.clear(); Yv.clear(); K.clear(); EX.clear(); EY.clear(); std::vector<signed char> ex(m, 0), ey(m, 0);
        std::function<void(int, u128, u128, u128)> rec = [&](int k, u128 xv, u128 yv, u128 key) {
          if (k == hi) { X.push_back(xv); Yv.push_back(yv); K.push_back(key); for (int t = lo; t < hi; t++) { EX.push_back(ex[t]); EY.push_back(ey[t]); } return; }
          for (int o = 0; o <= 2 * bf[k].second; o++) {
            int inX, inY, fx, fy; optExp(k, o, inX, inY, fx, fy); bool ok = true;
            for (int j = 0; j < na && ok; j++) { if (inX && ax[j] && conflict(k, inX, j, ax[j])) ok = false; if (inY && ay[j] && conflict(k, inY, j, ay[j])) ok = false; }
            for (int j = lo; j < k && ok; j++) { if (inX && ex[j] && conflict(k, inX, j, ex[j])) ok = false; if (inY && ey[j] && conflict(k, inY, j, ey[j])) ok = false; }
            if (!ok) continue;
            ex[k] = inX; ey[k] = inY; u128 nx = xv, ny = yv; for (int t = 0; t < fx; t++) nx *= pz[k]; for (int t = 0; t < fy; t++) ny *= pz[k];
            u128 nk = key;
            if (!aOne) { // multiply by p^{fx} p^{-fy} (half 1) or p^{-fx} p^{fy} (half 2)
              int ePos = second ? fy : fx, eNeg = second ? fx : fy;
              if (ePos) nk = mulmod128(nk, powP[k][ePos], am);
              if (eNeg) nk = mulmod128(nk, powPinv[k][eNeg], am);
            }
            rec(k + 1, nx, ny, nk); ex[k] = 0; ey[k] = 0;
          }
        };
        rec(lo, 1, 1, 1);
      };
      std::vector<u128> X1, Y1, K1, X2, Y2, K2; std::vector<signed char> EX1, EY1, EX2, EY2;
      enumHalf(na, mid, false, X1, Y1, K1, EX1, EY1); enumHalf(mid, m, true, X2, Y2, K2, EX2, EY2);
      int w1 = mid - na, w2 = m - mid;
      halfEntries += X1.size() + X2.size(); omegaSum += m;
      std::vector<std::pair<u128,int>> keys1;
      if (!aOne) { u128 ka = mulmod128(xa % am, invmod128(ya % am, am), am);
        keys1.reserve(X1.size()); for (size_t t = 0; t < X1.size(); t++) keys1.push_back({mulmod128(ka, K1[t], am), (int)t});
        std::sort(keys1.begin(), keys1.end()); }
      for (size_t q = 0; q < X2.size(); q++) {
        size_t lo = 0, hi = X1.size();
        if (!aOne) { u128 k = (am - K2[q] % am) % am;
          auto it = std::lower_bound(keys1.begin(), keys1.end(), std::make_pair(k, -1));
          lo = it - keys1.begin(); hi = lo; while (hi < keys1.size() && keys1[hi].first == k) hi++; }
        for (size_t z = lo; z < hi; z++) {
          int t = aOne ? (int)z : keys1[z].second;
          pairsTried++;
          bool ok = true;
          for (int u = 0; u < w1 && ok; u++) for (int v = 0; v < w2 && ok; v++) {
            int uX = EX1[(size_t)t * w1 + u], uY = EY1[(size_t)t * w1 + u], vX = EX2[q * w2 + v], vY = EY2[q * w2 + v];
            if (uX && vX && conflict(na + u, uX, mid + v, vX)) ok = false;
            if (uY && vY && conflict(na + u, uY, mid + v, vY)) ok = false;
          }
          if (!ok) continue;
          auto toZ = [](u128 v) { Z r(0); Z sh(1); while (v) { unsigned long long lo2 = (unsigned long long)(v & 0xffffffffULL); r = r + sh * Z(lo2); sh = sh * (1UL << 32); v >>= 32; } return r; };
          Z xp = toZ(xa * X1[t]) * toZ(X2[q]), yp = toZ(ya * Y1[t]) * toZ(Y2[q]);
          if (cmp(xp, yp) >= 0) continue;
          Z s = xp + yp; if (!divisible(s, a)) continue;
          Z g = divexact(divexact(b, xp * yp) * s, a);
          Z x = g * xp, y = g * yp;
          if (cmp(x, lowerExcl) <= 0) continue;
          if (!admissible(x, chosen)) continue; chosen.push_back(x);
          if (admissible(y, chosen)) { chosen.push_back(y); verify(chosen); chosen.pop_back(); }
          chosen.pop_back();
        }
      }
    };
    anchorsF(0, 1, 1);
    return true;
  }
  static const std::vector<unsigned>& smallPrimes() {
    static std::vector<unsigned> P; if (!P.empty()) return P;
    const unsigned L = 2000000; std::vector<char> c(L + 1, 0);
    for (unsigned i = 2; i <= L; i++) if (!c[i]) { P.push_back(i); for (unsigned long long j = (unsigned long long)i * i; j <= L; j += i) c[j] = 1; }
    return P;
  }
  static Fac combine(const Fac& bf, const Z& n, const Z& newb) {
    std::vector<Z> ps; for (auto& pe : bf) ps.push_back(pe.first);
    if (n.fitsU64() && n.u64v() < 4000000000000ULL) {      // trial division by primes <= 2*10^6
      unsigned long long m = n.u64v();
      for (unsigned p : smallPrimes()) { if ((unsigned long long)p * p > m) break; if (m % p == 0) { ps.push_back(Z(p)); while (m % p == 0) m /= p; } }
      if (m > 1) ps.push_back(Z(m));
    } else {
      Z m = n;
      for (unsigned long p = 2; cmpu(m, 1) > 0; p++) {
        if (cmpu(m, p * p) < 0) { ps.push_back(m); break; }
        if (divisibleU(m, p)) { ps.push_back(Z(p)); while (divisibleU(m, p)) { Z t; __gmpz_divexact_ui(t.v, m.v, p); m = t; } }
      }
    }
    std::sort(ps.begin(), ps.end(), [](const Z& x, const Z& y) { return cmp(x, y) < 0; });
    Fac r; Z rest = newb;
    for (size_t i = 0; i < ps.size(); i++) { if (i && cmp(ps[i], ps[i - 1]) == 0) continue; int e = 0; while (divisible(rest, ps[i])) { rest = divexact(rest, ps[i]); e++; } if (e) r.push_back({ps[i], e}); }
    if (cmpu(rest, 1) != 0) { fprintf(stderr, "combine: factorization failed\n"); exit(7); }
    return r;
  }
  // Can the prime powers of bf be distributed over h elements so that no element is divisible by a
  // core element?  Necessary condition (pairwise test: p^ep q^eq divisible by a core element using both).
  std::set<unsigned long long> coreSet; std::vector<char> coreMark;
  bool colorable(const Fac& bf, int h) {
    std::vector<std::pair<unsigned long long,int>> ps;
    for (auto& pe : bf) if (pe.first.fitsU64() && pe.first.u64v() <= Y) ps.push_back({pe.first.u64v(), pe.second});
    int n = ps.size(); if (n <= h) return true;
    std::vector<std::vector<char>> adj(n, std::vector<char>(n, 0));
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) {
      unsigned long long p = ps[i].first, q = ps[j].first; bool c = false;
      unsigned long long x = p; for (int a = 1; a <= ps[i].second && x <= Y && !c; a++, x *= p) { unsigned long long y = q; for (int b2 = 1; b2 <= ps[j].second && x * y <= Y; b2++, y *= q) if (coreSet.count(x * y)) { c = true; break; } }
      adj[i][j] = adj[j][i] = c;
    }
    std::vector<int> col(n, -1);
    std::function<bool(int)> rec = [&](int i) { if (i == n) return true;
      for (int c = 0; c < h; c++) { bool ok = true; for (int j = 0; j < i; j++) if (adj[i][j] && col[j] == c) { ok = false; break; } if (!ok) continue; col[i] = c; if (rec(i + 1)) return true; col[i] = -1; }
      return false; };
    return rec(0);
  }
  // h terms, all > lowerExcl
  void run(const Z& a, const Z& b, const Fac& bf, int h, const Z& lowerExcl, std::vector<Z>& chosen) {
    calls++;
    if (h == 1) { if (divisible(b, a)) { Z n = divexact(b, a); if (cmp(n, lowerExcl) > 0 && admissible(n, chosen)) { chosen.push_back(n); verify(chosen); chosen.pop_back(); } } return; }
    if (h == 2) { twoTerm(a, b, bf, lowerExcl, chosen); return; }
    Z lo = fdiv(b, a); if (cmp(lo, lowerExcl) < 0) lo = lowerExcl; Z hi = fdiv(b * (unsigned long)h, a);
    if (hi.fitsU64() && lo.fitsU64()) {
      // fast path: 64-bit candidates
      unsigned long long l = lo.u64v() + 1, hh = hi.u64v();
      std::vector<unsigned long long> ch64; bool allSmall = true; for (auto& c : chosen) { if (!c.fitsU64()) allSmall = false; else ch64.push_back(c.u64v()); }
      // primes of b (with exponents) as u64 where possible, for the certain-denominator pre-filter
      std::vector<std::pair<unsigned long long,int>> bpr; bool bAllSmall = true;
      for (auto& pe : bf) { if (pe.first.fitsU64()) bpr.push_back({pe.first.u64v(), pe.second}); else bAllSmall = false; }
      for (unsigned long long nn = l; nn <= hh; nn++) {
        n1Tried++;
        bool bad = false; for (auto c : core) if (nn % c == 0) { bad = true; break; } if (bad) continue;
        if (allSmall) { for (auto c : ch64) if (nn % c == 0) { bad = true; break; } if (bad) continue; }
        if (bAllSmall && nn < 4000000000000ULL) {
          // Sound pre-filter: primes certainly in the new denominator are those of b not dividing n
          // (p | b, p !| n => p !| a n - b) and those of n not dividing b; they must be coverable by h-1
          // elements, none a multiple of a core element.
          Fac certain; unsigned long long m2 = nn;
          std::vector<unsigned long long> np;
          for (unsigned p : smallPrimes()) { if ((unsigned long long)p * p > m2) break; if (m2 % p == 0) { int e = 0; while (m2 % p == 0) { m2 /= p; e++; } np.push_back(p); bool inB = false; for (auto& q : bpr) if (q.first == p) inB = true; if (!inB) certain.push_back({Z(p), e}); } }
          if (m2 > 1) { np.push_back(m2); bool inB = false; for (auto& q : bpr) if (q.first == m2) inB = true; if (!inB) certain.push_back({Z(m2), 1}); }
          for (auto& q : bpr) { bool dn = false; for (auto x : np) if (x == q.first) dn = true; if (!dn) certain.push_back({Z(q.first), q.second}); }
          prefilterTested++;
          if (!colorable(certain, h - 1)) { prefilterRejected++; continue; }
        }
        Z n(nn); if (!allSmall && !admissible(n, chosen)) continue;
        Z na = a * n - b, nb = b * n; Z g = gcd(na, nb); na = divexact(na, g); nb = divexact(nb, g);
        Fac nf = combine(bf, n, nb);
        if (!colorable(nf, h - 1)) continue;
        chosen.push_back(n); run(na, nb, nf, h - 1, n, chosen); chosen.pop_back();
      }
      return;
    }
    for (Z n = lo + Z(1); cmp(n, hi) <= 0; n = n + Z(1)) {
      n1Tried++;
      if (!admissible(n, chosen)) continue;
      Z na = a * n - b, nb = b * n; Z g = gcd(na, nb); na = divexact(na, g); nb = divexact(nb, g);
      Fac nf = combine(bf, n, nb);
      if (!colorable(nf, h - 1)) continue;
      chosen.push_back(n); run(na, nb, nf, h - 1, n, chosen); chosen.pop_back();
    }
  }
};
