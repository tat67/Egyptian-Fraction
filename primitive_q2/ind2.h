// ind2.h -- independent exact solver for 1/x + 1/y = a/b (x < y), used by complete2 / complete3.
// Shares no code with compl.h.  All arithmetic is exact (unsigned 128-bit where it provably fits,
// GMP otherwise).
//
//   Every solution has b/a < x <= 2b/a and y = bx/(ax-b).  Equivalently d = ax - b is a divisor of b^2
//   with 0 < d < b and d = -b (mod a), and then x = (b+d)/a, y = (b + b^2/d)/a.
//   AP  : test every integer x in (max(b/a, L), 2b/a]                       (cost ~ b/a)
//   DIV : enumerate the divisors d of b^2 in the class -b mod a by meet in the middle (cost ~ tau(b^2)^(1/2))
#pragma once
#include <bits/stdc++.h>
#include "gmpz.h"
namespace ind2 {
typedef unsigned long long u64; typedef unsigned __int128 u128;
inline Z fromStr(const std::string& s) { Z r; __gmpz_set_str(r.v, s.c_str(), 10); return r; }
inline bool toU128(const Z& z, u128& out) {
  if (z.v->_mp_size < 0 || z.v->_mp_size > 2) return false;
  out = 0; for (int i = z.v->_mp_size - 1; i >= 0; i--) out = (out << 64) | (u128)z.v->_mp_d[i];
  return true;
}
inline Z fromU128(u128 x) { Z r((unsigned long)(u64)(x >> 64)); __gmpz_mul_2exp(r.v, r.v, 64); __gmpz_add_ui(r.v, r.v, (unsigned long)(u64)x); return r; }
struct Counters { u64 ap = 0, dv = 0, apSteps = 0, divEntries = 0; };
// all (x, y) with L < x < y and 1/x + 1/y = a/b (a, b > 0 coprime); fb = factorisation of b.
inline void solve(const Z& a, const Z& b, const std::vector<std::pair<u64,int>>& fb, const Z& L, u64 apLimit,
                  std::vector<std::pair<Z,Z>>& out, Counters& c) {
  Z lo = fdiv(b, a) + Z(1UL), hi = fdiv(b * 2UL, a);
  if (cmp(lo, L) <= 0) lo = L + Z(1UL);
  if (cmp(hi, lo) < 0) return;
  Z cnt = hi - lo + Z(1UL);
  if (cmpu(cnt, apLimit) <= 0) {
    c.ap++; u64 n = cnt.u64v(); c.apSteps += n;
    u128 A, B, X0, t; bool fast = toU128(a, A) && toU128(b, B) && toU128(lo, X0);
    if (fast) { Z top = b * hi; fast = toU128(top, t) && (t >> 126) == 0 && toU128(a * hi, t) && (t >> 126) == 0; }
    if (fast) {
      u128 x = X0, d = A * x - B, bx = B * x;
      for (u64 i = 0; i < n; i++, x++, d += A, bx += B) if (bx % d == 0) { u128 y = bx / d; if (y > x) out.push_back({fromU128(x), fromU128(y)}); }
    } else {
      Z x = lo;
      for (u64 i = 0; i < n; i++, x = x + Z(1UL)) { Z d = a * x - b, bx = b * x; if (divisible(bx, d)) { Z y = divexact(bx, d); if (cmp(y, x) > 0) out.push_back({x, y}); } }
    }
    return;
  }
  c.dv++;
  std::vector<std::pair<u64,int>> f2; for (auto& p : fb) f2.push_back({p.first, 2 * p.second});
  size_t half = f2.size() / 2;
  auto divs = [&](size_t from, size_t to) { std::vector<Z> D{Z(1UL)}; for (size_t i = from; i < to; i++) { std::vector<Z> N; for (auto& d : D) { Z pw(1UL); for (int e = 0; e <= f2[i].second; e++) { N.push_back(d * pw); pw = pw * (unsigned long)f2[i].first; } } D.swap(N); } return D; };
  std::vector<Z> D1 = divs(0, half), D2 = divs(half, f2.size()); c.divEntries += D1.size() + D2.size();
  std::unordered_map<std::string, std::vector<int>> idx; idx.reserve(D1.size() * 2);
  for (size_t i = 0; i < D1.size(); i++) idx[mod(D1[i], a).str()].push_back(i);
  Z target = mod(a - mod(b, a), a);
  for (auto& d2 : D2) {
    Z inv; if (cmpu(a, 1) == 0) inv = Z(0UL); else __gmpz_invert(inv.v, d2.v, a.v);
    Z need = (cmpu(a, 1) == 0) ? Z(0UL) : mod(target * inv, a);
    auto it = idx.find(need.str()); if (it == idx.end()) continue;
    for (int i : it->second) {
      Z d = D1[i] * d2; if (cmp(d, b) >= 0) continue;
      Z xn = b + d, yn = b + divexact(b * b, d);
      if (divisible(xn, a) && divisible(yn, a)) { Z x = divexact(xn, a), y = divexact(yn, a); if (cmp(x, L) > 0 && cmp(y, x) > 0) out.push_back({x, y}); }
    }
  }
}
// factorisation by trial division with a prime list; returns false if a cofactor > 1 remains.
inline bool factorTD(Z r, const std::vector<unsigned>& primes, std::vector<std::pair<u64,int>>& f) {
  for (unsigned p : primes) { if (cmpu(r, 1) == 0) break; if (divisibleU(r, p)) { int e = 0; while (divisibleU(r, p)) { __gmpz_divexact_ui(r.v, r.v, p); e++; } f.push_back({p, e}); } }
  return cmpu(r, 1) == 0;
}
inline u64 primeOfPower(u64 n) { for (u64 p = 2; p * p <= n; p++) if (n % p == 0) { while (n % p == 0) n /= p; return n == 1 ? p : 0; } return n; }  // p if n = p^k, else 0
inline std::vector<std::pair<u64,int>> factor64(u64 n) { std::vector<std::pair<u64,int>> f; for (u64 p = 2; p * p <= n; p++) if (n % p == 0) { int e = 0; while (n % p == 0) { n /= p; e++; } f.push_back({p, e}); } if (n > 1) f.push_back({n, 1}); return f; }
inline void sumExact(const std::vector<Z>& T, Z& num, Z& den) { num = Z(0UL); den = Z(1UL); for (auto& t : T) { num = num * t + den; den = den * t; Z g = gcd(num, den); num = divexact(num, g); den = divexact(den, g); } }
}  // namespace ind2
