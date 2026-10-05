// Minimal C++ binding to the GMP shared library (libgmp.so.10), declared by hand because the
// development headers are not installed.  Only integer (mpz) functions are used.
#pragma once
#include <string>
#include <cstdlib>
extern "C" {
typedef unsigned long mp_limb_t;
typedef struct { int _mp_alloc; int _mp_size; mp_limb_t* _mp_d; } __mpz_struct;
typedef __mpz_struct mpz_t[1];
typedef const __mpz_struct* mpz_srcptr;
typedef __mpz_struct* mpz_ptr;
void __gmpz_init(mpz_ptr); void __gmpz_clear(mpz_ptr);
void __gmpz_set(mpz_ptr, mpz_srcptr); void __gmpz_set_ui(mpz_ptr, unsigned long);
int __gmpz_set_str(mpz_ptr, const char*, int); char* __gmpz_get_str(char*, int, mpz_srcptr);
void __gmpz_add(mpz_ptr, mpz_srcptr, mpz_srcptr); void __gmpz_add_ui(mpz_ptr, mpz_srcptr, unsigned long);
void __gmpz_sub(mpz_ptr, mpz_srcptr, mpz_srcptr); void __gmpz_sub_ui(mpz_ptr, mpz_srcptr, unsigned long);
void __gmpz_mul(mpz_ptr, mpz_srcptr, mpz_srcptr); void __gmpz_mul_ui(mpz_ptr, mpz_srcptr, unsigned long);
void __gmpz_fdiv_q(mpz_ptr, mpz_srcptr, mpz_srcptr); void __gmpz_tdiv_r(mpz_ptr, mpz_srcptr, mpz_srcptr);
void __gmpz_tdiv_qr(mpz_ptr, mpz_ptr, mpz_srcptr, mpz_srcptr);
void __gmpz_gcd(mpz_ptr, mpz_srcptr, mpz_srcptr); void __gmpz_lcm(mpz_ptr, mpz_srcptr, mpz_srcptr);
int __gmpz_cmp(mpz_srcptr, mpz_srcptr); int __gmpz_cmp_ui(mpz_srcptr, unsigned long);
int __gmpz_divisible_p(mpz_srcptr, mpz_srcptr); int __gmpz_divisible_ui_p(mpz_srcptr, unsigned long);
void __gmpz_divexact(mpz_ptr, mpz_srcptr, mpz_srcptr); void __gmpz_divexact_ui(mpz_ptr, mpz_srcptr, unsigned long);
unsigned long __gmpz_get_ui(mpz_srcptr); int __gmpz_fits_ulong_p(mpz_srcptr);
unsigned long __gmpz_fdiv_ui(mpz_srcptr, unsigned long);
void __gmpz_mul_2exp(mpz_ptr, mpz_srcptr, unsigned long); void __gmpz_fdiv_q_2exp(mpz_ptr, mpz_srcptr, unsigned long);
void __gmpz_pow_ui(mpz_ptr, mpz_srcptr, unsigned long);
int __gmpz_invert(mpz_ptr, mpz_srcptr, mpz_srcptr);
}
typedef unsigned long long u64_t;
struct Z {
  mpz_t v;
  Z() { __gmpz_init(v); }
  Z(unsigned long x) { __gmpz_init(v); __gmpz_set_ui(v, x); }
  Z(const Z& o) { __gmpz_init(v); __gmpz_set(v, o.v); }
  Z& operator=(const Z& o) { if (this != &o) __gmpz_set(v, o.v); return *this; }
  Z& operator=(unsigned long x) { __gmpz_set_ui(v, x); return *this; }
  ~Z() { __gmpz_clear(v); }
  int sgn() const { return v->_mp_size < 0 ? -1 : (v->_mp_size > 0); }
  bool fitsU64() const { return __gmpz_fits_ulong_p(v); }
  u64_t u64v() const { return (u64_t)__gmpz_get_ui(v); }
  std::string str() const { char* s = __gmpz_get_str(nullptr, 10, v); std::string r(s); free(s); return r; }
};
inline Z operator+(const Z& a, const Z& b) { Z r; __gmpz_add(r.v, a.v, b.v); return r; }
inline Z operator-(const Z& a, const Z& b) { Z r; __gmpz_sub(r.v, a.v, b.v); return r; }
inline Z operator*(const Z& a, const Z& b) { Z r; __gmpz_mul(r.v, a.v, b.v); return r; }
inline Z operator*(const Z& a, unsigned long b) { Z r; __gmpz_mul_ui(r.v, a.v, b); return r; }
inline Z fdiv(const Z& a, const Z& b) { Z r; __gmpz_fdiv_q(r.v, a.v, b.v); return r; }
inline Z mod(const Z& a, const Z& b) { Z r; __gmpz_tdiv_r(r.v, a.v, b.v); return r; }
inline Z gcd(const Z& a, const Z& b) { Z r; __gmpz_gcd(r.v, a.v, b.v); return r; }
inline Z divexact(const Z& a, const Z& b) { Z r; __gmpz_divexact(r.v, a.v, b.v); return r; }
inline int cmp(const Z& a, const Z& b) { return __gmpz_cmp(a.v, b.v); }
inline int cmpu(const Z& a, unsigned long b) { return __gmpz_cmp_ui(a.v, b); }
inline bool divisible(const Z& a, const Z& b) { return __gmpz_divisible_p(a.v, b.v); }
inline bool divisibleU(const Z& a, unsigned long b) { return __gmpz_divisible_ui_p(a.v, b); }
inline unsigned long modU(const Z& a, unsigned long m) { return __gmpz_fdiv_ui(a.v, m); }
