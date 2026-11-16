import Secp256k1Primality.Cert02

namespace Secp256k1Primality

set_option maxRecDepth 10000
set_option exponentiation.threshold 300

theorem prime_545358713 : Nat.Prime 545358713 := by
  refine lucas_primality 545358713 (5 : ZMod 545358713) ?_ ?_
  · exact lucas_ha 5 545358713 (by norm_num) (by rfl)
  · intro q hq hdvd
    have hfac : (545358713 - 1) = 2 * 2 * 2 * 41 * 59 * 28181 := by norm_num
    rw [hfac] at hdvd
    rcases (hq.dvd_mul.mp hdvd) with h5 | d5
    rcases (hq.dvd_mul.mp h5) with h4 | d4
    rcases (hq.dvd_mul.mp h4) with h3 | d3
    rcases (hq.dvd_mul.mp h3) with h2 | d2
    rcases (hq.dvd_mul.mp h2) with h1 | d1
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1]
      exact lucas_hq 5 545358713 2 545358712 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d1]
      exact lucas_hq 5 545358713 2 545358712 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d2]
      exact lucas_hq 5 545358713 2 545358712 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d3]
      exact lucas_hq 5 545358713 41 232418614 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d4]
      exact lucas_hq 5 545358713 59 256734421 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d5]
      exact lucas_hq 5 545358713 28181 453985277 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
end Secp256k1Primality
