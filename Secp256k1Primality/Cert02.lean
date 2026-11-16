import Secp256k1Primality.Cert01

namespace Secp256k1Primality

set_option maxRecDepth 10000
set_option exponentiation.threshold 300

theorem prime_107590001 : Nat.Prime 107590001 := by
  refine lucas_primality 107590001 (3 : ZMod 107590001) ?_ ?_
  · exact lucas_ha 3 107590001 (by norm_num) (by rfl)
  · intro q hq hdvd
    have hfac : (107590001 - 1) = 2 * 2 * 2 * 2 * 5 * 5 * 5 * 5 * 7 * 29 * 53 := by norm_num
    rw [hfac] at hdvd
    rcases (hq.dvd_mul.mp hdvd) with h10 | d10
    rcases (hq.dvd_mul.mp h10) with h9 | d9
    rcases (hq.dvd_mul.mp h9) with h8 | d8
    rcases (hq.dvd_mul.mp h8) with h7 | d7
    rcases (hq.dvd_mul.mp h7) with h6 | d6
    rcases (hq.dvd_mul.mp h6) with h5 | d5
    rcases (hq.dvd_mul.mp h5) with h4 | d4
    rcases (hq.dvd_mul.mp h4) with h3 | d3
    rcases (hq.dvd_mul.mp h3) with h2 | d2
    rcases (hq.dvd_mul.mp h2) with h1 | d1
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1]
      exact lucas_hq 3 107590001 2 107590000 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d1]
      exact lucas_hq 3 107590001 2 107590000 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d2]
      exact lucas_hq 3 107590001 2 107590000 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d3]
      exact lucas_hq 3 107590001 2 107590000 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d4]
      exact lucas_hq 3 107590001 5 67174630 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d5]
      exact lucas_hq 3 107590001 5 67174630 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d6]
      exact lucas_hq 3 107590001 5 67174630 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d7]
      exact lucas_hq 3 107590001 5 67174630 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d8]
      exact lucas_hq 3 107590001 7 37492364 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d9]
      exact lucas_hq 3 107590001 29 32711690 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d10]
      exact lucas_hq 3 107590001 53 15240736 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
end Secp256k1Primality
