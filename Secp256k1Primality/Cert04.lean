import Secp256k1Primality.Cert03

namespace Secp256k1Primality

set_option maxRecDepth 10000
set_option exponentiation.threshold 300

theorem prime_297159362677 : Nat.Prime 297159362677 := by
  refine lucas_primality 297159362677 (2 : ZMod 297159362677) ?_ ?_
  · exact lucas_ha 2 297159362677 (by norm_num) (by rfl)
  · intro q hq hdvd
    have hfac : (297159362677 - 1) = 2 * 2 * 3 * 3 * 11 * 461 * 1627771 := by norm_num
    rw [hfac] at hdvd
    rcases (hq.dvd_mul.mp hdvd) with h6 | d6
    rcases (hq.dvd_mul.mp h6) with h5 | d5
    rcases (hq.dvd_mul.mp h5) with h4 | d4
    rcases (hq.dvd_mul.mp h4) with h3 | d3
    rcases (hq.dvd_mul.mp h3) with h2 | d2
    rcases (hq.dvd_mul.mp h2) with h1 | d1
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1]
      exact lucas_hq 2 297159362677 2 297159362676 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d1]
      exact lucas_hq 2 297159362677 2 297159362676 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d2]
      exact lucas_hq 2 297159362677 3 21378871788 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d3]
      exact lucas_hq 2 297159362677 3 21378871788 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d4]
      exact lucas_hq 2 297159362677 11 235971553533 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d5]
      exact lucas_hq 2 297159362677 461 238970074943 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d6]
      exact lucas_hq 2 297159362677 1627771 114170894341 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
end Secp256k1Primality
