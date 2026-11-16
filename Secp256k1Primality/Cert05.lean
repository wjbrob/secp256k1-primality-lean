import Secp256k1Primality.Cert04

namespace Secp256k1Primality

set_option maxRecDepth 10000
set_option exponentiation.threshold 300

theorem prime_107361793816595537 : Nat.Prime 107361793816595537 := by
  refine lucas_primality 107361793816595537 (3 : ZMod 107361793816595537) ?_ ?_
  · exact lucas_ha 3 107361793816595537 (by norm_num) (by rfl)
  · intro q hq hdvd
    have hfac : (107361793816595537 - 1) = 2 * 2 * 2 * 2 * 16699 * 85831 * 4681609 := by norm_num
    rw [hfac] at hdvd
    rcases (hq.dvd_mul.mp hdvd) with h6 | d6
    rcases (hq.dvd_mul.mp h6) with h5 | d5
    rcases (hq.dvd_mul.mp h5) with h4 | d4
    rcases (hq.dvd_mul.mp h4) with h3 | d3
    rcases (hq.dvd_mul.mp h3) with h2 | d2
    rcases (hq.dvd_mul.mp h2) with h1 | d1
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1]
      exact lucas_hq 3 107361793816595537 2 107361793816595536 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d1]
      exact lucas_hq 3 107361793816595537 2 107361793816595536 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d2]
      exact lucas_hq 3 107361793816595537 2 107361793816595536 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d3]
      exact lucas_hq 3 107361793816595537 2 107361793816595536 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d4]
      exact lucas_hq 3 107361793816595537 16699 5951470030516601 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d5]
      exact lucas_hq 3 107361793816595537 85831 43062364984479349 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d6]
      exact lucas_hq 3 107361793816595537 4681609 38869239624772579 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
end Secp256k1Primality
