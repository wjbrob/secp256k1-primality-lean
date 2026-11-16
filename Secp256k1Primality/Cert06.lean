import Secp256k1Primality.Cert05

namespace Secp256k1Primality

set_option maxRecDepth 10000
set_option exponentiation.threshold 300

theorem prime_173378833005251801 : Nat.Prime 173378833005251801 := by
  refine lucas_primality 173378833005251801 (6 : ZMod 173378833005251801) ?_ ?_
  · exact lucas_ha 6 173378833005251801 (by norm_num) (by rfl)
  · intro q hq hdvd
    have hfac : (173378833005251801 - 1) = 2 * 2 * 2 * 5 * 5 * 2621 * 24809 * 13331831 := by norm_num
    rw [hfac] at hdvd
    rcases (hq.dvd_mul.mp hdvd) with h7 | d7
    rcases (hq.dvd_mul.mp h7) with h6 | d6
    rcases (hq.dvd_mul.mp h6) with h5 | d5
    rcases (hq.dvd_mul.mp h5) with h4 | d4
    rcases (hq.dvd_mul.mp h4) with h3 | d3
    rcases (hq.dvd_mul.mp h3) with h2 | d2
    rcases (hq.dvd_mul.mp h2) with h1 | d1
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1]
      exact lucas_hq 6 173378833005251801 2 173378833005251800 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d1]
      exact lucas_hq 6 173378833005251801 2 173378833005251800 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d2]
      exact lucas_hq 6 173378833005251801 2 173378833005251800 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d3]
      exact lucas_hq 6 173378833005251801 5 152071994513768143 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d4]
      exact lucas_hq 6 173378833005251801 5 152071994513768143 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d5]
      exact lucas_hq 6 173378833005251801 2621 25743935490785551 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d6]
      exact lucas_hq 6 173378833005251801 24809 5978649957832462 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d7]
      exact lucas_hq 6 173378833005251801 13331831 17954474104786666 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
end Secp256k1Primality
