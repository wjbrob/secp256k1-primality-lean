import Secp256k1Primality.Cert07

namespace Secp256k1Primality

set_option maxRecDepth 10000
set_option exponentiation.threshold 300

theorem prime_22149492674086928081353 : Nat.Prime 22149492674086928081353 := by
  refine lucas_primality 22149492674086928081353 (5 : ZMod 22149492674086928081353) ?_ ?_
  · exact lucas_ha 5 22149492674086928081353 (by norm_num) (by rfl)
  · intro q hq hdvd
    have hfac : (22149492674086928081353 - 1) = 2 * 2 * 2 * 3 * 5323 * 173378833005251801 := by norm_num
    rw [hfac] at hdvd
    rcases (hq.dvd_mul.mp hdvd) with h5 | d5
    rcases (hq.dvd_mul.mp h5) with h4 | d4
    rcases (hq.dvd_mul.mp h4) with h3 | d3
    rcases (hq.dvd_mul.mp h3) with h2 | d2
    rcases (hq.dvd_mul.mp h2) with h1 | d1
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1]
      exact lucas_hq 5 22149492674086928081353 2 22149492674086928081352 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d1]
      exact lucas_hq 5 22149492674086928081353 2 22149492674086928081352 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d2]
      exact lucas_hq 5 22149492674086928081353 2 22149492674086928081352 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d3]
      exact lucas_hq 5 22149492674086928081353 3 10043889752229528935999 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d4]
      exact lucas_hq 5 22149492674086928081353 5323 6446620476143922066636 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq prime_173378833005251801).mp d5]
      exact lucas_hq 5 22149492674086928081353 173378833005251801 317195385910872261254 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
end Secp256k1Primality
