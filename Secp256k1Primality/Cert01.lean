import Secp256k1Primality.Core

namespace Secp256k1Primality

set_option maxRecDepth 10000
set_option exponentiation.threshold 300

theorem prime_44706919 : Nat.Prime 44706919 := by
  refine lucas_primality 44706919 (6 : ZMod 44706919) ?_ ?_
  · exact lucas_ha 6 44706919 (by norm_num) (by rfl)
  · intro q hq hdvd
    have hfac : (44706919 - 1) = 2 * 3 * 797 * 9349 := by norm_num
    rw [hfac] at hdvd
    rcases (hq.dvd_mul.mp hdvd) with h3 | d3
    rcases (hq.dvd_mul.mp h3) with h2 | d2
    rcases (hq.dvd_mul.mp h2) with h1 | d1
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1]
      exact lucas_hq 6 44706919 2 44706918 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d1]
      exact lucas_hq 6 44706919 3 30500379 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d2]
      exact lucas_hq 6 44706919 797 41156332 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d3]
      exact lucas_hq 6 44706919 9349 6711465 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
end Secp256k1Primality
