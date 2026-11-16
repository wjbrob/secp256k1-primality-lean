import Secp256k1Primality.Cert09

namespace Secp256k1Primality

set_option maxRecDepth 10000
set_option exponentiation.threshold 300

theorem prime_29047611873442575647497758179 : Nat.Prime 29047611873442575647497758179 := by
  refine lucas_primality 29047611873442575647497758179 (2 : ZMod 29047611873442575647497758179) ?_ ?_
  · exact lucas_ha 2 29047611873442575647497758179 (by norm_num) (by rfl)
  · intro q hq hdvd
    have hfac : (29047611873442575647497758179 - 1) = 2 * 293 * 305873 * 545358713 * 297159362677 := by norm_num
    rw [hfac] at hdvd
    rcases (hq.dvd_mul.mp hdvd) with h4 | d4
    rcases (hq.dvd_mul.mp h4) with h3 | d3
    rcases (hq.dvd_mul.mp h3) with h2 | d2
    rcases (hq.dvd_mul.mp h2) with h1 | d1
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1]
      exact lucas_hq 2 29047611873442575647497758179 2 29047611873442575647497758178 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d1]
      exact lucas_hq 2 29047611873442575647497758179 293 6256662822391641148461841119 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d2]
      exact lucas_hq 2 29047611873442575647497758179 305873 15515419077790409984750505041 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq prime_545358713).mp d3]
      exact lucas_hq 2 29047611873442575647497758179 545358713 1548700731856248688196814844 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq prime_297159362677).mp d4]
      exact lucas_hq 2 29047611873442575647497758179 297159362677 16062460713643416818883781819 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
end Secp256k1Primality
