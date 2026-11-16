import Secp256k1Primality.Cert10

namespace Secp256k1Primality

set_option maxRecDepth 10000
set_option exponentiation.threshold 300

theorem prime_341948486974166000522343609283189 : Nat.Prime 341948486974166000522343609283189 := by
  refine lucas_primality 341948486974166000522343609283189 (2 : ZMod 341948486974166000522343609283189) ?_ ?_
  · exact lucas_ha 2 341948486974166000522343609283189 (by norm_num) (by rfl)
  · intro q hq hdvd
    have hfac : (341948486974166000522343609283189 - 1) = 2 * 2 * 3 * 3 * 3 * 109 * 29047611873442575647497758179 := by norm_num
    rw [hfac] at hdvd
    rcases (hq.dvd_mul.mp hdvd) with h6 | d6
    rcases (hq.dvd_mul.mp h6) with h5 | d5
    rcases (hq.dvd_mul.mp h5) with h4 | d4
    rcases (hq.dvd_mul.mp h4) with h3 | d3
    rcases (hq.dvd_mul.mp h3) with h2 | d2
    rcases (hq.dvd_mul.mp h2) with h1 | d1
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1]
      exact lucas_hq 2 341948486974166000522343609283189 2 341948486974166000522343609283188 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d1]
      exact lucas_hq 2 341948486974166000522343609283189 2 341948486974166000522343609283188 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d2]
      exact lucas_hq 2 341948486974166000522343609283189 3 165002932037550746596172898062794 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d3]
      exact lucas_hq 2 341948486974166000522343609283189 3 165002932037550746596172898062794 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d4]
      exact lucas_hq 2 341948486974166000522343609283189 3 165002932037550746596172898062794 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d5]
      exact lucas_hq 2 341948486974166000522343609283189 109 153618737808983370202320649387857 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq prime_29047611873442575647497758179).mp d6]
      exact lucas_hq 2 341948486974166000522343609283189 29047611873442575647497758179 291782875431971620014836968593543 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
end Secp256k1Primality
