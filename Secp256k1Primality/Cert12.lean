import Secp256k1Primality.Cert11

namespace Secp256k1Primality

set_option maxRecDepth 10000
set_option exponentiation.threshold 300

theorem prime_255515944373312847190720520512484175977 : Nat.Prime 255515944373312847190720520512484175977 := by
  refine lucas_primality 255515944373312847190720520512484175977 (3 : ZMod 255515944373312847190720520512484175977) ?_ ?_
  · exact lucas_ha 3 255515944373312847190720520512484175977 (by norm_num) (by rfl)
  · intro q hq hdvd
    have hfac : (255515944373312847190720520512484175977 - 1) = 2 * 2 * 2 * 7 * 7 * 11 * 1627 * 2657 * 4423 * 41201 * 96557 * 7240687 * 107590001 := by norm_num
    rw [hfac] at hdvd
    rcases (hq.dvd_mul.mp hdvd) with h12 | d12
    rcases (hq.dvd_mul.mp h12) with h11 | d11
    rcases (hq.dvd_mul.mp h11) with h10 | d10
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
      exact lucas_hq 3 255515944373312847190720520512484175977 2 255515944373312847190720520512484175976 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d1]
      exact lucas_hq 3 255515944373312847190720520512484175977 2 255515944373312847190720520512484175976 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d2]
      exact lucas_hq 3 255515944373312847190720520512484175977 2 255515944373312847190720520512484175976 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d3]
      exact lucas_hq 3 255515944373312847190720520512484175977 7 101630464857884484146913207008716355375 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d4]
      exact lucas_hq 3 255515944373312847190720520512484175977 7 101630464857884484146913207008716355375 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d5]
      exact lucas_hq 3 255515944373312847190720520512484175977 11 216514664320154426008163201710470464886 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d6]
      exact lucas_hq 3 255515944373312847190720520512484175977 1627 72473583126275438393254198129422586513 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d7]
      exact lucas_hq 3 255515944373312847190720520512484175977 2657 25264823290665569537380285172105507303 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d8]
      exact lucas_hq 3 255515944373312847190720520512484175977 4423 83399280779944061005050044694706920693 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d9]
      exact lucas_hq 3 255515944373312847190720520512484175977 41201 172827330636526207461984371528411705589 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d10]
      exact lucas_hq 3 255515944373312847190720520512484175977 96557 255259905881023646761568249610326048823 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d11]
      exact lucas_hq 3 255515944373312847190720520512484175977 7240687 31043399383638056505926561103262574803 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq prime_107590001).mp d12]
      exact lucas_hq 3 255515944373312847190720520512484175977 107590001 18335160587089267704563076742628378053 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
end Secp256k1Primality
