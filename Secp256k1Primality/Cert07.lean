import Secp256k1Primality.Cert06

namespace Secp256k1Primality

set_option maxRecDepth 10000
set_option exponentiation.threshold 300

theorem prime_174723607534414371449 : Nat.Prime 174723607534414371449 := by
  refine lucas_primality 174723607534414371449 (3 : ZMod 174723607534414371449) ?_ ?_
  · exact lucas_ha 3 174723607534414371449 (by norm_num) (by rfl)
  · intro q hq hdvd
    have hfac : (174723607534414371449 - 1) = 2 * 2 * 2 * 17 * 59 * 4051 * 120233 * 44706919 := by norm_num
    rw [hfac] at hdvd
    rcases (hq.dvd_mul.mp hdvd) with h7 | d7
    rcases (hq.dvd_mul.mp h7) with h6 | d6
    rcases (hq.dvd_mul.mp h6) with h5 | d5
    rcases (hq.dvd_mul.mp h5) with h4 | d4
    rcases (hq.dvd_mul.mp h4) with h3 | d3
    rcases (hq.dvd_mul.mp h3) with h2 | d2
    rcases (hq.dvd_mul.mp h2) with h1 | d1
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1]
      exact lucas_hq 3 174723607534414371449 2 174723607534414371448 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d1]
      exact lucas_hq 3 174723607534414371449 2 174723607534414371448 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d2]
      exact lucas_hq 3 174723607534414371449 2 174723607534414371448 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d3]
      exact lucas_hq 3 174723607534414371449 17 143977312736193201955 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d4]
      exact lucas_hq 3 174723607534414371449 59 101275312590739994117 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d5]
      exact lucas_hq 3 174723607534414371449 4051 117775491988442121468 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d6]
      exact lucas_hq 3 174723607534414371449 120233 143725591556162883674 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d7]
      exact lucas_hq 3 174723607534414371449 44706919 72059039805266995621 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
end Secp256k1Primality
