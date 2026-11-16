import Secp256k1Primality.Cert08

namespace Secp256k1Primality

set_option maxRecDepth 10000
set_option exponentiation.threshold 300

theorem prime_132896956044521568488119 : Nat.Prime 132896956044521568488119 := by
  refine lucas_primality 132896956044521568488119 (6 : ZMod 132896956044521568488119) ?_ ?_
  · exact lucas_ha 6 132896956044521568488119 (by norm_num) (by rfl)
  · intro q hq hdvd
    have hfac : (132896956044521568488119 - 1) = 2 * 3 * 22149492674086928081353 := by norm_num
    rw [hfac] at hdvd
    rcases (hq.dvd_mul.mp hdvd) with h2 | d2
    rcases (hq.dvd_mul.mp h2) with h1 | d1
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1]
      exact lucas_hq 6 132896956044521568488119 2 132896956044521568488118 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp d1]
      exact lucas_hq 6 132896956044521568488119 3 76725380987433565404982 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hq prime_22149492674086928081353).mp d2]
      exact lucas_hq 6 132896956044521568488119 22149492674086928081353 46656 (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
end Secp256k1Primality
