/-
Copyright (c) 2025 Will Roberts. Released under Apache 2.0 license.

# secp256k1: the field prime `p` and the group order `n` are prime

Both results are proved with Pratt (Lucas) certificates whose arithmetic is checked by the Lean kernel itself:
no `native_decide`, no `sorry`, no custom `axiom`. See `Secp256k1Primality/Core.lean` for the method.
-/
import Secp256k1Primality.Cert15

namespace Secp256k1Primality

set_option maxRecDepth 10000
set_option exponentiation.threshold 300

/-- The secp256k1 field prime, `p = 2^256 - 2^32 - 977`. -/
theorem p_eq_closed_form :
    (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F : ℕ) = 2 ^ 256 - 2 ^ 32 - 977 := by
  norm_num

/-- secp256k1 field prime p = 2^256 - 2^32 - 977 is prime (kernel-clean). -/
theorem p_prime :
    Nat.Prime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F :=
  prime_115792089237316195423570985008687907853269984665640564039457584007908834671663

/-- secp256k1 group order n is prime (kernel-clean). -/
theorem n_prime :
    Nat.Prime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 :=
  prime_115792089237316195423570985008687907852837564279074904382605163141518161494337

end Secp256k1Primality
