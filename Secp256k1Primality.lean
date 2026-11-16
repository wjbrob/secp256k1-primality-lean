/-
Copyright (c) 2025 Will Roberts. Released under Apache 2.0 license.

# secp256k1: the field prime `p` and the group order `n` are prime, and `G` has order `n`

`p_prime` and `n_prime` are proved with Pratt (Lucas) certificates; `Order.addOrderOf_G` adds the
curve-level result that the SEC 2 generator has order exactly `n`, via a 445-step addition-chain
certificate. All arithmetic is checked by the Lean kernel itself: no `native_decide`, no `sorry`,
no custom `axiom`. See `Secp256k1Primality/Core.lean` and `Secp256k1Primality/Order/Curve.lean`
for the two methods.
-/
import Secp256k1Primality.Order

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

/-- `Fact (Nat.Prime p)`, so `ZMod p` is a field. -/
instance fact_p_prime :
    Fact (Nat.Prime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) :=
  ⟨p_prime⟩

/-- `Fact (Nat.Prime n)`, so `ZMod n` is a field (secp256k1 scalars). -/
instance fact_n_prime :
    Fact (Nat.Prime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141) :=
  ⟨n_prime⟩

/-- **The secp256k1 generator `G` has order exactly `n`** (re-exported from `Order`). -/
theorem addOrderOf_G : addOrderOf Order.G = Order.N := Order.addOrderOf_G

end Secp256k1Primality
