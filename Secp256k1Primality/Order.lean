/-
  Secp256k1Primality.Order -- **the secp256k1 generator has order n**, kernel-checked.

  `addOrderOf G = N` on Mathlib's secp256k1 `WeierstrassCurve.Affine.Point` group, from:
  * `G_nonsingular` -- G is on `y^2 = x^3 + 7` (checked mod p; Δ = -21168 ≠ 0);
  * `cert_nsmul_eq_zero` -- the generated addition-chain certificate (Secp256k1Order/Cert.lean,
    445 inverse-free steps) showing `N • G = 0`;
  * `N_prime` (the Lucas/Pratt certificate of this package) + Mathlib's `addOrderOf_eq_prime`.
  Axioms: propext, Classical.choice, Quot.sound only (kernel-checked, no compiled evaluation).
-/
import Secp256k1Primality.Order.Cert

namespace Secp256k1Primality.Order

open WeierstrassCurve.Affine

theorem Gx_cast :
    ((0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798 : ℕ) : ZMod P) = Gx := by
  unfold Gx; exact Nat.cast_ofNat

theorem Gy_cast :
    ((0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8 : ℕ) : ZMod P) = Gy := by
  unfold Gy; exact Nat.cast_ofNat

/-- The SEC 2 generator lies on secp256k1. -/
theorem G_nonsingular : W.Nonsingular Gx Gy := by
  rw [← Gx_cast, ← Gy_cast]; exact G_nonsingular_nat

/-- The secp256k1 generator as a point of Mathlib's group. -/
def G : W.Point := Point.some G_nonsingular

theorem G_eq_cert : G = Point.some G_nonsingular_nat := some_congr Gx_cast.symm Gy_cast.symm

theorem G_ne_zero : G ≠ 0 := by
  unfold G; exact Point.some_ne_zero G_nonsingular

/-- `n • G = 0`. -/
theorem nsmul_N_G : N • G = 0 := by
  rw [G_eq_cert]; exact cert_nsmul_eq_zero

/-- **The secp256k1 generator has order exactly `n`.** -/
theorem addOrderOf_G : addOrderOf G = N :=
  addOrderOf_eq_prime nsmul_N_G G_ne_zero

end Secp256k1Primality.Order
