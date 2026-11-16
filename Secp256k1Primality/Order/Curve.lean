/-
  Secp256k1Primality.Order.Curve -- secp256k1 as a Mathlib Weierstrass curve, plus the
  INVERSE-FREE step lemmas an addition-chain certificate is checked with.

  Mathlib's affine group law (`WeierstrassCurve.Affine.Point`) computes slopes by division in
  `ZMod P`, whose inverse the kernel cannot reduce at 256 bits. Each lemma below instead takes
  a claimed slope `l` and checks it with natural-number congruences mod `P` (the kernel reduces
  `Nat` `*`, `+`, `%` on literals natively), then transports the result into Mathlib's group
  through `ZMod.natCast_eq_natCast_iff'` and Mathlib's own addition lemmas
  (`Point.add_of_X_ne`, `Point.add_self_of_Y_ne`, `Point.add_of_Y_eq`). The certificate
  (Cert.lean, generated) is then a list of such checks; nothing here assumes the curve order.

  Generated certificate: `Order/Cert.lean`, produced by `scripts/gen_order_cert.py`.
-/
import Mathlib
import Secp256k1Primality.Cert15

namespace Secp256k1Primality.Order

open WeierstrassCurve.Affine

/-- secp256k1 base-field prime `p = 2^256 - 2^32 - 977`. -/
def P : ℕ := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

theorem P_prime : Nat.Prime P :=
  prime_115792089237316195423570985008687907853269984665640564039457584007908834671663

instance : Fact (Nat.Prime P) := ⟨P_prime⟩

/-- secp256k1 group order `n`. -/
def N : ℕ := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

theorem N_prime : Nat.Prime N :=
  prime_115792089237316195423570985008687907852837564279074904382605163141518161494337

instance : Fact (Nat.Prime N) := ⟨N_prime⟩

/-- secp256k1: `y^2 = x^3 + 7` over `F_p`. -/
def secpCurve : WeierstrassCurve (ZMod P) := ⟨0, 0, 0, 0, 7⟩

/-- The affine model carrying Mathlib's group law. -/
abbrev W : WeierstrassCurve.Affine (ZMod P) := secpCurve.toAffine

/-- Generator x-coordinate (SEC 2). -/
def Gx : ZMod P := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798

/-- Generator y-coordinate (SEC 2). -/
def Gy : ZMod P := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

theorem W_a1 : W.a₁ = 0 := rfl
theorem W_a2 : W.a₂ = 0 := rfl
theorem W_a3 : W.a₃ = 0 := rfl
theorem W_a4 : W.a₄ = 0 := rfl
theorem W_a6 : W.a₆ = 7 := rfl

theorem natEq {a b : ℕ} (h : a % P = b % P) : (a : ZMod P) = (b : ZMod P) :=
  (ZMod.natCast_eq_natCast_iff' a b P).mpr h

theorem nat_ne {a b : ℕ} (h : a % P ≠ b % P) : (a : ZMod P) ≠ (b : ZMod P) :=
  fun e => h ((ZMod.natCast_eq_natCast_iff' a b P).mp e)

/-- The discriminant `Δ = -16 (4·0 + 27·7²) = -21168` is nonzero mod `p`. -/
theorem W_Δ_ne_zero : W.Δ ≠ 0 := by
  have : W.Δ = -((21168 : ℕ) : ZMod P) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, W_a1, W_a2, W_a3, W_a4, W_a6]
    push_cast; ring
  rw [this, neg_ne_zero, ← Nat.cast_zero]
  exact nat_ne (by decide)

/-- A point is on the curve (hence nonsingular, as `Δ ≠ 0`) if `y² ≡ x³ + 7 (mod p)`. -/
theorem ns {x y : ℕ} (h : (y * y) % P = (x * x * x + 7) % P) :
    W.Nonsingular (x : ZMod P) (y : ZMod P) := by
  rw [← equation_iff_nonsingular_of_Δ_ne_zero W_Δ_ne_zero, equation_iff]
  simp only [W_a1, W_a2, W_a3, W_a4, W_a6]
  have := natEq h
  push_cast at this
  linear_combination this

/-- Two points with the same coordinates are equal (whatever the nonsingularity proofs). -/
theorem some_congr {x x' y y' : ZMod P} {h : W.Nonsingular x y} {h' : W.Nonsingular x' y'}
    (hx : x = x') (hy : y = y') : Point.some h = Point.some h' := by
  subst hx; subst hy; rfl

/-- **Addition step** (`x₁ ≠ x₂`) with certified slope `l`: `l (x₁ - x₂) = y₁ - y₂`,
`x₃ = l² - x₁ - x₂`, `y₃ = l (x₁ - x₃) - y₁`, all as congruences mod `p`. -/
theorem add_step {x₁ y₁ x₂ y₂ x₃ y₃ l : ℕ} {h₁ : W.Nonsingular (x₁ : ZMod P) y₁}
    {h₂ : W.Nonsingular (x₂ : ZMod P) y₂} (h₃ : W.Nonsingular (x₃ : ZMod P) y₃)
    (hx : x₁ % P ≠ x₂ % P)
    (hl : (l * x₁ + y₂) % P = (l * x₂ + y₁) % P)
    (hX : (l * l) % P = (x₁ + x₂ + x₃) % P)
    (hY : (l * x₁) % P = (l * x₃ + y₁ + y₃) % P) :
    Point.some h₁ + Point.some h₂ = Point.some h₃ := by
  have hx' := nat_ne hx
  rw [Point.add_of_X_ne hx']
  have hsub : (x₁ : ZMod P) - x₂ ≠ 0 := sub_ne_zero.mpr hx'
  have hl' := natEq hl
  have hX' := natEq hX
  have hY' := natEq hY
  push_cast at hl' hX' hY'
  have hs : W.slope (x₁ : ZMod P) x₂ y₁ y₂ = l := by
    rw [slope_of_X_ne hx', div_eq_iff hsub]
    linear_combination hl'.symm
  congr 1
  · simp only [hs, addX, W_a1, W_a2]
    linear_combination hX'
  · simp only [hs, addY, negY, negAddY, addX, W_a1, W_a2, W_a3]
    linear_combination hY' - (l : ZMod P) * hX'

/-- **Doubling step** with certified tangent slope `l`: `l · 2y₁ = 3x₁²` (and `2y₁ ≠ 0`). -/
theorem dbl_step {x₁ y₁ x₃ y₃ l : ℕ} {h₁ : W.Nonsingular (x₁ : ZMod P) y₁}
    (h₃ : W.Nonsingular (x₃ : ZMod P) y₃)
    (hy : (y₁ + y₁) % P ≠ 0 % P)
    (hl : (l * (y₁ + y₁)) % P = (3 * x₁ * x₁) % P)
    (hX : (l * l) % P = (x₁ + x₁ + x₃) % P)
    (hY : (l * x₁) % P = (l * x₃ + y₁ + y₃) % P) :
    Point.some h₁ + Point.some h₁ = Point.some h₃ := by
  have hy2 := nat_ne hy
  push_cast at hy2
  have hyn : (y₁ : ZMod P) ≠ W.negY x₁ y₁ := by
    simp only [negY, W_a1, W_a3]
    intro e
    apply hy2
    linear_combination e
  rw [Point.add_self_of_Y_ne hyn]
  have hden : (y₁ : ZMod P) - W.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hyn
  have hl' := natEq hl
  have hX' := natEq hX
  have hY' := natEq hY
  push_cast at hl' hX' hY'
  have hs : W.slope (x₁ : ZMod P) x₁ y₁ y₁ = l := by
    rw [slope_of_Y_ne rfl hyn, div_eq_iff hden]
    simp only [negY, W_a1, W_a2, W_a3, W_a4]
    linear_combination -hl'
  congr 1
  · simp only [hs, addX, W_a1, W_a2]
    linear_combination hX'
  · simp only [hs, addY, negY, negAddY, addX, W_a1, W_a2, W_a3]
    linear_combination hY' - (l : ZMod P) * hX'

/-- **Cancellation step**: `x₁ = x₂`, `y₁ = -y₂` gives `P₁ + P₂ = 0`. -/
theorem neg_step {x₁ y₁ x₂ y₂ : ℕ} {h₁ : W.Nonsingular (x₁ : ZMod P) y₁}
    {h₂ : W.Nonsingular (x₂ : ZMod P) y₂}
    (hx : x₁ % P = x₂ % P) (hy : (y₁ + y₂) % P = 0 % P) :
    Point.some h₁ + Point.some h₂ = 0 := by
  have hx' := natEq hx
  have hy' := natEq hy
  push_cast at hy'
  exact Point.add_of_Y_eq hx' (by simp only [negY, W_a1, W_a3]; linear_combination hy')

/-- Scalar bookkeeping for an addition chain. -/
theorem chain {A B C G : W.Point} {a b c : ℕ} (hA : A = a • G) (hB : B = b • G)
    (h : A + B = C) (hc : a + b = c) : C = c • G := by
  rw [← h, hA, hB, ← add_nsmul, hc]

end Secp256k1Primality.Order
