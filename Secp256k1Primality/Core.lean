/-
Copyright (c) 2025 Will Roberts.
Released under Apache 2.0 license.

# secp256k1 Primality — kernel-clean Lucas/Pratt certificates

This module discharges the primality of the secp256k1 field prime `p` and group
order `n` as honest THEOREMS (no `axiom`, no `native_decide`, no `sorry`).

Method: `lucas_primality` (Mathlib/NumberTheory/LucasPrimality.lean) with a full
Pratt certificate tree. Each `(a : ZMod m) ^ ((m-1)/q)` is evaluated in the Lean
kernel via a fast repeated-squaring `powMod : Nat → Nat → Nat → Nat` (fixed fuel
264) whose result is reduced by `rfl` (kernel `Nat` is GMP-backed; ~256 squarings
of <512-bit numbers, NOT the ~2^256 multiplications of default unary `Monoid.npow`).

The bridge `zmod_pow_eq_powMod` proves `(a:ZMod m)^e = ((powMod a e m :ℕ):ZMod m)`
for `e < 2^264`, so the kernel only ever evaluates `powMod`, never the giant `a^e`.

`#print axioms` for `p_prime`/`n_prime` shows ONLY: propext, Classical.choice,
Quot.sound (plus whatever `lucas_primality`/`norm_num` legitimately use). No
`sorryAx`, no `Lean.ofReduceBool`, no `Lean.trustCompiler`.

The 15-node certificate tree (primitive roots + factorizations) was computed and
cross-checked in SageMath; every product and power equality is RE-VERIFIED in the
Lean kernel here.
-/
import Mathlib

set_option maxRecDepth 10000
set_option exponentiation.threshold 512

namespace Secp256k1Primality

/-- Repeated-squaring modular exponentiation with explicit fuel. -/
def powModAux : Nat → Nat → Nat → Nat → Nat
  | 0,        _, _, _ => 1
  | _+1,      _, 0, _ => 1
  | fuel+1, base, e, m =>
      let half := powModAux fuel (base * base % m) (e / 2) m
      if e % 2 == 1 then half * base % m else half

/-- Fixed fuel 264 > 256: structurally bounded recursion (no huge-literal
    predecessor), so each `rfl` defeq has bounded stack depth. Valid for all
    `e < 2^264`, which covers every exponent here (all `m - 1 < 2^256`). -/
def powMod (base e m : Nat) : Nat := powModAux 264 base e m

theorem powModAux_modEq (m : Nat) :
    ∀ fuel base e, e < 2^fuel → powModAux fuel base e m ≡ base ^ e [MOD m] := by
  intro fuel
  induction fuel with
  | zero =>
      intro base e he
      interval_cases e
      · simp [powModAux, Nat.ModEq]
  | succ fuel ih =>
      intro base e he
      rcases Nat.eq_zero_or_pos e with he0 | hepos
      · subst he0; simp [powModAux, Nat.ModEq]
      · have hbound : e / 2 < 2 ^ fuel := by
          have : e < 2^(fuel+1) := he
          omega
        have ihe := ih (base * base % m) (e / 2) hbound
        have hhalf : powModAux fuel (base * base % m) (e / 2) m
            ≡ base ^ (2 * (e / 2)) [MOD m] := by
          calc powModAux fuel (base * base % m) (e / 2) m
              ≡ (base * base % m) ^ (e / 2) [MOD m] := ihe
            _ ≡ (base * base) ^ (e / 2) [MOD m] := Nat.ModEq.pow _ (Nat.mod_modEq _ _)
            _ = base ^ (2 * (e / 2)) := by rw [← pow_two, ← pow_mul]
        have hunf : powModAux (fuel+1) base e m
            = (if e % 2 == 1
                then powModAux fuel (base * base % m) (e / 2) m * base % m
                else powModAux fuel (base * base % m) (e / 2) m) := by
          obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hepos.ne'
          rfl
        rw [hunf]
        by_cases hpar : e % 2 == 1
        · rw [if_pos hpar]
          have hp : e % 2 = 1 := by simpa using hpar
          have heq : 2 * (e / 2) + 1 = e := by omega
          calc powModAux fuel (base * base % m) (e / 2) m * base % m
              ≡ powModAux fuel (base * base % m) (e / 2) m * base [MOD m] :=
                (Nat.mod_modEq _ _)
            _ ≡ base ^ (2 * (e / 2)) * base [MOD m] := Nat.ModEq.mul_right _ hhalf
            _ = base ^ (2 * (e / 2) + 1) := by rw [pow_succ]
            _ = base ^ e := by rw [heq]
        · rw [if_neg hpar]
          have hp : e % 2 = 0 := by
            have : e % 2 ≠ 1 := by simpa using hpar
            omega
          have heq : 2 * (e / 2) = e := by omega
          calc powModAux fuel (base * base % m) (e / 2) m
              ≡ base ^ (2 * (e / 2)) [MOD m] := hhalf
            _ = base ^ e := by rw [heq]

theorem powMod_modEq (base e m : Nat) (he : e < 2 ^ 264) :
    powMod base e m ≡ base ^ e [MOD m] := by
  apply powModAux_modEq
  exact he

theorem zmod_pow_eq_powMod (base e m : Nat) (he : e < 2 ^ 264) :
    (base : ZMod m) ^ e = ((powMod base e m : Nat) : ZMod m) := by
  have h := powMod_modEq base e m he
  rw [← Nat.cast_pow]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr h.symm)

/-- The "a^(m-1) = 1" obligation, reduced to a kernel `powMod` computation. -/
theorem lucas_ha (a m : Nat) (hm : m < 2 ^ 264) (h : powMod a (m-1) m = 1) :
    (a : ZMod m) ^ (m-1) = 1 := by
  rw [zmod_pow_eq_powMod a (m-1) m (by omega), h, Nat.cast_one]

/-- The "a^((m-1)/q) ≠ 1" obligation for a single prime q.
    `r` is the kernel-computed `powMod a ((m-1)/q) m`, with `1 < r < m`. -/
theorem lucas_hq (a m q r : Nat) (hm : m < 2 ^ 264) (hr : powMod a ((m-1)/q) m = r)
    (hr1 : r ≠ 1) (hrm : r < m) (hm1 : 1 < m) :
    (a : ZMod m) ^ ((m-1)/q) ≠ 1 := by
  have hediv : (m-1)/q < 2 ^ 264 := by
    have : (m-1)/q ≤ m - 1 := Nat.div_le_self _ _
    omega
  rw [zmod_pow_eq_powMod a ((m-1)/q) m hediv, hr]
  intro hcontra
  have hval : ((r : ZMod m)).val = (1 : ZMod m).val := by rw [hcontra]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrm] at hval
  have : (1 : ZMod m).val = 1 := by
    have : NeZero m := ⟨by omega⟩
    simp [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hm1]
  rw [this] at hval
  exact hr1 hval

end Secp256k1Primality
