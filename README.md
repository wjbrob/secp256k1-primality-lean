# secp256k1 primality in Lean 4, checked by the kernel

<p>
  <a href="../../actions/workflows/ci.yml"><img src="../../actions/workflows/ci.yml/badge.svg" alt="CI"></a>
  <img src="https://img.shields.io/badge/Lean-v4.27.0-6E4AFF?style=flat-square" alt="Lean v4.27.0">
  <img src="https://img.shields.io/badge/Mathlib-v4.27.0-6E4AFF?style=flat-square" alt="Mathlib">
  <img src="https://img.shields.io/badge/axioms-propext%20%C2%B7%20choice%20%C2%B7%20Quot.sound-brightgreen?style=flat-square" alt="standard axioms only">
  <img src="https://img.shields.io/badge/license-Apache--2.0-blue?style=flat-square" alt="Apache-2.0">
</p>

Machine-checked proofs that the two numbers behind Bitcoin's elliptic curve are prime:

```lean
theorem Secp256k1Primality.p_prime :   -- field prime, p = 2^256 − 2^32 − 977
  Nat.Prime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

theorem Secp256k1Primality.n_prime :   -- order of the generator G
  Nat.Prime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
```

```text
$ lake env lean scripts/AxiomCheck.lean
'Secp256k1Primality.p_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Secp256k1Primality.n_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There's **no `native_decide`** (so no trust in the compiler), **no `sorry`** and **no custom `axiom`**. Every
multiplication and modular power in the certificate is checked by Lean's kernel.

## Why this needs any work at all

Primality of a 78-digit number is easy for a computer algebra system, but it's awkward to make the Lean
*kernel* check it:

- `decide` on `Nat.Prime` is hopeless at this size, and `native_decide` would mean trusting compiled code
  rather than the kernel.
- A **Pratt / Lucas certificate** (Mathlib's `lucas_primality`) reduces primality of `m` to
  `a^(m−1) = 1` and `a^((m−1)/q) ≠ 1` for every prime `q ∣ m − 1`. But evaluating `a ^ e` in `ZMod m` with
  the default `Monoid.npow` unfolds into roughly `e ≈ 2^256` multiplications.

The fix, in [`Core.lean`](Secp256k1Primality/Core.lean):

1. `powMod`: square-and-multiply on plain `Nat` with a **fixed fuel of 264**. The recursion is structurally
   bounded and takes about 256 squarings of numbers under 512 bits. The kernel's GMP-backed `Nat` arithmetic
   reduces it with `rfl` in seconds.
2. A bridge lemma, `zmod_pow_eq_powMod : (a : ZMod m) ^ e = ((powMod a e m : ℕ) : ZMod m)` for `e < 2^264`,
   **proved once** by induction on the fuel. After that, the kernel only ever evaluates `powMod`, never the giant power.
3. Two helpers (`lucas_ha`, `lucas_hq`) turn each Lucas obligation into a single `rfl` on `powMod`.

## The certificate tree

Proving `p` and `n` prime needs the primality of the large prime factors of `p − 1` and `n − 1`, and of *their*
factors, and so on. That gives 15 certificates, each building on the earlier ones. Small factors are closed
directly by `norm_num`.

| File | Proves prime | Digits |
|---|---|---|
| `Cert01` … `Cert09` | 44706919 … 132896956044521568488119 | 8 – 24 |
| `Cert10` | 29047611873442575647497758179 | 29 |
| `Cert11` | 341948486974166000522343609283189 | 33 |
| `Cert12` | 255515944373312847190720520512484175977 | 39 |
| `Cert13` | 205115282021455665897114700593932402728804164701536103180137503955397371 | 72 |
| `Cert14` | **n** = 115792089237316195423570985008687907852837564279074904382605163141518161494337 | 78 |
| `Cert15` | **p** = 115792089237316195423570985008687907853269984665640564039457584007908834671663 | 78 |

For example, `p − 1 = 2 · 3 · 7 · 13441 · q₇₂`, with witness `a = 3`, where `q₇₂` is the 72-digit prime from `Cert13`.

The certificate (witnesses and factorizations) was generated with SageMath. You don't have to trust Sage:
every product and every power is re-checked by the Lean kernel.

## Build

```bash
git clone https://github.com/wjbrob/secp256k1-primality-lean && cd secp256k1-primality-lean
lake exe cache get        # prebuilt Mathlib
lake build                # project itself: about 1 minute
lake env lean scripts/AxiomCheck.lean
```

## Use it in your project

```lean
-- lakefile.lean
require secp256k1_primality from git
  "https://github.com/wjbrob/secp256k1-primality-lean" @ "main"
```

```lean
import Secp256k1Primality

example : Nat.Prime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 :=
  Secp256k1Primality.n_prime
```

Typical uses are making `ZMod n` a field for secp256k1 scalars (`Fact (Nat.Prime n)`), and removing an
`axiom n_prime` from an existing formalisation of ECDSA or Schnorr.

The `powMod` bridge in `Core.lean` is general: it works for any modulus below `2^264`, so the same approach
certifies other 256-bit curve parameters (P-256, Curve25519, …) once you supply their Pratt trees.

## License

Apache-2.0, the same licence as Mathlib.
