import Lake
open Lake DSL

package secp256k1_primality where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «Secp256k1Primality» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.27.0"
