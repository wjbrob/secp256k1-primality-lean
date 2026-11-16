import Secp256k1Primality

/-! Run with `lake env lean scripts/AxiomCheck.lean`.
Expected output for each theorem: only `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms Secp256k1Primality.p_prime
#print axioms Secp256k1Primality.n_prime
