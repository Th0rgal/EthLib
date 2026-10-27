import EthLib.Cryptography.Proofs.Kzg.RecoveryCoset

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

/-- Cell-level bit reversal selects the low seven bits of the natural FFT index. -/
theorem reverseBits_cellOfRoot (j : Nat) :
    reverseBits (reverseBits j FIELD_ELEMENTS_PER_EXT_BLOB / FIELD_ELEMENTS_PER_CELL)
      CELLS_PER_EXT_BLOB = j % CELLS_PER_EXT_BLOB := by
  change reverseBits (reverseBits j (2 ^ 13) / 2 ^ 6) (2 ^ 7) = j % 2 ^ 7
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_reverseBits, Nat.testBit_mod_two_pow]
  by_cases ht : t < 7
  · rw [if_pos ht, Nat.testBit_div_two_pow, testBit_reverseBits,
      if_pos (by omega)]
    simp only [decide_eq_true ht, Bool.true_and]
    congr 1
    omega
  · rw [if_neg ht]
    simp [ht]

/-- The extended-domain generator maps to the cell-domain generator by a 64th power. -/
theorem domainRoot_extended_pow_cell :
    domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ FIELD_ELEMENTS_PER_CELL =
      domainRoot CELLS_PER_EXT_BLOB := by
  unfold domainRoot
  rw [Bls.Fr.hpow_eq_pow, Bls.Fr.hpow_eq_pow]
  have h1 : (Fr.ofNat ((BLS_MODULUS - 1) / FIELD_ELEMENTS_PER_EXT_BLOB)).val =
      (BLS_MODULUS - 1) / FIELD_ELEMENTS_PER_EXT_BLOB := by decide
  have h2 : (Fr.ofNat ((BLS_MODULUS - 1) / CELLS_PER_EXT_BLOB)).val =
      (BLS_MODULUS - 1) / CELLS_PER_EXT_BLOB := by decide
  rw [h1, h2]
  have hpow (x : Fr) (a b : Nat) : (x ^ a) ^ b = x ^ (a * b) := (pow_mul x a b).symm
  rw [hpow]
  congr 1

end EthLib.Cryptography.Kzg
