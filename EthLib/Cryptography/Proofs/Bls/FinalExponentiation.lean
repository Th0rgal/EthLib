import EthLib.Cryptography.Proofs.Bls.Fp12
import EthLib.Cryptography.Bls.Pairing
import Mathlib.FieldTheory.Finite.Basic

/-!
# The target subgroup of final exponentiation

The concrete extension tower has p^12 elements.
Fermat's theorem therefore places every nonzero final-exponentiation
output in the r-th roots of unity.
This result does not assert that a Miller-loop output is nonzero or that
Miller evaluation is a bilinear pairing.
-/
namespace EthLib.Cryptography.Bls

set_option maxRecDepth 4000

private def fp2Equiv : Fp2 ≃ Fp × Fp where
  toFun a := (a.c0, a.c1)
  invFun a := ⟨a.1, a.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

private def fp6Equiv : Fp6 ≃ Fp2 × Fp2 × Fp2 where
  toFun a := (a.c0, a.c1, a.c2)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨a,b,c⟩; rfl

private def fp12Equiv : Fp12 ≃ Fp6 × Fp6 where
  toFun a := (a.c0, a.c1)
  invFun a := ⟨a.1, a.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

noncomputable instance : Fintype Fp2 := Fintype.ofEquiv (Fp × Fp) fp2Equiv.symm
noncomputable instance : Fintype Fp6 := Fintype.ofEquiv (Fp2 × Fp2 × Fp2) fp6Equiv.symm
noncomputable instance : Fintype Fp12 := Fintype.ofEquiv (Fp6 × Fp6) fp12Equiv.symm

theorem card_fp2 : Fintype.card Fp2 = Fp.modulus ^ 2 := by
  rw [Fintype.card_congr fp2Equiv, Fintype.card_prod]
  rw [show Fintype.card Fp = Fp.modulus from Fintype.card_fin _]
  exact (pow_two _).symm

theorem card_fp6 : Fintype.card Fp6 = Fp.modulus ^ 6 := by
  rw [Fintype.card_congr fp6Equiv, Fintype.card_prod, Fintype.card_prod, card_fp2]
  ring

theorem card_fp12 : Fintype.card Fp12 = Fp.modulus ^ 12 := by
  rw [Fintype.card_congr fp12Equiv, Fintype.card_prod, card_fp6]
  ring

/-- The scalar modulus divides the nonzero extension-field order. -/
theorem scalar_modulus_dvd_extension_order : Fr.modulus ∣ Fp.modulus ^ 12 - 1 := by
  decide +kernel

/-- The exponent uses exact integer division. -/
theorem finalExpExponent_mul_modulus :
    finalExpExponent * Fr.modulus = Fp.modulus ^ 12 - 1 :=
  Nat.div_mul_cancel scalar_modulus_dvd_extension_order

/-- Nonzero inputs map into the r-th roots of unity. -/
theorem finalExponentiation_pow_modulus {f : Fp12} (hf : f ≠ 0) :
    finalExponentiation f ^ Fr.modulus = 1 := by
  rw [finalExponentiation, Fp12.powNat_eq_pow, ← pow_mul, finalExpExponent_mul_modulus]
  simpa only [card_fp12] using FiniteField.pow_card_sub_one_eq_one f hf

/-- Final exponentiation preserves multiplication. -/
theorem finalExponentiation_mul (a b : Fp12) :
    finalExponentiation (a * b) = finalExponentiation a * finalExponentiation b := by
  simp only [finalExponentiation, Fp12.powNat_eq_pow, mul_pow]

/-- Final exponentiation cannot turn a nonzero input into zero. -/
theorem finalExponentiation_ne_zero {f : Fp12} (hf : f ≠ 0) :
    finalExponentiation f ≠ 0 := by
  rw [finalExponentiation, Fp12.powNat_eq_pow]
  exact pow_ne_zero _ hf

end EthLib.Cryptography.Bls
