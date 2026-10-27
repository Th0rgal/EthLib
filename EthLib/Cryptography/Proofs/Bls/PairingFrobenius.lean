import EthLib.Cryptography.Proofs.Bls.PairingDenominator

/-!
# Concrete quadratic Frobenius and the negative BLS parameter

Conjugation in the final quadratic tower is the p^6-power Frobenius.
After final exponentiation it is inversion, as required by negative x.
-/
namespace EthLib.Cryptography.Bls
namespace PairingTower

private theorem v_ne_zero : (Fp6.v : Fp6) ≠ 0 := by
  intro h
  have hc := congrArg Fp6.c1 h
  exact one_ne_zero hc

/-- The tower generator v cannot be a square in Fp6, since w is outside
Fp6 and is a square root of v in the already-proved Fp12 field. -/
theorem v_not_square : ¬IsSquare (Fp6.v : Fp6) := by
  rintro ⟨a, ha⟩
  have hs : (fp6ToFp12 a) ^ 2 = w ^ 2 := by
    rw [w_squared, ← map_pow, pow_two, ← ha]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · have hc := congrArg Fp12.c1 h
    exact zero_ne_one hc
  · have hc := congrArg Fp12.c1 h
    change (0 : Fp6) = -1 at hc
    exact (neg_ne_zero.mpr one_ne_zero) hc.symm

private theorem fp6_char_ne_two : ringChar Fp6 ≠ 2 := by
  let f : ZMod Fp.modulus →+* Fp6 := fp2ToFp6.comp fpToFp2
  letI : CharP Fp6 Fp.modulus := charP_of_injective_ringHom f.injective Fp.modulus
  rw [ringChar.eq Fp6 Fp.modulus]
  decide

/-- Euler's criterion identifies the nontrivial quadratic Frobenius sign. -/
theorem v_pow_half_card : Fp6.v ^ (Fp.modulus ^ 6 / 2) = -1 := by
  have hn : Fp6.v ^ (Fp.modulus ^ 6 / 2) ≠ 1 := by
    intro h
    apply v_not_square
    apply (FiniteField.isSquare_iff fp6_char_ne_two v_ne_zero).mpr
    simpa only [card_fp6] using h
  have hs : (Fp6.v ^ (Fp.modulus ^ 6 / 2)) ^ 2 = (1 : Fp6) ^ 2 := by
    rw [← pow_mul, show Fp.modulus ^ 6 / 2 * 2 = Fp.modulus ^ 6 - 1 by decide, one_pow]
    simpa only [card_fp6] using FiniteField.pow_card_sub_one_eq_one Fp6.v v_ne_zero
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hs).resolve_left hn

theorem w_pow_fp6_card : w ^ (Fp.modulus ^ 6) = -w := by
  rw [show Fp.modulus ^ 6 = 2 * (Fp.modulus ^ 6 / 2) + 1 by decide,
    pow_succ, pow_mul, w_squared, ← map_pow, v_pow_half_card, map_neg, map_one, neg_one_mul]

/-- The exact implementation's conjugation equals the sixth Frobenius. -/
theorem pow_fp6_card_eq_conjugate (a : Fp12) : a ^ (Fp.modulus ^ 6) = a.conjugate := by
  letI : Algebra Fp6 Fp12 := fp6ToFp12.toAlgebra
  let φ := FiniteField.frobeniusAlgHom Fp6 Fp12
  have hf (b : Fp6) : φ (fp6ToFp12 b) = fp6ToFp12 b := φ.commutes b
  have hw : φ w = -w := by
    change w ^ Fintype.card Fp6 = -w
    rw [card_fp6, w_pow_fp6_card]
  have hd : a = fp6ToFp12 a.c0 + fp6ToFp12 a.c1 * w := by
    apply Fp12.ext <;> simp [fp6ToFp12, w, Fp6.mulByV_eq]
  have hpow : a ^ Fintype.card Fp6 = φ a := by rfl
  rw [← card_fp6, hpow]
  conv_lhs => rw [hd, map_add, map_mul, hf, hf, hw]
  apply Fp12.ext <;> simp [fp6ToFp12, w, Fp6.mulByV_eq]

end PairingTower
open PairingTower

/-- Conjugation after the final exponent is inversion, with nonzero input
proved separately for every concrete valid Miller loop. -/
theorem finalExponentiation_conjugate {a : Fp12} (ha : a ≠ 0) :
    finalExponentiation a.conjugate = (finalExponentiation a)⁻¹ := by
  have hc : a.conjugate ≠ 0 := fun h => ha (conjugation.injective (h.trans (map_zero _).symm))
  have hfix : (a * a.conjugate).conjugate = a * a.conjugate := by
    rw [Fp12.conjugate_mul, Fp12.conjugate_conjugate, mul_comm]
  have he := finalExponentiation_of_conjugate_eq (mul_ne_zero ha hc) hfix
  rw [finalExponentiation_mul] at he
  exact eq_inv_of_mul_eq_one_right he

theorem conjugate_finalExponentiation (a : Fp12) :
    (finalExponentiation a).conjugate = finalExponentiation a.conjugate := by
  simp only [finalExponentiation, Fp12.powNat_eq_pow]
  exact map_pow conjugation a finalExpExponent

/-- On the actual output subgroup, the sixth Frobenius acts by inversion. -/
theorem pairing_pow_fp6_card {p : G1} {q : G2} (hp : G1.Valid p) (hq : G2.Valid q) :
    pairing p q ^ (Fp.modulus ^ 6) = (pairing p q)⁻¹ := by
  rw [pow_fp6_card_eq_conjugate]
  unfold pairing
  rw [conjugate_finalExponentiation]
  apply finalExponentiation_conjugate
  exact fun h => blsMillerLoop_ne_zero hp hq
    (conjugation.injective (h.trans (map_zero _).symm))

end EthLib.Cryptography.Bls
