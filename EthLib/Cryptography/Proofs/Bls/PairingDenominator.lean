import EthLib.Cryptography.Proofs.Bls.PairingSupport
import EthLib.Cryptography.Proofs.Bls.FinalExponentiation

/-!
# Proofs: final exponentiation removes the line denominators

The optimal ate formulas omit the vertical-line denominators.

Those denominators lie in the degree-6 subfield.

The final exponent is a multiple of the order of that subfield's multiplicative group.

So final exponentiation sends every nonzero denominator to 1, and omitting them does not change the pairing.
-/

namespace EthLib.Cryptography.Bls
open PairingTower Embedded

/-- The final exponent is a multiple of the order of the multiplicative Fp6
subfield. This is the concrete embedding-degree-12 calculation for BLS12-381. -/
theorem fp6_order_dvd_finalExpExponent :
    Fp.modulus ^ 6 - 1 ∣ finalExpExponent := by
  decide +kernel

/-- Every nonzero embedded Fp6 element is killed by the final exponent. -/
theorem finalExponentiation_fp6 {a : Fp6} (ha : a ≠ 0) :
    finalExponentiation (fp6ToFp12 a) = 1 := by
  rw [finalExponentiation, Fp12.powNat_eq_pow]
  obtain ⟨k, hk⟩ := fp6_order_dvd_finalExpExponent
  rw [hk, pow_mul]
  have hcard : (fp6ToFp12 a) ^ (Fp.modulus ^ 6 - 1) = 1 := by
    rw [← map_pow]
    have hc : a ^ (Fp.modulus ^ 6 - 1) = 1 := by
      simpa only [card_fp6] using FiniteField.pow_card_sub_one_eq_one a ha
    rw [hc, map_one]
  rw [hcard, one_pow]

/-- Final exponentiation removes any nonzero conjugation-fixed factor. -/
theorem finalExponentiation_of_conjugate_eq {a : Fp12} (ha : a ≠ 0)
    (hc : a.conjugate = a) : finalExponentiation a = 1 := by
  have he := (conjugate_eq_self_iff a).mp hc
  have h0 : a.c0 ≠ 0 := by
    intro h
    apply ha
    rw [he, h, map_zero]
  rw [he]
  exact finalExponentiation_fp6 h0

/-- The omitted denominator evaluates nontrivially in Fp6 and is killed
by the final exponent for all valid finite G1/G2 inputs. -/
theorem blsMillerState_denominator_finalExponentiation {p : G1} {q : G2}
    (hp : G1.Valid p) (hq : G2.Valid q) (hi : p.isInfinity = false) :
    finalExponentiation (evaluate (ofG1 p) (ofG1_onCurve hp) (by simpa using hi)
      (blsMillerState p q).denominator) = 1 :=
  finalExponentiation_of_conjugate_eq (blsMillerState_evaluate_nonzero hp hi hq).2
    (blsMillerState_denominator_conjugate hp hi q)

/-- Evaluate the proved formal numerator/denominator presentation at G1.
Nonzero support has been established separately, so this quotient is the
value of that presentation of the actual Miller rational function. -/
noncomputable def blsMillerValue (p : G1) (hp : G1.Valid p)
    (hi : p.isInfinity = false) (q : G2) : Fp12 :=
  let ev := evaluate (ofG1 p) (ofG1_onCurve hp) (by simpa using hi)
  ev (blsMillerState p q).numerator / ev (blsMillerState p q).denominator

theorem blsMillerValue_ne_zero {p : G1} {q : G2} (hp : G1.Valid p)
    (hq : G2.Valid q) (hi : p.isInfinity = false) : blsMillerValue p hp hi q ≠ 0 :=
  div_ne_zero (blsMillerState_evaluate_nonzero hp hi hq).1
    (blsMillerState_evaluate_nonzero hp hi hq).2

/-- The exact executable pairing equals final exponentiation of the full
Miller value, including its vertical denominator and negative-x conjugation. -/
theorem pairing_eq_full_millerValue {p : G1} {q : G2} (hp : G1.Valid p)
    (hq : G2.Valid q) (hpi : p.isInfinity = false) (hqi : q.isInfinity = false) :
    pairing p q = finalExponentiation (blsMillerValue p hp hpi q).conjugate := by
  rw [pairing_eq_formal_numerator hp q hpi hqi]
  let ev := evaluate (ofG1 p) (ofG1_onCurve hp) (by simpa using hpi)
  have hc := blsMillerState_denominator_conjugate hp hpi q
  have hd := blsMillerState_denominator_finalExponentiation hp hq hpi
  change finalExponentiation (ev (blsMillerState p q).numerator).conjugate =
    finalExponentiation ((ev (blsMillerState p q).numerator /
      ev (blsMillerState p q).denominator).conjugate)
  rw [show (ev (blsMillerState p q).numerator /
      ev (blsMillerState p q).denominator).conjugate =
      (ev (blsMillerState p q).numerator).conjugate /
      (ev (blsMillerState p q).denominator).conjugate from map_div₀ conjugation _ _, hc]
  simp only [finalExponentiation, Fp12.powNat_eq_pow, div_pow] at hd ⊢
  rw [hd, div_one]

/-- The actual pairing is nonzero on all valid inputs, including infinity. -/
theorem pairing_ne_zero {p : G1} {q : G2} (hp : G1.Valid p) (hq : G2.Valid q) :
    pairing p q ≠ 0 := by
  apply finalExponentiation_ne_zero
  exact fun h => blsMillerLoop_ne_zero hp hq
    (conjugation.injective (h.trans (map_zero conjugation).symm))

/-- The actual pairing lands in r-th roots of unity on valid inputs. -/
theorem pairing_pow_modulus {p : G1} {q : G2} (hp : G1.Valid p) (hq : G2.Valid q) :
    pairing p q ^ Fr.modulus = 1 := by
  apply finalExponentiation_pow_modulus
  exact fun h => blsMillerLoop_ne_zero hp hq
    (conjugation.injective (h.trans (map_zero conjugation).symm))

end EthLib.Cryptography.Bls
