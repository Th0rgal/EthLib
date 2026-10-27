import EthLib.Cryptography.Proofs.Bls.PairingMillerComposition
import EthLib.Cryptography.Proofs.Bls.PairingMillerCovariance

/-!
# Proofs: negating the twisted source point

Points coming from the G2 twist have a parity under conjugation.

Negating such a source point conjugates its Miller value.

G1 points are fixed by conjugation.
-/

namespace EthLib.Cryptography.Bls.Embedded
open PairingTower PairingSource

theorem negate_twistParity {R : EmbeddedPoint} (hR : TwistParity R) : TwistParity (negate R) := by
  exact ⟨hR.1, by simpa only [negate, Fp12.conjugate_neg] using congrArg Neg.neg hR.2⟩

theorem primeFrobenius_conjugate (a : Fp12) : (primeFrobenius a).conjugate = primeFrobenius a.conjugate := by
  simp only [primeFrobenius_apply]
  exact map_pow conjugation a Fp.modulus

theorem frobeniusPoint_twistParity {R : EmbeddedPoint} (hR : TwistParity R) :
    TwistParity (frobeniusPoint R) := by
  constructor
  · change (primeFrobenius R.x).conjugate = primeFrobenius R.x
    rw [primeFrobenius_conjugate, hR.1]
  · change (primeFrobenius R.y).conjugate = -primeFrobenius R.y
    rw [primeFrobenius_conjugate, hR.2, map_neg]

theorem fieldMapPoint_negate (f : Fp12 →+* Fp12) (R : EmbeddedPoint) :
    fieldMapPoint f (negate R) = negate (fieldMapPoint f R) := by
  simp only [fieldMapPoint, negate, map_neg]

theorem frobeniusPoint_negate (R : EmbeddedPoint) :
    frobeniusPoint (negate R) = negate (frobeniusPoint R) := fieldMapPoint_negate primeFrobenius R

theorem fieldMapPoint_conjugation_ofG1 (p : G1) : fieldMapPoint conjugation (ofG1 p) = ofG1 p := by
  unfold fieldMapPoint
  rw [conjugation_apply, conjugation_apply, ofG1_conjugate_x, ofG1_conjugate_y]

theorem fieldMapPoint_conjugation_of_twistParity {R : EmbeddedPoint} (hR : TwistParity R) :
    fieldMapPoint conjugation R = negate R := by
  simp only [fieldMapPoint, conjugation_apply, hR.1, hR.2, negate]

/-- Negating a twisted source conjugates its executable Miller value. -/
theorem millerLoop_negate {R : EmbeddedPoint} (hR : TwistParity R) (n : Nat) (p : G1) :
    millerLoop n (negate R) (ofG1 p) = (millerLoop n R (ofG1 p)).conjugate := by
  rw [← fieldMapPoint_conjugation_of_twistParity hR, ← fieldMapPoint_conjugation_ofG1 p,
    millerLoop_fieldMap, fieldMapPoint_conjugation_ofG1, conjugation_apply]

namespace ReducedMiller

theorem value_ne_zero (n : Nat) {R P : EmbeddedPoint} (hR : OnCurve R) (hpar : TwistParity R)
    (hP : OnCurve P) (hi : P.inf = false) (hsep : Tate.Separated P) : value n R P hP hi ≠ 0 := by
  have h0 := MillerState.run_evaluate_nonzero_at hR hpar hP hi hsep n P
  exact finalExponentiation_ne_zero (div_ne_zero h0.1 h0.2)

/-- The Frobenius-negated source contributes the inverse p-th power after reduction. -/
theorem value_negate_frobenius {n : Nat} (hn : n ≠ 0) {R : EmbeddedPoint}
    (hR : OnCurve R) (hpar : TwistParity R) {p : G1} (hp : G1.Valid p) (hi : p.isInfinity = false) :
    value n (negate (frobeniusPoint R)) (ofG1 p) (ofG1_onCurve hp) ((ofG1_inf p).trans hi) =
      (value n R (ofG1 p) (ofG1_onCurve hp) ((ofG1_inf p).trans hi) ^ Fp.modulus)⁻¹ := by
  have hsep := Tate.ofG1_separated hp hi
  have hfpar := negate_twistParity (frobeniusPoint_twistParity hpar)
  rw [value_eq_millerLoop hn (negate_onCurve (frobeniusPoint_onCurve hR)) hfpar
      (ofG1_onCurve hp) ((ofG1_inf p).trans hi) hsep,
    value_eq_millerLoop hn hR hpar (ofG1_onCurve hp) ((ofG1_inf p).trans hi) hsep,
    ← frobeniusPoint_negate, millerLoop_primeFrobenius, millerLoop_negate hpar]
  have hloop : millerLoop n R (ofG1 p) ≠ 0 := by
    have hv := value_ne_zero n hR hpar (ofG1_onCurve hp) ((ofG1_inf p).trans hi) hsep
    rw [value_eq_millerLoop hn hR hpar (ofG1_onCurve hp) ((ofG1_inf p).trans hi) hsep] at hv
    intro he
    apply hv
    rw [he]
    simp only [finalExponentiation, Fp12.powNat_eq_pow, zero_pow (by decide : finalExpExponent ≠ 0)]
  have hpow (a : Fp12) : finalExponentiation (a ^ Fp.modulus) = finalExponentiation a ^ Fp.modulus := by
    simp only [finalExponentiation, Fp12.powNat_eq_pow, pow_right_comm _ Fp.modulus]
  rw [hpow, finalExponentiation_conjugate hloop, inv_pow]

/-- Positive Miller value scalar law when [|x|]R is the negated Frobenius of R. -/
theorem value_blsX_scalar_cursor {n : Nat} (hn : n ≠ 0) {R : EmbeddedPoint}
    (hR : OnCurve R) (hpar : TwistParity R) {p : G1} (hp : G1.Valid p) (hi : p.isInfinity = false)
    (heigen : primeFrobeniusHom (toAmbient R hR) = -(blsX • toAmbient R hR)) :
    value blsX (state n R (ofG1 p)).point (ofG1 p) (ofG1_onCurve hp) ((ofG1_inf p).trans hi) =
      value blsX R (ofG1 p) (ofG1_onCurve hp) ((ofG1_inf p).trans hi) ^ n := by
  have hsep := Tate.ofG1_separated hp hi
  have hcomp := value_composition (by decide : blsX ≠ 0) hn hR hpar (ofG1_onCurve hp)
    ((ofG1_inf p).trans hi) hsep
  have he : toAmbient (state blsX R (ofG1 p)).point (state_onCurve blsX hR (ofG1 p)) =
      toAmbient (negate (frobeniusPoint R)) (negate_onCurve (frobeniusPoint_onCurve hR)) := by
    rw [state_group (by decide : blsX ≠ 0) hR, negate_toAmbient (frobeniusPoint_onCurve hR),
      frobeniusPoint_toAmbient hR, heigen, neg_neg]
  rw [value_eq_of_toAmbient_eq hn (state_onCurve blsX hR _) (negate_onCurve (frobeniusPoint_onCurve hR))
    (state_parity blsX hpar _) (negate_twistParity (frobeniusPoint_twistParity hpar))
    (ofG1_onCurve hp) ((ofG1_inf p).trans hi) hsep he,
    value_negate_frobenius hn hR hpar hp hi] at hcomp
  let u := value n R (ofG1 p) (ofG1_onCurve hp) ((ofG1_inf p).trans hi)
  have hu : u ≠ 0 := value_ne_zero n hR hpar (ofG1_onCurve hp) ((ofG1_inf p).trans hi) hsep
  have hur : u ^ Fr.modulus = 1 := by
    exact finalExponentiation_pow_modulus (div_ne_zero
      (MillerState.run_evaluate_nonzero_at hR hpar (ofG1_onCurve hp) ((ofG1_inf p).trans hi) hsep n _).1
      (MillerState.run_evaluate_nonzero_at hR hpar (ofG1_onCurve hp) ((ofG1_inf p).trans hi) hsep n _).2)
  have hc : u ^ blsX * u ^ Fp.modulus = 1 := by
    rw [← pow_add, show blsX + Fp.modulus = Fr.modulus * ((blsX + Fp.modulus) / Fr.modulus) by decide,
      pow_mul, hur, one_pow]
  have hc' : u ^ blsX = (u ^ Fp.modulus)⁻¹ := eq_inv_of_mul_eq_one_left hc
  change _ * u ^ blsX = (u ^ Fp.modulus)⁻¹ * _ at hcomp
  rw [← hc', mul_comm (u ^ blsX)] at hcomp
  exact mul_right_cancel₀ (pow_ne_zero blsX hu) hcomp

end ReducedMiller
end EthLib.Cryptography.Bls.Embedded
