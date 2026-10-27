import EthLib.Cryptography.Proofs.Bls.PairingG1Reciprocity
import EthLib.Cryptography.Proofs.Bls.PairingPsi

/-!
# Proofs: Frobenius and the signed Miller value

The Frobenius map acts on embedded points coordinate by coordinate, and keeps them on the curve.

Slopes, line weights and norms commute with it.

These facts connect the Miller value for the negative parameter to the one for its absolute value.
-/


namespace EthLib.Cryptography.Bls.Embedded


open PairingTower PairingSource

/-- Applying a field homomorphism to an embedded curve record. -/
def fieldMapPoint (f : Fp12 →+* Fp12) (P : EmbeddedPoint) : EmbeddedPoint :=
  ⟨f P.x, f P.y, P.inf⟩

theorem fieldMapPoint_onCurve (f : Fp12 →+* Fp12) {P : EmbeddedPoint} (hP : OnCurve P) :
    OnCurve (fieldMapPoint f P) := by
  intro hi
  have h := congrArg f (hP hi)
  simpa only [map_pow, map_add, map_ofNat] using h

theorem fieldMapPoint_toAmbient (f : Fp12 →+* Fp12) {P : EmbeddedPoint} (hP : OnCurve P) :
    toAmbient (fieldMapPoint f P) (fieldMapPoint_onCurve f hP) =
      scaledPoint f 1 (by rw [one_pow, mul_one, map_ofNat]) (toAmbient P hP) := by
  by_cases hi : P.inf = true
  · rw [toAmbient_inf (fieldMapPoint_onCurve f hP) hi, toAmbient_inf hP hi]
    rfl
  · rw [toAmbient_finite (fieldMapPoint_onCurve f hP) (Bool.eq_false_iff.mpr hi),
      toAmbient_finite hP (Bool.eq_false_iff.mpr hi)]
    simp only [scaledPoint, one_pow, mul_one, fieldMapPoint]

/-- Coordinate Frobenius, retaining the infinity flag. -/
noncomputable def frobeniusPoint : EmbeddedPoint → EmbeddedPoint := fieldMapPoint primeFrobenius

theorem frobeniusPoint_onCurve {P : EmbeddedPoint} (hP : OnCurve P) :
    OnCurve (frobeniusPoint P) := fieldMapPoint_onCurve primeFrobenius hP

theorem frobeniusPoint_toAmbient {P : EmbeddedPoint} (hP : OnCurve P) :
    toAmbient (frobeniusPoint P) (frobeniusPoint_onCurve hP) =
      primeFrobeniusHom (toAmbient P hP) := fieldMapPoint_toAmbient primeFrobenius hP

/-- Exact signed Frobenius eigenrelation on the supported concrete generator span. -/
theorem frobenius_generator_mulNat_signed (n : Nat) :
    primeFrobeniusHom (toAmbient (ofG2 (G2.mulNat G2.generator n))
      (ofG2_onCurve (G2.valid_mulNat G2.valid_generator n))) =
      -(blsX • toAmbient (ofG2 (G2.mulNat G2.generator n))
        (ofG2_onCurve (G2.valid_mulNat G2.valid_generator n))) := by
  rw [PairingPsi.primeFrobenius_ofG2_mulNat]
  apply eq_neg_of_add_eq_zero_left
  rw [← add_nsmul]
  have hr := (ofG2_inSubgroup_iff (G2.valid_mulNat G2.valid_generator n)).mp
    (G2.inSubgroup_mulNat G2.valid_generator G2.inSubgroup_generator n)
  have harith : Fp.modulus + blsX = ((Fp.modulus + blsX) / Fr.modulus) * Fr.modulus := by decide +kernel
  rw [harith, mul_nsmul', hr, nsmul_zero]

namespace SplitLine

theorem norm_vertical_weight (s : SplitLine) {T : EmbeddedPoint} (hT : OnCurve T) :
    s.norm (vertical T) = s.weight T * s.weight (negate T) := by
  by_cases hi : T.inf = true
  · simp [vertical, weight, negate, hi]
  · rw [s.norm_vertical hT (Bool.eq_false_iff.mpr hi)]
    simp [weight, negate, hi, sub_neg_eq_add]


theorem weight_fieldMap (s : SplitLine) (f : Fp12 →+* Fp12)
    (hm : f s.slope = s.slope) (hb : f s.offset = s.offset) (P : EmbeddedPoint) :
    s.weight (fieldMapPoint f P) = f (s.weight P) := by
  by_cases hi : P.inf = true
  · simp [weight, fieldMapPoint, hi]
  · simp only [weight, fieldMapPoint, if_neg hi, map_sub, map_add, map_mul, hm, hb]

/-- A line over Fp transports its normalized value by p-Frobenius. -/
theorem weight_frobenius (s : SplitLine)
    (hm : primeFrobenius s.slope = s.slope) (hb : primeFrobenius s.offset = s.offset)
    (P : EmbeddedPoint) : s.weight (frobeniusPoint P) = s.weight P ^ Fp.modulus :=
  (s.weight_fieldMap primeFrobenius hm hb P).trans (primeFrobenius_apply _)

end SplitLine
namespace VerticalNorm

theorem norm_vertical_weight (P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false)
    (T : EmbeddedPoint) :
    norm P hP hi (vertical T) = weight P T * weight P (negate T) := by
  rw [norm_vertical]
  simp only [weight, negate, pow_two]


theorem weight_fieldMap (P T : EmbeddedPoint) (f : Fp12 →+* Fp12) (hx : f P.x = P.x) :
    weight P (fieldMapPoint f T) = f (weight P T) := by
  by_cases hi : T.inf = true
  · simp [weight, fieldMapPoint, hi]
  · simp only [weight, fieldMapPoint, if_neg hi, map_sub, hx]

theorem weight_frobenius (P T : EmbeddedPoint) (hx : primeFrobenius P.x = P.x) :
    weight P (frobeniusPoint T) = weight P T ^ Fp.modulus :=
  (weight_fieldMap P T primeFrobenius hx).trans (primeFrobenius_apply _)

end VerticalNorm
namespace MillerNorm

/-- The exact reciprocal norm identity for the negative Miller function.
The extra vertical factor accounts for negating the final cursor. -/
theorem negative_norm (N : MillerNorm) {R : EmbeddedPoint} (hR : OnCurve R)
    (P : EmbeddedPoint) {n : Nat} (hn : n ≠ 0)
    (hV : ∀ T, OnCurve T → N.norm (vertical T) = N.weight T * N.weight (negate T))
    (hD : N.norm (MillerState.run n R P n.log2 (MillerState.initial R)).denominator ≠ 0) :
    let s := MillerState.run n R P n.log2 (MillerState.initial R)
    N.norm s.denominator / N.norm (s.numerator * vertical s.point) =
      (N.weight R ^ n * N.weight (negate s.point))⁻¹ := by
  dsimp only
  let s := MillerState.run n R P n.log2 (MillerState.initial R)
  have h := N.millerLoop hR P hn
  change N.norm s.numerator * N.weight s.point = N.norm s.denominator * N.weight R ^ n at h
  change N.norm s.denominator / N.norm (s.numerator * vertical s.point) = _
  rw [map_mul, hV s.point (MillerState.run_onCurve hR P n n.log2 hR), ← mul_assoc, h]
  change N.norm s.denominator ≠ 0 at hD
  rw [mul_assoc, div_mul_eq_div_div, div_self hD, one_div]

/-- The normalized source weight is independent of unused infinity coordinates. -/
theorem weight_eq_of_toAmbient_eq (N : MillerNorm) {P Q : EmbeddedPoint}
    (hP : OnCurve P) (hQ : OnCurve Q) (he : toAmbient P hP = toAmbient Q hQ) :
    N.weight P = N.weight Q := by
  by_cases hi : P.inf = true
  · rw [N.weight_inf P hi, N.weight_inf Q ((inf_eq_of_toAmbient_eq hP hQ he).symm.trans hi)]
  · rw [eq_of_toAmbient_eq_of_finite hP hQ (Bool.eq_false_iff.mpr hi) he]

/-- The numerical cancellation used for the signed BLS parameter. -/
theorem reduced_negative_of_weight_eigen (N : MillerNorm) {R : EmbeddedPoint}
    (hR : OnCurve R) (P : EmbeddedPoint)
    (hV : ∀ T, OnCurve T → N.norm (vertical T) = N.weight T * N.weight (negate T))
    (hD : N.norm (MillerState.run blsX R P blsX.log2 (MillerState.initial R)).denominator ≠ 0)
    (hweight : N.weight R ≠ 0)
    (heigen : N.weight (negate (MillerState.run blsX R P blsX.log2 (MillerState.initial R)).point) =
      N.weight R ^ Fp.modulus) :
    let s := MillerState.run blsX R P blsX.log2 (MillerState.initial R)
    finalExponentiation (N.norm s.denominator / N.norm (s.numerator * vertical s.point)) = 1 := by
  dsimp only
  rw [N.negative_norm hR P (by decide : blsX ≠ 0) hV hD, heigen, ← pow_add]
  have harith : blsX + Fp.modulus = Fr.modulus * ((blsX + Fp.modulus) / Fr.modulus) := by decide +kernel
  rw [harith, pow_mul]
  have hred := finalExponentiation_pow_modulus hweight
  simp only [finalExponentiation, Fp12.powNat_eq_pow] at hred ⊢
  rw [inv_pow, pow_right_comm, pow_right_comm (N.weight R), hred, one_pow, inv_one]


/-- Frobenius compatibility of a concrete norm turns the signed cursor relation
into the weight identity needed above. -/
theorem negative_cursor_weight (N : MillerNorm) {R : EmbeddedPoint} (hR : OnCurve R)
    (P : EmbeddedPoint)
    (hf : ∀ T, N.weight (frobeniusPoint T) = N.weight T ^ Fp.modulus)
    (he : primeFrobeniusHom (toAmbient R hR) = -(blsX • toAmbient R hR)) :
    N.weight (negate (MillerState.run blsX R P blsX.log2 (MillerState.initial R)).point) =
      N.weight R ^ Fp.modulus := by
  rw [← hf R]
  apply N.weight_eq_of_toAmbient_eq
    (negate_onCurve (MillerState.run_onCurve hR _ _ _ hR)) (frobeniusPoint_onCurve hR)
  rw [negate_toAmbient (MillerState.run_onCurve hR _ _ _ hR),
    MillerState.millerLoop_group hR P (by decide : blsX ≠ 0), frobeniusPoint_toAmbient hR, he]

end MillerNorm
end EthLib.Cryptography.Bls.Embedded

namespace EthLib.Cryptography.Bls.Embedded
open PairingTower

theorem ofG1_primeFrobenius_x (p : G1) :
    primeFrobenius (ofG1 p).x = (ofG1 p).x := by
  unfold ofG1
  split
  · exact map_zero primeFrobenius
  · exact primeFrobenius_fp _

theorem ofG1_primeFrobenius_y (p : G1) :
    primeFrobenius (ofG1 p).y = (ofG1 p).y := by
  unfold ofG1
  split
  · exact map_zero primeFrobenius
  · exact primeFrobenius_fp _

end EthLib.Cryptography.Bls.Embedded

namespace EthLib.Cryptography.Bls.Embedded
open PairingTower

theorem addSlope_fieldMap (f : Fp12 →+* Fp12) (x y t z : Fp12) :
    f (Line.addSlope x y t z) = Line.addSlope (f x) (f y) (f t) (f z) := by
  change f ((z - y) * (t - x)⁻¹) = (f z - f y) * (f t - f x)⁻¹
  simp only [map_mul, map_sub, map_inv₀]

theorem tangentSlope_fieldMap (f : Fp12 →+* Fp12) (x y : Fp12) :
    f (Line.tangentSlope x y) = Line.tangentSlope (f x) (f y) := by
  have hc2 : (⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 2)), Fp6.zero⟩ : Fp12) = 2 := by decide
  have hc3 : (⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 3)), Fp6.zero⟩ : Fp12) = 3 := by decide
  simp only [Line.tangentSlope, hc2, hc3]
  change f (3 * x * x * (2 * y)⁻¹) = 3 * f x * f x * (2 * f y)⁻¹
  simp only [map_mul, map_inv₀, map_ofNat]

private theorem ofG1_coord_fixed (p : G1) :
    primeFrobenius (ofG1 p).x = (ofG1 p).x ∧ primeFrobenius (ofG1 p).y = (ofG1 p).y :=
  ⟨ofG1_primeFrobenius_x p, ofG1_primeFrobenius_y p⟩

theorem secant_coeff_fixed {p t : G1} (hp : G1.Valid p) (ht : G1.Valid t)
    (hpi : p.isInfinity = false) (hti : t.isInfinity = false)
    (hx : (ofG1 p).x ≠ (ofG1 t).x) :
    let s := SplitLine.secant (ofG1_onCurve hp) (ofG1_onCurve ht)
      (by simpa only [ofG1_inf] using hpi) (by simpa only [ofG1_inf] using hti) hx
    primeFrobenius s.slope = s.slope ∧ primeFrobenius s.offset = s.offset := by
  dsimp only [SplitLine.secant, SplitLine.ofChord]
  have hp' := ofG1_coord_fixed p
  have ht' := ofG1_coord_fixed t
  have hm : primeFrobenius (Line.addSlope (ofG1 p).x (ofG1 p).y (ofG1 t).x (ofG1 t).y) =
      Line.addSlope (ofG1 p).x (ofG1 p).y (ofG1 t).x (ofG1 t).y := by
    rw [addSlope_fieldMap, hp'.1, hp'.2, ht'.1, ht'.2]
  exact ⟨hm, by rw [map_sub, map_mul, hm, hp'.1, hp'.2]⟩

theorem tangent_coeff_fixed {p : G1} (hp : G1.Valid p) (hpi : p.isInfinity = false)
    (hy : (ofG1 p).y ≠ 0) :
    let s := SplitLine.tangent (ofG1_onCurve hp) (by simpa only [ofG1_inf] using hpi) hy
    primeFrobenius s.slope = s.slope ∧ primeFrobenius s.offset = s.offset := by
  dsimp only [SplitLine.tangent, SplitLine.ofChord]
  have hp' := ofG1_coord_fixed p
  have hm : primeFrobenius (Line.tangentSlope (ofG1 p).x (ofG1 p).y) =
      Line.tangentSlope (ofG1 p).x (ofG1 p).y := by
    rw [tangentSlope_fieldMap, hp'.1, hp'.2]
  exact ⟨hm, by rw [map_sub, map_mul, hm, hp'.1, hp'.2]⟩

end EthLib.Cryptography.Bls.Embedded

namespace EthLib.Cryptography.Bls.Embedded
open PairingTower

namespace MillerState

theorem run_evaluate_nonzero_at {R Q : EmbeddedPoint} (hR : OnCurve R) (hpar : TwistParity R)
    (hQ : OnCurve Q) (hi : Q.inf = false) (hsep : Tate.Separated Q) (n : Nat) (P : EmbeddedPoint) :
    evaluate Q hQ hi (run n R P n.log2 (initial R)).numerator ≠ 0 ∧
      evaluate Q hQ hi (run n R P n.log2 (initial R)).denominator ≠ 0 := by
  rw [run_evalIndependent n R P Q]
  apply run_evaluate_nonzero hR hpar hQ hi hsep.1 hsep.2.1 hsep.2.2 _ _ hR hpar
  · simpa only [initial, map_one] using (one_ne_zero : (1 : Fp12) ≠ 0)
  · simpa only [initial, map_one] using (one_ne_zero : (1 : Fp12) ≠ 0)

end MillerState
namespace SplitLine

theorem norm_denominator_ne_zero (s : SplitLine) {R : EmbeddedPoint}
    (hR : OnCurve R) (hpar : TwistParity R)
    (h₁ : Tate.Separated s.point₁) (h₂ : Tate.Separated s.point₂) (h₃ : Tate.Separated s.point₃)
    (n : Nat) (P : EmbeddedPoint) :
    s.norm (MillerState.run n R P n.log2 (MillerState.initial R)).denominator ≠ 0 :=
  mul_ne_zero (mul_ne_zero
    (MillerState.run_evaluate_nonzero_at hR hpar s.point₁_onCurve rfl h₁ n P).2
    (MillerState.run_evaluate_nonzero_at hR hpar s.point₂_onCurve rfl h₂ n P).2)
    (MillerState.run_evaluate_nonzero_at hR hpar s.point₃_onCurve rfl h₃ n P).2

theorem weight_ne_zero (s : SplitLine) {R : EmbeddedPoint}
    (hR : OnCurve R) (hpar : TwistParity R)
    (h₁ : Tate.Separated s.point₁) (h₂ : Tate.Separated s.point₂) (h₃ : Tate.Separated s.point₃) :
    s.weight R ≠ 0 := by
  have hv : s.norm (vertical R) ≠ 0 := mul_ne_zero (mul_ne_zero
    (evaluate_vertical_ne_zero hR s.point₁_onCurve rfl hpar h₁.2.1 h₁.2.2)
    (evaluate_vertical_ne_zero hR s.point₂_onCurve rfl hpar h₂.2.1 h₂.2.2))
    (evaluate_vertical_ne_zero hR s.point₃_onCurve rfl hpar h₃.2.1 h₃.2.2)
  rw [s.norm_vertical_weight hR] at hv
  exact (mul_ne_zero_iff.mp hv).1

/-- Signed-Ate reciprocity on a split Fp line, with all support and generator
Frobenius hypotheses discharged by the concrete arithmetic theorems. -/
theorem reduced_negative_generator_norm (s : SplitLine)
    (hm : primeFrobenius s.slope = s.slope) (hb : primeFrobenius s.offset = s.offset)
    (h₁ : Tate.Separated s.point₁) (h₂ : Tate.Separated s.point₂) (h₃ : Tate.Separated s.point₃)
    (k : Nat) (P : EmbeddedPoint) :
    let R := ofG2 (G2.mulNat G2.generator k)
    let st := MillerState.run blsX R P blsX.log2 (MillerState.initial R)
    finalExponentiation (s.norm st.denominator / s.norm (st.numerator * vertical st.point)) = 1 := by
  dsimp only
  have hR := ofG2_onCurve (G2.valid_mulNat G2.valid_generator k)
  have hpar := ofG2_twistParity (G2.mulNat G2.generator k)
  exact s.millerNorm.reduced_negative_of_weight_eigen hR P
    (fun T hT => s.norm_vertical_weight hT)
    (s.norm_denominator_ne_zero hR hpar h₁ h₂ h₃ blsX P)
    (s.weight_ne_zero hR hpar h₁ h₂ h₃)
    (s.millerNorm.negative_cursor_weight hR P (s.weight_frobenius hm hb)
      (frobenius_generator_mulNat_signed k))

end SplitLine
namespace VerticalNorm

theorem weight_ne_zero {P R : EmbeddedPoint} (hP : OnCurve P) (hi : P.inf = false)
    (hsep : Tate.Separated P) (hR : OnCurve R) (hpar : TwistParity R) : weight P R ≠ 0 := by
  by_cases hr : R.inf = true
  · simpa only [weight, if_pos hr] using (one_ne_zero : (1 : Fp12) ≠ 0)
  · rw [weight, if_neg hr]
    exact sub_ne_zero.mpr (Ne.symm (x_ne_of_twistParity hR hP (Bool.eq_false_iff.mpr hr)
      hi hpar hsep.2.1 hsep.2.2))

/-- Signed-Ate reciprocity for the vertical through a concrete finite G1 point. -/
theorem reduced_negative_generator_norm {p : G1} (hp : G1.Valid p) (hi : p.isInfinity = false)
    (k : Nat) (P : EmbeddedPoint) :
    let Q := ofG1 p
    let R := ofG2 (G2.mulNat G2.generator k)
    let st := MillerState.run blsX R P blsX.log2 (MillerState.initial R)
    let N := millerNorm Q (ofG1_onCurve hp) ((ofG1_inf p).trans hi)
    finalExponentiation (N.norm st.denominator / N.norm (st.numerator * vertical st.point)) = 1 := by
  dsimp only
  have hQ := ofG1_onCurve hp
  have hqi : (ofG1 p).inf = false := by simpa only [ofG1_inf] using hi
  have hsep := Tate.ofG1_separated hp hi
  have hR := ofG2_onCurve (G2.valid_mulNat G2.valid_generator k)
  have hpar := ofG2_twistParity (G2.mulNat G2.generator k)
  let N := millerNorm (ofG1 p) hQ hqi
  have hD : N.norm (MillerState.run blsX (ofG2 (G2.mulNat G2.generator k)) P blsX.log2
      (MillerState.initial (ofG2 (G2.mulNat G2.generator k)))).denominator ≠ 0 :=
    mul_ne_zero (MillerState.run_evaluate_nonzero_at hR hpar hQ hqi hsep blsX P).2
      (MillerState.run_evaluate_nonzero_at hR hpar (negate_onCurve hQ) hqi hsep.negate blsX P).2
  exact N.reduced_negative_of_weight_eigen hR P
    (fun T _ => norm_vertical_weight (ofG1 p) hQ hqi T) hD
    (weight_ne_zero hQ hqi hsep hR hpar)
    (N.negative_cursor_weight hR P (fun T => weight_frobenius (ofG1 p) T (ofG1_primeFrobenius_x p))
      (frobenius_generator_mulNat_signed k))

end VerticalNorm
end EthLib.Cryptography.Bls.Embedded

