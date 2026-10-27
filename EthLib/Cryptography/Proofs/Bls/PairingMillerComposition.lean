import EthLib.Cryptography.Proofs.Bls.PairingSignedG1

/-!
# Proofs: composing Miller loops

The Miller state for a scalar `n` is a cursor point and a function.

The cursor is `n` times the source point, and the function stays nonzero.

Scalars compose: two compositions that reach the same scalar give the same function, up to the expected factors.
-/

namespace EthLib.Cryptography.Bls.Embedded
open FunctionSymmetry
namespace ReducedMiller

noncomputable def state (n : Nat) (R P : EmbeddedPoint) : MillerState :=
  MillerState.run n R P n.log2 (MillerState.initial R)

theorem state_onCurve (n : Nat) {R : EmbeddedPoint} (hR : OnCurve R) (P : EmbeddedPoint) :
    OnCurve (state n R P).point := MillerState.run_onCurve hR _ _ _ hR

theorem state_parity (n : Nat) {R : EmbeddedPoint} (hR : TwistParity R) (P : EmbeddedPoint) :
    TwistParity (state n R P).point :=
  MillerState.run_twistParity hR P n n.log2 (s := MillerState.initial R) hR

theorem state_symmetric (n : Nat) {R : EmbeddedPoint} (hR : TwistParity R) (P : EmbeddedPoint) :
    Symmetric (state n R P).numerator ∧ Symmetric (state n R P).denominator :=
  run_symmetric hR P n n.log2 hR symmetric_one symmetric_one

theorem state_group {n : Nat} (hn : n ≠ 0) {R : EmbeddedPoint} (hR : OnCurve R) (P : EmbeddedPoint) :
    toAmbient (state n R P).point (state_onCurve n hR P) = n • toAmbient R hR :=
  MillerState.millerLoop_group hR P hn

theorem state_nonzero (n : Nat) (R P : EmbeddedPoint) :
    (state n R P).numerator ≠ 0 ∧ (state n R P).denominator ≠ 0 :=
  MillerState.millerLoop_nonzero R P n

noncomputable def value (n : Nat) (R P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false) : Fp12 :=
  finalExponentiation (evaluate P hP hi (state n R P).numerator /
    evaluate P hP hi (state n R P).denominator)

private theorem composition_algebra {M : Type*} [CommSemiring M]
    (a b c d e f g h q u v w : M) (m n : Nat) (hw : IsUnit w)
    (ha : a * w = b * u ^ m) (hc : c * u = d * q ^ n)
    (he : e * w = f * v ^ n) (hg : g * v = h * q ^ m) :
    a * c ^ m * f * h ^ n = e * g ^ n * b * d ^ m := by
  apply hw.mul_left_inj.mp
  calc
    _ = (a * w) * c ^ m * f * h ^ n := by ring
    _ = b * (c * u) ^ m * f * h ^ n := by rw [ha, mul_pow]; ring
    _ = b * (d * q ^ n) ^ m * f * h ^ n := by rw [hc]
    _ = f * (h * q ^ m) ^ n * b * d ^ m := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n m]
      ring
    _ = (e * w) * g ^ n * b * d ^ m := by rw [← hg, he, mul_pow]; ring
    _ = _ := by ring

theorem pointFractional_eq_of_toAmbient_eq {T R : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (he : toAmbient T hT = toAmbient R hR) : pointFractional T = pointFractional R :=
  congrArg (fun I : Ideal CoordinateRing => (I : FractionalIdeal NonZeroDivisors FunctionField))
    (Tate.pointIdeal_eq_of_toAmbient_eq hT hR he)

/-- The two scalar compositions have exactly the same final point ideal. -/
theorem composition_cursor_ideal {m n : Nat} (hm : m ≠ 0) (hn : n ≠ 0)
    {R : EmbeddedPoint} (hR : OnCurve R) (P : EmbeddedPoint) :
    pointFractional (state m (state n R P).point P).point =
      pointFractional (state n (state m R P).point P).point := by
  apply pointFractional_eq_of_toAmbient_eq (state_onCurve m (state_onCurve n hR P) P)
    (state_onCurve n (state_onCurve m hR P) P)
  rw [state_group hm (state_onCurve n hR P) P, state_group hn (state_onCurve m hR P) P,
    state_group hm hR P, state_group hn hR P, smul_smul, smul_smul, Nat.mul_comm]

/-- Regular-function divisor comparison for f_m([n]R) f_n(R)^m and
f_n([m]R) f_m(R)^n. The common final point ideal is invertible. -/
theorem composition_ideal {m n : Nat} (hm : m ≠ 0) (hn : n ≠ 0)
    {R : EmbeddedPoint} (hR : OnCurve R) (P : EmbeddedPoint) :
    let A := state m (state n R P).point P
    let B := state n R P
    let C := state n (state m R P).point P
    let D := state m R P
    principal (A.numerator * B.numerator ^ m * C.denominator * D.denominator ^ n) =
      principal (C.numerator * D.numerator ^ n * A.denominator * B.denominator ^ m) := by
  dsimp only
  apply FractionalIdeal.coeIdeal_injective (K := FunctionField)
  simp only [principal, FractionalIdeal.coeIdeal_span_singleton]
  change principalFractional _ = principalFractional _
  simp only [principalFractional_mul, principalFractional_pow]
  have ha := miller_global_fractionalIdeal (state_onCurve n hR P) P hm
  have hc := miller_global_fractionalIdeal hR P hn
  have he := miller_global_fractionalIdeal (state_onCurve m hR P) P hn
  have hg := miller_global_fractionalIdeal hR P hm
  change principalFractional (state n (state m R P).point P).numerator *
    pointFractional (state n (state m R P).point P).point = _ at he
  rw [← composition_cursor_ideal hm hn hR P] at he
  exact composition_algebra _ _ _ _ _ _ _ _ _ _ _ _ m n
    (pointFractional_isUnit (state_onCurve m (state_onCurve n hR P) P)) ha hc he hg

private theorem symmetric_pow {f : CoordinateRing} (hf : Symmetric f) (n : Nat) : Symmetric (f ^ n) := by
  simp only [FunctionSymmetry.Symmetric, map_pow, pow_right_comm _ n 2]
  rw [hf]

/-- The actual reduced Miller functions obey scalar-composition reciprocity. -/
theorem value_composition {m n : Nat} (hm : m ≠ 0) (hn : n ≠ 0)
    {R P : EmbeddedPoint} (hR : OnCurve R) (hpar : TwistParity R)
    (hP : OnCurve P) (hi : P.inf = false) (hsep : Tate.Separated P) :
    value m (state n R P).point P hP hi * value n R P hP hi ^ m =
      value n (state m R P).point P hP hi * value m R P hP hi ^ n := by
  let A := state m (state n R P).point P
  let B := state n R P
  let C := state n (state m R P).point P
  let D := state m R P
  have has := state_symmetric m (state_parity n hpar P) P
  have hbs := state_symmetric n hpar P
  have hcs := state_symmetric n (state_parity m hpar P) P
  have hds := state_symmetric m hpar P
  have han := state_nonzero m B.point P
  have hbn := state_nonzero n R P
  have hcn := state_nonzero n D.point P
  have hdn := state_nonzero m R P
  have hid := composition_ideal hm hn hR P
  have hred := reduced_evaluate_eq_of_ideal_eq hP hi
    (mul_ne_zero (mul_ne_zero (mul_ne_zero han.1 (pow_ne_zero m hbn.1)) hcn.2) (pow_ne_zero n hdn.2))
    (symmetric_mul (symmetric_mul (symmetric_mul has.1 (symmetric_pow hbs.1 m)) hcs.2)
      (symmetric_pow hds.2 n))
    (symmetric_mul (symmetric_mul (symmetric_mul hcs.1 (symmetric_pow hds.1 n)) has.2)
      (symmetric_pow hbs.2 m)) hid
  have ha0 := MillerState.run_evaluate_nonzero_at (state_onCurve n hR P) (state_parity n hpar P)
    hP hi hsep m P
  have hb0 := MillerState.run_evaluate_nonzero_at hR hpar hP hi hsep n P
  have hc0 := MillerState.run_evaluate_nonzero_at (state_onCurve m hR P) (state_parity m hpar P)
    hP hi hsep n P
  have hd0 := MillerState.run_evaluate_nonzero_at hR hpar hP hi hsep m P
  have reduce_div (a b : Fp12) : finalExponentiation (a / b) = finalExponentiation a / finalExponentiation b := by
    simp only [finalExponentiation, Fp12.powNat_eq_pow, div_pow]
  have reduce_pow (a : Fp12) (j : Nat) : finalExponentiation (a ^ j) = finalExponentiation a ^ j := by
    simp only [finalExponentiation, Fp12.powNat_eq_pow, pow_right_comm _ j]
  simp only [map_mul, map_pow, finalExponentiation_mul, reduce_pow] at hred
  simp only [value, reduce_div, div_pow]
  rw [← mul_div_mul_comm, ← mul_div_mul_comm]
  apply (div_eq_div_iff
    (mul_ne_zero (finalExponentiation_ne_zero ha0.2) (pow_ne_zero m (finalExponentiation_ne_zero hb0.2)))
    (mul_ne_zero (finalExponentiation_ne_zero hc0.2) (pow_ne_zero n (finalExponentiation_ne_zero hd0.2)))).mpr
  dsimp only [B, D, state] at hred ⊢
  linear_combination hred


theorem principal_eq_of_fractional_eq {a b : CoordinateRing}
    (he : principalFractional a = principalFractional b) : principal a = principal b := by
  apply FractionalIdeal.coeIdeal_injective (K := FunctionField)
  simpa only [principal, FractionalIdeal.coeIdeal_span_singleton, principalFractional] using he

/-- Reduced Miller values depend on the represented source point for every positive index. -/
theorem value_eq_of_toAmbient_eq {n : Nat} (hn : n ≠ 0) {R T P : EmbeddedPoint}
    (hR : OnCurve R) (hT : OnCurve T) (hparR : TwistParity R) (hparT : TwistParity T)
    (hP : OnCurve P) (hi : P.inf = false) (hsep : Tate.Separated P)
    (he : toAmbient R hR = toAmbient T hT) : value n R P hP hi = value n T P hP hi := by
  have hI := pointFractional_eq_of_toAmbient_eq hR hT he
  have hC : pointFractional (state n R P).point = pointFractional (state n T P).point := by
    apply pointFractional_eq_of_toAmbient_eq (state_onCurve n hR P) (state_onCurve n hT P)
    rw [state_group hn hR P, state_group hn hT P, he]
  have hRinv := miller_global_fractionalIdeal hR P hn
  have hTinv := miller_global_fractionalIdeal hT P hn
  change principalFractional (state n R P).numerator * pointFractional (state n R P).point =
    principalFractional (state n R P).denominator * pointFractional R ^ n at hRinv
  change principalFractional (state n T P).numerator * pointFractional (state n T P).point =
    principalFractional (state n T P).denominator * pointFractional T ^ n at hTinv
  rw [hC, hI] at hRinv
  have hid : principal ((state n R P).numerator * (state n T P).denominator) =
      principal ((state n T P).numerator * (state n R P).denominator) := by
    apply principal_eq_of_fractional_eq
    simp only [principalFractional_mul]
    apply (pointFractional_isUnit (state_onCurve n hT P)).mul_left_inj.mp
    calc
      _ = (principalFractional (state n R P).numerator * pointFractional (state n T P).point) *
          principalFractional (state n T P).denominator := by ring
      _ = principalFractional (state n R P).denominator *
          (principalFractional (state n T P).denominator * pointFractional T ^ n) := by
        rw [hRinv]; ring
      _ = principalFractional (state n R P).denominator *
          (principalFractional (state n T P).numerator * pointFractional (state n T P).point) := by
        rw [hTinv]
      _ = _ := by ring
  have hsR := state_symmetric n hparR P
  have hsT := state_symmetric n hparT P
  have hred := reduced_evaluate_eq_of_ideal_eq hP hi
    (mul_ne_zero (state_nonzero n R P).1 (state_nonzero n T P).2)
    (symmetric_mul hsR.1 hsT.2) (symmetric_mul hsT.1 hsR.2) hid
  have hR0 := MillerState.run_evaluate_nonzero_at hR hparR hP hi hsep n P
  have hT0 := MillerState.run_evaluate_nonzero_at hT hparT hP hi hsep n P
  simp only [map_mul, finalExponentiation_mul] at hred
  simp only [value, finalExponentiation, Fp12.powNat_eq_pow, div_pow]
  apply (div_eq_div_iff (pow_ne_zero _ hR0.2) (pow_ne_zero _ hT0.2)).mpr
  simpa only [state, finalExponentiation, Fp12.powNat_eq_pow] using hred

/-- The formal value at the identity source is normalized to one. -/
theorem value_of_inf {n : Nat} (hn : n ≠ 0) {R P : EmbeddedPoint}
    (hR : OnCurve R) (hpar : TwistParity R) (hri : R.inf = true)
    (hP : OnCurve P) (hi : P.inf = false) (hsep : Tate.Separated P) : value n R P hP hi = 1 := by
  have hcursor := state_group hn hR P
  rw [toAmbient_inf hR hri, nsmul_zero] at hcursor
  have hci := Tate.inf_of_toAmbient_zero (state_onCurve n hR P) hcursor
  have hinv := miller_global_fractionalIdeal hR P hn
  change principalFractional (state n R P).numerator * pointFractional (state n R P).point =
    principalFractional (state n R P).denominator * pointFractional R ^ n at hinv
  have hone : ((1 : Ideal CoordinateRing) : FractionalIdeal NonZeroDivisors FunctionField) = 1 :=
    FractionalIdeal.coeIdeal_eq_one.mpr rfl
  simp only [pointFractional, pointIdeal, hri, hci, ↓reduceIte, hone, one_pow, mul_one] at hinv
  have hsym := state_symmetric n hpar P
  have he := reduced_evaluate_eq_of_ideal_eq hP hi (state_nonzero n R P).1 hsym.1 hsym.2
    (principal_eq_of_fractional_eq hinv)
  have h0 := MillerState.run_evaluate_nonzero_at hR hpar hP hi hsep n P
  unfold value
  simp only [finalExponentiation, Fp12.powNat_eq_pow, div_pow] at he ⊢
  rw [he]
  dsimp only [state]
  exact div_self (pow_ne_zero _ h0.2)

/-- Denominator elimination connects the generic reduced function to the real loop. -/
theorem value_eq_millerLoop {n : Nat} (hn : n ≠ 0) {R P : EmbeddedPoint}
    (hR : OnCurve R) (hpar : TwistParity R)
    (hP : OnCurve P) (hi : P.inf = false) (hsep : Tate.Separated P) :
    value n R P hP hi = finalExponentiation (millerLoop n R P) := by
  by_cases hri : R.inf = true
  · rw [value_of_inf hn hR hpar hri hP hi hsep, millerLoop_inf_left n R P hri, finalExponentiation_one]
    rfl
  · have hrf := Bool.eq_false_iff.mpr hri
    rw [MillerState.millerLoop_eq_evaluate R P hP hrf hi]
    have h0 := MillerState.run_evaluate_nonzero_at hR hpar hP hi hsep n P
    have hd := MillerState.run_denominator_conjugate hpar hP hi hsep.1 n n.log2
      (s := MillerState.initial R) hpar
      (by simpa only [MillerState.initial, map_one] using PairingTower.conjugate_one)
    have hdred := finalExponentiation_of_conjugate_eq h0.2 hd
    change finalExponentiation (evaluate P hP hi (state n R P).numerator /
      evaluate P hP hi (state n R P).denominator) = _
    simp only [finalExponentiation, Fp12.powNat_eq_pow, div_pow] at hdred ⊢
    dsimp only [state]
    rw [hdred, div_one]

end ReducedMiller
end EthLib.Cryptography.Bls.Embedded
