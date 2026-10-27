import EthLib.Cryptography.Proofs.Bls.PairingConjugation

/-!
# Evaluation support for the concrete Miller functions

The base curve has no finite point with y=0: -4 is not a cube in Fp,
verified using the existing kernel-checked modular exponentiation tool.
Conjugation then separates embedded G1 from every finite untwisted cursor.
-/
namespace EthLib.Cryptography.Bls
open PairingTower
open scoped Fp
namespace G1

set_option maxRecDepth 8000 in
set_option exponentiation.threshold 512 in
theorem cube_ne_neg_four (z : ZMod Fp.modulus) : z ^ 3 ≠ -4 := by
  intro h
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide)] at h
    revert h
    decide
  have hc : (-4 : ZMod Fp.modulus) = ((Fp.modulus - 4 : Nat) : ZMod Fp.modulus) := by
    decide
  have hf := ZMod.pow_card_sub_one_eq_one hz
  rw [show Fp.modulus - 1 = 3 * ((Fp.modulus - 1) / 3) by decide, pow_mul, h, hc] at hf
  exact PowMod.natCast_pow_div_ne_one Fp.modulus 384 (Fp.modulus - 4) 3
    (by decide) (by decide) hf

theorem toAffine_y_ne_zero {p : G1} (hp : Valid p) (hi : p.isInfinity = false) :
    (p.toAffine.2 : ZMod Fp.modulus) ≠ 0 := by
  have he := affine_sqrt_witness hp (by change ¬p.isInfinity = true; simp only [hi, Bool.false_eq_true, not_false_eq_true])
  intro hy
  have transport (x y : ZMod Fp.modulus) (he : y * y = x * x * x + 4)
      (hy : y = 0) : False := by
    apply cube_ne_neg_four x
    rw [hy] at he
    linear_combination -he
  exact transport _ _ he hy

end G1
namespace Embedded

theorem ofG1_y_ne_zero {p : G1} (hp : G1.Valid p) (hi : p.isInfinity = false) :
    (ofG1 p).y ≠ 0 := by
  have hy := G1.toAffine_y_ne_zero hp hi
  have he : (ofG1 p).y = fpToFp12 p.toAffine.2 := by simp [ofG1, hi]
  rw [he]
  exact fun h => hy (fpToFp12.injective (h.trans (map_zero _).symm))

/-- A conjugation-odd ordinate cannot equal a nonzero conjugation-fixed ordinate,
even up to sign. This proves disjointness of the relevant affine supports. -/
theorem x_ne_of_twistParity {T P : EmbeddedPoint} (hT : OnCurve T) (hP : OnCurve P)
    (ht : T.inf = false) (hp : P.inf = false) (hpar : TwistParity T)
    (hpy : P.y.conjugate = P.y) (hy : P.y ≠ 0) : P.x ≠ T.x := by
  intro hx
  have hs : P.y ^ 2 = T.y ^ 2 := by rw [hP hp, hT ht, hx]
  have h2 : (2 : Fp12) ≠ 0 := by decide
  apply hy
  apply (mul_eq_zero.mp (show 2 * P.y = 0 from ?_)).resolve_left h2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
  · have hc := congrArg Fp12.conjugate he
    rw [hpy, hpar.2] at hc
    linear_combination he + hc
  · have hc := congrArg Fp12.conjugate he
    rw [hpy, Fp12.conjugate_neg, hpar.2, neg_neg] at hc
    linear_combination he + hc

theorem evaluate_vertical_ne_zero {T P : EmbeddedPoint} (hT : OnCurve T)
    (hP : OnCurve P) (hi : P.inf = false) (hpar : TwistParity T)
    (hpy : P.y.conjugate = P.y) (hy : P.y ≠ 0) :
    evaluate P hP hi (vertical T) ≠ 0 := by
  unfold vertical
  split
  · simpa only [map_one] using (one_ne_zero : (1 : Fp12) ≠ 0)
  · rw [evaluate_XClass]
    exact sub_ne_zero.mpr (x_ne_of_twistParity hT hP (by simp_all) hi hpar hpy hy)

/-- A nonzero fixed ordinate cannot lie on a line whose slope and
intercept are conjugation-negated. -/
theorem evalAt_ne_zero {T P : EmbeddedPoint} (hpar : TwistParity T)
    (hpx : P.x.conjugate = P.x) (hpy : P.y.conjugate = P.y) (hy : P.y ≠ 0)
    {m : Fp12} (hm : m.conjugate = -m) : Line.evalAt T.x T.y m P.x P.y ≠ 0 := by
  intro he
  have hc := congrArg Fp12.conjugate he
  simp only [Line.evalAt, Fp12.conjugate_sub, Fp12.conjugate_mul,
    hpar.1, hpar.2, hpx, hpy, hm, PairingTower.conjugate_zero] at hc
  unfold Line.evalAt at he
  apply hy
  have hh : 2 * P.y = 0 := by linear_combination he + hc
  exact (mul_eq_zero.mp hh).resolve_left (by decide)

theorem millerDouble_value_ne_zero {T P : EmbeddedPoint} (hT : OnCurve T)
    (hP : OnCurve P) (hi : P.inf = false) (hpar : TwistParity T)
    (hpx : P.x.conjugate = P.x) (hpy : P.y.conjugate = P.y) (hy : P.y ≠ 0) :
    (millerDouble T P).2 ≠ 0 := by
  unfold millerDouble
  split
  · exact one_ne_zero
  · rename_i ht
    split
    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      exact sub_ne_zero.mpr (x_ne_of_twistParity hT hP (Bool.eq_false_iff.mpr ht) hi hpar hpy hy)
    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      exact evalAt_ne_zero hpar hpx hpy hy (tangentSlope_conjugate hpar)

theorem millerAdd_value_ne_zero {T R P : EmbeddedPoint} (hT : OnCurve T)
    (hP : OnCurve P) (hi : P.inf = false) (hpar : TwistParity T) (hrpar : TwistParity R)
    (hpx : P.x.conjugate = P.x) (hpy : P.y.conjugate = P.y) (hy : P.y ≠ 0) :
    (millerAdd T R P).2 ≠ 0 := by
  unfold millerAdd
  split
  · exact one_ne_zero
  · rename_i ht
    split
    · exact one_ne_zero
    · split
      · split
        · exact millerDouble_value_ne_zero hT hP hi hpar hpx hpy hy
        · simp only [hi, Bool.false_eq_true, ↓reduceIte]
          exact sub_ne_zero.mpr (x_ne_of_twistParity hT hP (Bool.eq_false_iff.mpr ht) hi hpar hpy hy)
      · simp only [hi, Bool.false_eq_true, ↓reduceIte]
        exact evalAt_ne_zero hpar hpx hpy hy (addSlope_conjugate hpar hrpar)

theorem evaluate_addDenominator_ne_zero {T R P : EmbeddedPoint} (hT : OnCurve T)
    (hR : OnCurve R) (hP : OnCurve P) (hi : P.inf = false) (hpar : TwistParity T)
    (hrpar : TwistParity R) (hpy : P.y.conjugate = P.y) (hy : P.y ≠ 0) :
    evaluate P hP hi (addDenominator T R P) ≠ 0 := by
  unfold addDenominator
  split
  · simpa only [map_one] using (one_ne_zero : (1 : Fp12) ≠ 0)
  · exact evaluate_vertical_ne_zero (millerAdd_onCurve hT hR P) hP hi
      (millerAdd_twistParity hpar hrpar P) hpy hy

namespace MillerState

/-- Both full Miller-function components have nonzero values at the
actual separated evaluation support. -/
theorem run_evaluate_nonzero {R P : EmbeddedPoint} (hR : OnCurve R)
    (hrpar : TwistParity R) (hP : OnCurve P) (hi : P.inf = false)
    (hpx : P.x.conjugate = P.x) (hpy : P.y.conjugate = P.y) (hy : P.y ≠ 0)
    (n i : Nat) {s : MillerState} (hs : OnCurve s.point) (hspar : TwistParity s.point)
    (hn : evaluate P hP hi s.numerator ≠ 0) (hd : evaluate P hP hi s.denominator ≠ 0) :
    evaluate P hP hi (run n R P i s).numerator ≠ 0 ∧
      evaluate P hP hi (run n R P i s).denominator ≠ 0 := by
  induction i generalizing s with
  | zero => exact ⟨hn, hd⟩
  | succ i ih =>
    have hds : OnCurve (s.double P).point := double_onCurve hs P
    have hdpar : TwistParity (s.double P).point := millerDouble_twistParity hspar P
    have hdn : evaluate P hP hi (s.double P).numerator ≠ 0 := by
      simp only [double, map_mul, evaluate_doubleLine]
      exact mul_ne_zero (mul_ne_zero hn hn) (millerDouble_value_ne_zero hs hP hi hspar hpx hpy hy)
    have hdd : evaluate P hP hi (s.double P).denominator ≠ 0 := by
      simp only [double, map_mul]
      exact mul_ne_zero (mul_ne_zero hd hd)
        (evaluate_vertical_ne_zero hds hP hi hdpar hpy hy)
    simp only [run]
    split
    · apply ih (add_onCurve hds hR P) (millerAdd_twistParity hdpar hrpar P)
      · simp only [add, map_mul, evaluate_addLine]
        exact mul_ne_zero hdn (millerAdd_value_ne_zero hds hP hi hdpar hrpar hpx hpy hy)
      · simp only [add, map_mul]
        exact mul_ne_zero hdd (evaluate_addDenominator_ne_zero hds hR hP hi hdpar hrpar hpy hy)
    · exact ih hds hdpar hdn hdd

end MillerState
end Embedded
open Embedded

/-- Evaluation support is discharged for the concrete BLS inputs from validity
and a finite G1 point. Neither subgroup membership nor nonvanishing is assumed. -/
theorem blsMillerState_evaluate_nonzero {p : G1} (hp : G1.Valid p)
    (hi : p.isInfinity = false) {q : G2} (hq : G2.Valid q) :
    let ev := evaluate (ofG1 p) (ofG1_onCurve hp) (by simpa using hi)
    ev (blsMillerState p q).numerator ≠ 0 ∧ ev (blsMillerState p q).denominator ≠ 0 := by
  apply MillerState.run_evaluate_nonzero (ofG2_onCurve hq) (ofG2_twistParity q)
    (ofG1_onCurve hp) (by simpa using hi) (ofG1_conjugate_x p) (ofG1_conjugate_y p)
    (ofG1_y_ne_zero hp hi) _ _ (ofG2_onCurve hq) (ofG2_twistParity q)
  · simpa only [MillerState.initial, map_one] using (one_ne_zero : (1 : Fp12) ≠ 0)
  · simpa only [MillerState.initial, map_one] using (one_ne_zero : (1 : Fp12) ≠ 0)

/-- The concrete executable Miller loop is nonzero on all valid inputs. -/
theorem blsMillerLoop_ne_zero {p : G1} {q : G2} (hp : G1.Valid p) (hq : G2.Valid q) :
    millerLoop blsX (ofG2 q) (ofG1 p) ≠ 0 := by
  by_cases hpi : p.isInfinity = true
  · simp only [millerLoop, ofG1_inf, hpi, Bool.or_true, ↓reduceIte, Fp12.one_eq_one, ne_eq,
      one_ne_zero, not_false_eq_true]
  · by_cases hqi : q.isInfinity = true
    · simp only [millerLoop, ofG2_inf, hqi, Bool.true_or, ↓reduceIte, Fp12.one_eq_one, ne_eq,
        one_ne_zero, not_false_eq_true]
    · rw [MillerState.millerLoop_eq_evaluate _ _ (ofG1_onCurve hp)
        (by simpa using Bool.eq_false_iff.mpr hqi) (by simpa using Bool.eq_false_iff.mpr hpi)]
      exact (blsMillerState_evaluate_nonzero hp (Bool.eq_false_iff.mpr hpi) hq).1

end EthLib.Cryptography.Bls
