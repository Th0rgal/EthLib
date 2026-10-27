import EthLib.Cryptography.Proofs.Bls.PairingMillerReciprocity
import EthLib.Cryptography.Proofs.Bls.PairingNegative

/-!
# Proofs: norms of vertical lines

A vertical line `x - c` vanishes at a point and its negative.

Its norm at a point is computed for each kind of Miller line: vertical, chord, tangent and sum.

These norms make the reciprocity argument close for the full Miller function.
-/

namespace EthLib.Cryptography.Bls.Embedded
open Polynomial WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
namespace VerticalNorm

noncomputable def norm (P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false) :
    CoordinateRing →*₀ Fp12 where
  toFun f := evaluate P hP hi f * evaluate (negate P) (negate_onCurve hP) hi f
  map_zero' := by simp
  map_one' := by simp
  map_mul' f g := by simp only [map_mul]; ring

def weight (P T : EmbeddedPoint) : Fp12 := if T.inf then 1 else T.x - P.x

theorem norm_XClass (P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false) (x : Fp12) :
    norm P hP hi (XClass ambientCurve x) = (x - P.x) ^ 2 := by
  simp only [norm, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, evaluate_XClass, negate]
  ring

theorem norm_vertical (P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false)
    (T : EmbeddedPoint) : norm P hP hi (vertical T) = weight P T ^ 2 := by
  by_cases ht : T.inf = true
  · simp [vertical, weight, ht]
  · simp only [vertical, weight, if_neg ht, norm_XClass]

theorem norm_chord (P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false)
    (x t y m : Fp12)
    (hf : ambientCurve.addPolynomial x y m =
      -((X - C x) * (X - C t) * (X - C (ambientCurve.addX x t m)))) :
    norm P hP hi (YClass ambientCurve (linePolynomial x y m)) =
      (x - P.x) * (t - P.x) * (ambientCurve.addX x t m - P.x) := by
  have h := (SplitLine.ofChord x t y m hf).vertical_norm (hP hi)
  dsimp only [SplitLine.ofChord] at h
  simp only [norm, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, evaluate_YClass,
    negate, linePolynomial, eval_add, eval_mul, eval_sub, eval_C, eval_X]
  linear_combination -h

theorem norm_double (P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false)
    {T : EmbeddedPoint} (hT : OnCurve T) (U : EmbeddedPoint) :
    norm P hP hi (doubleLine T) * weight P (millerDouble T U).1 =
      weight P T * weight P T * norm P hP hi (vertical (millerDouble T U).1) := by
  by_cases ht : T.inf = true
  · simp [doubleLine, millerDouble, ht, vertical, weight]
  · have htf := Bool.eq_false_iff.mpr ht
    by_cases hy : T.y = 0
    · simp only [doubleLine, millerDouble, if_neg ht, hy, Fp12.zero_eq_zero,
        beq_self_eq_true, ↓reduceIte, weight, vertical, map_one, mul_one, norm_XClass, pow_two]
    · have hf := millerDouble_intersection hT htf hy U
      rw [millerDouble_fst_of_nonvertical htf hy, pow_two] at hf
      simp only [doubleLine, if_neg ht, if_neg hy]
      rw [norm_chord P hP hi _ _ _ _ hf, norm_vertical,
        millerDouble_fst_of_nonvertical htf hy]
      simp only [weight, ht, Bool.false_eq_true, ↓reduceIte]
      ring

theorem norm_add (P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false)
    {T R : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R) (U : EmbeddedPoint) :
    norm P hP hi (addLine T R) * weight P (millerAdd T R U).1 =
      weight P T * weight P R * norm P hP hi (addDenominator T R U) := by
  by_cases ht : T.inf = true
  · simp [addLine, addDenominator, millerAdd, ht, weight]
  · by_cases hr : R.inf = true
    · simp [addLine, addDenominator, millerAdd, ht, hr, weight]
    · have htf := Bool.eq_false_iff.mpr ht
      have hrf := Bool.eq_false_iff.mpr hr
      by_cases hx : T.x = R.x
      · by_cases hy : T.y = R.y
        · have he : T = R := by cases T; cases R; simp_all
          subst R
          simpa only [millerAdd_self_eq_millerDouble, addDenominator, addLine, ht,
            Bool.false_or, Bool.false_eq_true, ↓reduceIte] using norm_double P hP hi hT U
        · simp only [addLine, addDenominator, htf, hrf, Bool.false_or, Bool.false_eq_true,
            ↓reduceIte, millerAdd, beq_iff_eq, hx, hy, weight, vertical,
            map_one, mul_one, norm_XClass, pow_two]
      · have hf := millerAdd_intersection hT hR htf hrf hx U
        rw [millerAdd_fst_of_nonvertical htf hrf hx] at hf
        simp only [addLine, addDenominator, ht, hr, hx, ↓reduceIte,
          Bool.false_or, Bool.false_eq_true]
        rw [norm_chord P hP hi _ _ _ _ hf, norm_vertical,
          millerAdd_fst_of_nonvertical htf hrf hx]
        simp only [weight, ht, hr, Bool.false_eq_true, ↓reduceIte]
        ring

noncomputable def millerNorm (P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false) :
    MillerNorm where
  norm := norm P hP hi
  weight := weight P
  weight_inf T ht := by simp [weight, ht]
  double _ hT U := norm_double P hP hi hT U
  add _ _ hT hR U := norm_add P hP hi hT hR U

end VerticalNorm
end EthLib.Cryptography.Bls.Embedded
