import EthLib.Cryptography.Proofs.Bls.PairingEvaluation
import EthLib.Cryptography.Proofs.Bls.PairingLineSymmetry

namespace EthLib.Cryptography.Bls.Embedded
open Polynomial WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

/-- A nonvertical affine line whose cubic intersection with the ambient curve splits,
with multiplicity. Tangents are included. -/
structure SplitLine where
  slope : Fp12
  offset : Fp12
  x₁ : Fp12
  x₂ : Fp12
  x₃ : Fp12
  factor : X ^ 3 + C (4 : Fp12) - (C slope * X + C offset) ^ 2 =
    (X - C x₁) * (X - C x₂) * (X - C x₃)

namespace SplitLine

theorem linear_norm (s : SplitLine) (d e : Fp12) :
    (d * s.x₁ + e) * (d * s.x₂ + e) * (d * s.x₃ + e) =
      e ^ 3 + d * e ^ 2 * s.slope ^ 2 - 2 * d ^ 2 * e * s.slope * s.offset +
        d ^ 3 * (s.offset ^ 2 - 4) := by
  have hf := s.factor
  ring_nf at hf
  have h0 := congrArg (fun p : Fp12[X] => p.coeff 0) hf
  have h1 := congrArg (fun p : Fp12[X] => p.coeff 1) hf
  have h2 := congrArg (fun p : Fp12[X] => p.coeff 2) hf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_mul_C, coeff_X_pow, coeff_C,
    coeff_neg, coeff_X] at h0 h1 h2
  norm_num at h0 h1 h2
  linear_combination d ^ 3 * h0 - d ^ 2 * e * h1 + d * e ^ 2 * h2



/-- Reciprocity for two split nonvertical lines, including tangent multiplicities. -/
theorem reciprocity (s t : SplitLine) :
    ((s.slope - t.slope) * s.x₁ + (s.offset - t.offset)) *
      ((s.slope - t.slope) * s.x₂ + (s.offset - t.offset)) *
      ((s.slope - t.slope) * s.x₃ + (s.offset - t.offset)) =
    -(((t.slope - s.slope) * t.x₁ + (t.offset - s.offset)) *
      ((t.slope - s.slope) * t.x₂ + (t.offset - s.offset)) *
      ((t.slope - s.slope) * t.x₃ + (t.offset - s.offset))) := by
  rw [linear_norm, linear_norm]
  ring

/-- Reciprocity with a vertical section through a point on the curve. -/
theorem vertical_norm (s : SplitLine) {x y : Fp12} (hy : y ^ 2 = x ^ 3 + 4) :
    (s.x₁ - x) * (s.x₂ - x) * (s.x₃ - x) =
      (s.slope * x + s.offset - y) * (s.slope * x + s.offset + y) := by
  have h := s.linear_norm 1 (-x)
  simp only [one_mul, ← sub_eq_add_neg] at h
  linear_combination h + hy

noncomputable def ofChord (x t y m : Fp12)
    (hf : ambientCurve.addPolynomial x y m =
      -((X - C x) * (X - C t) * (X - C (ambientCurve.addX x t m)))) : SplitLine where
  slope := m
  offset := y - m * x
  x₁ := x
  x₂ := t
  x₃ := ambientCurve.addX x t m
  factor := by
    rw [← neg_inj] at hf
    rw [neg_neg] at hf
    rw [← hf]
    simp [addPolynomial, WeierstrassCurve.Affine.polynomial, ambientCurve, linePolynomial]
    ring

noncomputable def secant {T R : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (ht : T.inf = false) (hr : R.inf = false) (hx : T.x ≠ R.x) : SplitLine :=
  ofChord T.x R.x T.y (Line.addSlope T.x T.y R.x R.y) (by
    have h := millerAdd_intersection hT hR ht hr hx T
    rw [millerAdd_fst_of_nonvertical ht hr hx] at h
    exact h)

noncomputable def tangent {T : EmbeddedPoint} (hT : OnCurve T)
    (ht : T.inf = false) (hy : T.y ≠ 0) : SplitLine :=
  ofChord T.x T.x T.y (Line.tangentSlope T.x T.y) (by
    have h := millerDouble_intersection hT ht hy T
    rw [millerDouble_fst_of_nonvertical ht hy, pow_two] at h
    exact h)



def point₁ (s : SplitLine) : EmbeddedPoint := ⟨s.x₁, s.slope * s.x₁ + s.offset, false⟩
def point₂ (s : SplitLine) : EmbeddedPoint := ⟨s.x₂, s.slope * s.x₂ + s.offset, false⟩
def point₃ (s : SplitLine) : EmbeddedPoint := ⟨s.x₃, s.slope * s.x₃ + s.offset, false⟩

private theorem onCurve_of_root (s : SplitLine) (x : Fp12)
    (hx : (x - s.x₁) * (x - s.x₂) * (x - s.x₃) = 0) :
    OnCurve (⟨x, s.slope * x + s.offset, false⟩ : EmbeddedPoint) := by
  intro _
  have h := congrArg (Polynomial.eval x) s.factor
  simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X, hx] at h
  change (s.slope * x + s.offset) ^ 2 = x ^ 3 + 4
  linear_combination -h

theorem point₁_onCurve (s : SplitLine) : OnCurve s.point₁ :=
  s.onCurve_of_root s.x₁ (by simp)
theorem point₂_onCurve (s : SplitLine) : OnCurve s.point₂ :=
  s.onCurve_of_root s.x₂ (by simp)
theorem point₃_onCurve (s : SplitLine) : OnCurve s.point₃ :=
  s.onCurve_of_root s.x₃ (by simp)

/-- Product of evaluation at the three intersections, counted with multiplicity. -/
noncomputable def norm (s : SplitLine) : CoordinateRing →*₀ Fp12 where
  toFun f := evaluate s.point₁ s.point₁_onCurve rfl f *
    evaluate s.point₂ s.point₂_onCurve rfl f * evaluate s.point₃ s.point₃_onCurve rfl f
  map_zero' := by simp
  map_one' := by simp
  map_mul' f g := by simp only [map_mul]; ring

@[simp] theorem norm_XClass (s : SplitLine) (x : Fp12) :
    s.norm (XClass ambientCurve x) = (s.x₁ - x) * (s.x₂ - x) * (s.x₃ - x) := by
  simp [norm, point₁, point₂, point₃]

@[simp] theorem norm_YClass (s : SplitLine) (f : Fp12[X]) :
    s.norm (YClass ambientCurve f) =
      (s.slope * s.x₁ + s.offset - f.eval s.x₁) *
      (s.slope * s.x₂ + s.offset - f.eval s.x₂) *
      (s.slope * s.x₃ + s.offset - f.eval s.x₃) := by
  simp [norm, point₁, point₂, point₃]

/-- The normalized value of the evaluation line at a source point. Its value
at infinity is its leading coefficient after the common sign is removed. -/
def weight (s : SplitLine) (T : EmbeddedPoint) : Fp12 :=
  if T.inf then 1 else s.slope * T.x + s.offset - T.y

theorem norm_line (s t : SplitLine) :
    s.norm (YClass ambientCurve (C t.slope * X + C t.offset)) =
      (s.slope * t.x₁ + s.offset - (t.slope * t.x₁ + t.offset)) *
      (s.slope * t.x₂ + s.offset - (t.slope * t.x₂ + t.offset)) *
      (s.slope * t.x₃ + s.offset - (t.slope * t.x₃ + t.offset)) := by
  rw [norm_YClass]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  have h := s.reciprocity t
  linear_combination h

theorem norm_chord (s : SplitLine) (x t y z m : Fp12)
    (hf : ambientCurve.addPolynomial x y m =
      -((X - C x) * (X - C t) * (X - C (ambientCurve.addX x t m))))
    (hz : m * (t - x) = z - y) :
    s.norm (YClass ambientCurve (linePolynomial x y m)) =
      (s.slope * x + s.offset - y) * (s.slope * t + s.offset - z) *
      (s.slope * (ambientCurve.addX x t m) + s.offset + ambientCurve.addY x t y m) := by
  have hp : linePolynomial x y m = C m * X + C (y - m * x) := by
    simp only [linePolynomial, map_sub, map_mul]
    ring
  rw [hp]
  have h := s.norm_line (ofChord x t y m hf)
  dsimp only [ofChord] at h
  rw [h]
  have hz' : z = m * (t - x) + y := by linear_combination -hz
  rw [hz']
  simp only [ambient_addX, ambient_addY]
  ring

theorem norm_vertical (s : SplitLine) {T : EmbeddedPoint} (hT : OnCurve T)
    (ht : T.inf = false) :
    s.norm (vertical T) = (s.slope * T.x + s.offset - T.y) *
      (s.slope * T.x + s.offset + T.y) := by
  simp only [vertical, ht, Bool.false_eq_true, ↓reduceIte, norm_XClass]
  exact s.vertical_norm (hT ht)

theorem norm_double (s : SplitLine) {T : EmbeddedPoint} (hT : OnCurve T)
    (P : EmbeddedPoint) :
    s.norm (doubleLine T) * s.weight (millerDouble T P).1 =
      s.weight T * s.weight T * s.norm (vertical (millerDouble T P).1) := by
  by_cases ht : T.inf = true
  · simp [doubleLine, millerDouble, ht, vertical, weight]
  · have htf := Bool.eq_false_iff.mpr ht
    by_cases hy : T.y = 0
    · simp only [doubleLine, millerDouble, if_neg ht, hy, Fp12.zero_eq_zero,
        beq_self_eq_true, ↓reduceIte, weight, vertical, map_one, mul_one, sub_zero]
      have hn := s.vertical_norm (hT htf)
      simpa only [hy, sub_zero, add_zero, norm_XClass] using hn
    · have hf := millerDouble_intersection hT htf hy P
      rw [millerDouble_fst_of_nonvertical htf hy, pow_two] at hf
      have hn := s.norm_chord T.x T.x T.y T.y (Line.tangentSlope T.x T.y) hf (by simp)
      have hv := s.norm_vertical (millerDouble_onCurve hT P)
        (by rw [millerDouble_fst_of_nonvertical htf hy])
      simp only [doubleLine, if_neg ht, if_neg hy]
      rw [hn, hv, millerDouble_fst_of_nonvertical htf hy]
      simp only [weight, ht, Bool.false_eq_true, ↓reduceIte]
      ring


theorem norm_add (s : SplitLine) {T R : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (P : EmbeddedPoint) :
    s.norm (addLine T R) * s.weight (millerAdd T R P).1 =
      s.weight T * s.weight R * s.norm (addDenominator T R P) := by
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
            Bool.false_or, Bool.false_eq_true, ↓reduceIte] using s.norm_double hT P
        · have hnY := (Y_eq_of_X_eq ((ambient_equation _ _).mpr (hT htf))
            ((ambient_equation _ _).mpr (hR hrf)) hx).resolve_left hy
          simp only [negY, ambientCurve, zero_mul, sub_zero] at hnY
          have hn := s.vertical_norm (hR hrf)
          simp only [addLine, addDenominator, htf, hrf, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
            millerAdd, beq_iff_eq, hx, hy, weight, vertical, map_one, mul_one]
          simpa only [hx, hnY, sub_neg_eq_add, norm_XClass, mul_comm] using hn

      · have hf := millerAdd_intersection hT hR htf hrf hx P
        rw [millerAdd_fst_of_nonvertical htf hrf hx] at hf
        have hz : Line.addSlope T.x T.y R.x R.y * (R.x - T.x) = R.y - T.y :=
          addSlope_mul_sub (y := T.y) (z := R.y) hx
        have hn := s.norm_chord T.x R.x T.y R.y (Line.addSlope T.x T.y R.x R.y) hf hz
        have hv := s.norm_vertical (millerAdd_onCurve hT hR P)
          (by rw [millerAdd_fst_of_nonvertical htf hrf hx])
        simp only [addLine, addDenominator, ht, hr, hx, ↓reduceIte,
          Bool.false_or, Bool.false_eq_true]
        rw [hn, hv, millerAdd_fst_of_nonvertical htf hrf hx]
        simp only [weight, ht, hr, Bool.false_eq_true, ↓reduceIte]
        ring

end SplitLine
end EthLib.Cryptography.Bls.Embedded
