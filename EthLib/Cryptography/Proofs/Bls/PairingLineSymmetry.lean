import EthLib.Cryptography.Proofs.Bls.PairingDivisor

/-!
# Proofs: the chord does not depend on the order of its points

The line through `T` and `R` is the line through `R` and `T`.

For finite points, the addition step gives the same cursor either way.
-/

namespace EthLib.Cryptography.Bls.Embedded
open Polynomial WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

theorem addSlope_swap (x y t z : Fp12) :
    Line.addSlope x y t z = Line.addSlope t z x y := by
  change (z - y) * (t - x)⁻¹ = (y - z) * (x - t)⁻¹
  have hd : t - x = -(x - t) := by ring
  rw [hd, inv_neg]
  ring

theorem addSlope_mul_sub {x y t z : Fp12} (h : x ≠ t) :
    Line.addSlope x y t z * (t - x) = z - y := by
  change ((z - y) / (t - x)) * (t - x) = z - y
  exact div_mul_cancel₀ _ (sub_ne_zero.mpr h.symm)

theorem linePolynomial_swap {x y t z : Fp12} (h : x ≠ t) :
    linePolynomial x y (Line.addSlope x y t z) =
      linePolynomial t z (Line.addSlope t z x y) := by
  rw [← addSlope_swap x y t z]
  have hs := congrArg (C : Fp12 → Fp12[X]) (addSlope_mul_sub (y := y) (z := z) h)
  simp only [map_mul, map_sub] at hs
  unfold linePolynomial
  linear_combination hs

theorem addLine_swap (T R : EmbeddedPoint) : addLine T R = addLine R T := by
  by_cases ht : T.inf = true
  · by_cases hr : R.inf = true <;> simp [addLine, ht, hr]
  · by_cases hr : R.inf = true
    · simp [addLine, ht, hr]
    · by_cases hx : T.x = R.x
      · by_cases hy : T.y = R.y
        · have he : T = R := by cases T; cases R; simp_all
          subst R
          rfl
        · have hy' : R.y ≠ T.y := Ne.symm hy
          simp [addLine, ht, hr, hx, hy, hy']
      · have hx' : R.x ≠ T.x := Ne.symm hx
        simp only [addLine, ht, hr, hx, hx', ↓reduceIte]
        rw [linePolynomial_swap hx]

/-- Finite-input cursor symmetry. Infinity records may have distinct unused coordinates. -/
theorem millerAdd_fst_swap_of_finite {T R : EmbeddedPoint}
    (ht : T.inf = false) (hr : R.inf = false) (P : EmbeddedPoint) :
    (millerAdd T R P).1 = (millerAdd R T P).1 := by
  by_cases hx : T.x = R.x
  · by_cases hy : T.y = R.y
    · have he : T = R := by cases T; cases R; simp_all
      subst R
      rfl
    · have hy' : R.y ≠ T.y := Ne.symm hy
      simp [millerAdd, ht, hr, hx, hy, hy']
  · rw [millerAdd_fst_of_nonvertical ht hr hx,
      millerAdd_fst_of_nonvertical hr ht (Ne.symm hx),
      ← addSlope_swap T.x T.y R.x R.y]
    have hs := addSlope_mul_sub (y := T.y) (z := R.y) hx
    simp only [ambient_addX, ambient_addY]
    apply congrArg₂ (fun x y => (⟨x, y, false⟩ : EmbeddedPoint))
    · ring
    · linear_combination -hs

theorem addDenominator_swap (T R P : EmbeddedPoint) :
    addDenominator T R P = addDenominator R T P := by
  by_cases ht : T.inf = true
  · by_cases hr : R.inf = true <;> simp [addDenominator, ht, hr]
  · by_cases hr : R.inf = true
    · simp [addDenominator, ht, hr]
    · simp only [addDenominator, Bool.eq_false_iff.mpr ht, Bool.eq_false_iff.mpr hr,
        Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      rw [millerAdd_fst_swap_of_finite (Bool.eq_false_iff.mpr ht) (Bool.eq_false_iff.mpr hr)]

end EthLib.Cryptography.Bls.Embedded
