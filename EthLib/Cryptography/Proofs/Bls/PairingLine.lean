import EthLib.Cryptography.Proofs.Bls.PairingEmbedding
set_option maxHeartbeats 200000

namespace EthLib.Cryptography.Bls
namespace Embedded

open WeierstrassCurve
open WeierstrassCurve.Affine

/-- The ambient short Weierstrass model used by the Miller formulas. -/
def ambientCurve : Affine Fp12 :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 4 }

/-- In the nonvertical case the implementation's secant slope is Mathlib's
slope on the ambient curve. This is the algebraic line-function bridge used
by each Miller addition step. -/
theorem addSlope_eq_ambientSlope {Rx Ry Tx Ty : Fp12}
    (hx : Rx ≠ Tx) :
    Line.addSlope Rx Ry Tx Ty =
      ambientCurve.slope Rx Tx Ry Ty := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  change (Ty - Ry) * (Tx - Rx)⁻¹ = (Ry - Ty) / (Rx - Tx)
  have hn : Ty - Ry = -(Ry - Ty) := by ring
  have hd : Tx - Rx = -(Rx - Tx) := by ring
  rw [hn, hd, inv_neg, neg_mul_neg, div_eq_mul_inv]

/-- In the nonvertical tangent case the implementation's tangent slope is
Mathlib's tangent slope on the ambient curve. -/
theorem tangentSlope_eq_ambientSlope {Rx Ry : Fp12}
    (hy : Ry ≠ 0) :
    Line.tangentSlope Rx Ry =
      ambientCurve.slope Rx Rx Ry Ry := by
  have h2 : (2 : Fp12) ≠ 0 := by decide
  have hneg : Ry ≠ ambientCurve.negY Rx Ry := by
    simp only [negY, ambientCurve, zero_mul, sub_zero]
    intro h
    apply hy
    have hh : 2 * Ry = 0 := by linear_combination h
    exact (mul_eq_zero.mp hh).resolve_left h2
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  have hc2 : (⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 2)), Fp6.zero⟩ : Fp12) = 2 := by decide
  have hc3 : (⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 3)), Fp6.zero⟩ : Fp12) = 3 := by decide
  simp only [Line.tangentSlope, hc2, hc3, ambientCurve, negY, zero_mul, mul_zero,
    add_zero, sub_zero]
  change 3 * Rx * Rx * (2 * Ry)⁻¹ = 3 * Rx ^ 2 / (Ry - -Ry)
  rw [sub_neg_eq_add, ← two_mul, div_eq_mul_inv]
  rw [mul_assoc 3 Rx Rx, ← pow_two]


/-- The evaluated implementation line is the affine line polynomial at the
Miller evaluation point. -/
theorem evalAt_eq_linePolynomial {Rx Ry m xp yp : Fp12} :
    Line.evalAt Rx Ry m xp yp =
      yp - (m * (xp - Rx) + Ry) := by
  unfold Line.evalAt
  ring

@[simp] theorem ambient_equation (x y : Fp12) :
    ambientCurve.Equation x y ↔ y ^ 2 = x ^ 3 + 4 := by
  simp [WeierstrassCurve.Affine.equation_iff, ambientCurve]

@[simp] theorem ambient_addX (x t m : Fp12) :
    ambientCurve.addX x t m = m * m - x - t := by
  simp [addX, ambientCurve, pow_two]

@[simp] theorem ambient_addY (x t y m : Fp12) :
    ambientCurve.addY x t y m = m * (x - (m * m - x - t)) - y := by
  simp [addY, negY, negAddY, ambientCurve, addX, pow_two]
  ring

/-- Every affine point on this characteristic-p curve is nonsingular. -/
theorem ambient_nonsingular {x y : Fp12} (h : y ^ 2 = x ^ 3 + 4) :
    ambientCurve.Nonsingular x y := by
  rw [nonsingular_iff', ambient_equation]
  refine ⟨h, ?_⟩
  simp only [ambientCurve, zero_mul, mul_zero, add_zero, zero_sub, neg_ne_zero]
  have h2 : (2 : Fp12) ≠ 0 := by decide
  have h3 : (3 : Fp12) ≠ 0 := by decide
  by_cases hy : y = 0
  · left
    apply mul_ne_zero h3
    apply pow_ne_zero
    intro hx
    have hf : (0 : Fp12) = 4 := by simpa [hx, hy] using h
    exact (by decide : (0 : Fp12) ≠ 4) hf
  · exact Or.inr (mul_ne_zero h2 hy)

/-- A valid implementation record determines an actual ambient curve point. -/
def toAmbient (p : EmbeddedPoint) (hp : OnCurve p) : ambientCurve.Point :=
  if hi : p.inf = true then 0
  else .some p.x p.y (ambient_nonsingular (hp (Bool.eq_false_iff.mpr hi)))

/-- The actual line value returned by the implementation is evaluation of
Mathlib's polynomial defining the same affine line. -/
theorem evalAt_eq_polynomial_eval (Rx Ry m xp yp : Fp12) :
    Line.evalAt Rx Ry m xp yp =
      yp - (linePolynomial Rx Ry m).eval xp := by
  simp [linePolynomial, Line.evalAt]
  ring

theorem millerDouble_fst_of_nonvertical {T : EmbeddedPoint}
    (hi : T.inf = false) (hy : T.y ≠ 0) (P : EmbeddedPoint) :
    (millerDouble T P).1 =
      { x := ambientCurve.addX T.x T.x (Line.tangentSlope T.x T.y),
        y := ambientCurve.addY T.x T.x T.y (Line.tangentSlope T.x T.y),
        inf := false } := by
  simp only [millerDouble, hi, Bool.false_eq_true, ↓reduceIte,
    Fp12.zero_eq_zero, beq_iff_eq, hy, ambient_addX, ambient_addY]

theorem millerAdd_fst_of_nonvertical {T R : EmbeddedPoint}
    (hi : T.inf = false) (hj : R.inf = false) (hx : T.x ≠ R.x) (P : EmbeddedPoint) :
    (millerAdd T R P).1 =
      { x := ambientCurve.addX T.x R.x (Line.addSlope T.x T.y R.x R.y),
        y := ambientCurve.addY T.x R.x T.y (Line.addSlope T.x T.y R.x R.y),
        inf := false } := by
  simp only [millerAdd, hi, hj, Bool.false_eq_true, ↓reduceIte,
    beq_iff_eq, hx, ambient_addX, ambient_addY]

/-- Doubling preserves the ambient curve equation in every exceptional branch. -/
theorem millerDouble_onCurve {T : EmbeddedPoint} (hT : OnCurve T)
    (P : EmbeddedPoint) : OnCurve (millerDouble T P).1 := by
  by_cases hi : T.inf = true
  · simpa [millerDouble, hi] using hT
  · have hf : T.inf = false := Bool.eq_false_iff.mpr hi
    by_cases hy : T.y = 0
    · simp [OnCurve, millerDouble, hi, hy]
    · have he := (ambient_equation T.x T.y).mpr (hT hf)
      have hn : T.y ≠ ambientCurve.negY T.x T.y := by
        simp only [negY, ambientCurve, zero_mul, sub_zero]
        intro h
        apply hy
        have hz : 2 * T.y = 0 := by linear_combination h
        exact (mul_eq_zero.mp hz).resolve_left (by decide)
      have ha := equation_add he he (fun h => hn h.2)
      rw [← tangentSlope_eq_ambientSlope hy] at ha
      rw [millerDouble_fst_of_nonvertical hf hy]
      intro _
      exact (ambient_equation _ _).mp ha

/-- Addition preserves the ambient curve equation in every exceptional branch. -/
theorem millerAdd_onCurve {T R : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (P : EmbeddedPoint) : OnCurve (millerAdd T R P).1 := by
  by_cases hi : T.inf = true
  · simpa [millerAdd, hi] using hR
  · by_cases hj : R.inf = true
    · simpa [millerAdd, hi, hj] using hT
    · by_cases hx : T.x = R.x
      · by_cases hy : T.y = R.y
        · simpa [millerAdd, hi, hj, hx, hy] using millerDouble_onCurve hT P
        · simp [OnCurve, millerAdd, hi, hj, hx, hy]
      · have ht := (ambient_equation T.x T.y).mpr (hT (Bool.eq_false_iff.mpr hi))
        have hr := (ambient_equation R.x R.y).mpr (hR (Bool.eq_false_iff.mpr hj))
        have ha := equation_add ht hr (fun h => hx h.1)
        rw [← addSlope_eq_ambientSlope hx] at ha
        rw [millerAdd_fst_of_nonvertical (Bool.eq_false_iff.mpr hi)
          (Bool.eq_false_iff.mpr hj) hx]
        intro _
        exact (ambient_equation _ _).mp ha

open Polynomial in
/-- The cubic intersection polynomial of an actual nonvertical addition
step has precisely the three expected x-coordinates as roots, counted
with multiplicity. This is the polynomial input to the line divisor law. -/
theorem millerAdd_intersection {T R : EmbeddedPoint}
    (hT : OnCurve T) (hR : OnCurve R) (hi : T.inf = false) (hj : R.inf = false)
    (hx : T.x ≠ R.x) (P : EmbeddedPoint) :
    ambientCurve.addPolynomial T.x T.y (Line.addSlope T.x T.y R.x R.y) =
      -((X - C T.x) * (X - C R.x) * (X - C (millerAdd T R P).1.x)) := by
  have he := addPolynomial_slope
    ((ambient_equation T.x T.y).mpr (hT hi))
    ((ambient_equation R.x R.y).mpr (hR hj)) (fun h => hx h.1)
  rw [← addSlope_eq_ambientSlope hx] at he
  rw [millerAdd_fst_of_nonvertical hi hj hx]
  exact he

open Polynomial in
/-- At a nonvertical tangent step the old x-coordinate occurs twice in
the intersection polynomial, as required by the doubling divisor law. -/
theorem millerDouble_intersection {T : EmbeddedPoint}
    (hT : OnCurve T) (hi : T.inf = false) (hy : T.y ≠ 0) (P : EmbeddedPoint) :
    ambientCurve.addPolynomial T.x T.y (Line.tangentSlope T.x T.y) =
      -((X - C T.x) ^ 2 * (X - C (millerDouble T P).1.x)) := by
  have ht := (ambient_equation T.x T.y).mpr (hT hi)
  have hn : T.y ≠ ambientCurve.negY T.x T.y := by
    simp only [negY, ambientCurve, zero_mul, sub_zero]
    intro h
    apply hy
    have hz : 2 * T.y = 0 := by linear_combination h
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have he := addPolynomial_slope ht ht (fun h => hn h.2)
  rw [← tangentSlope_eq_ambientSlope hy] at he
  rw [millerDouble_fst_of_nonvertical hi hy, pow_two]
  exact he

end Embedded
end EthLib.Cryptography.Bls
