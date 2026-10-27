import EthLib.Cryptography.Proofs.Bls.PairingGroup

/-!
# Affine ideal identities for the implementation's Miller lines

The identities here are in the actual coordinate ring of y²=x³+4, using
Mathlib's proved chord/tangent ideal identities (Affine/Point.lean,
`CoordinateRing.XYIdeal_mul_XYIdeal` and `XYIdeal_neg_mul`). They retain
vertical denominators explicitly. The corresponding order at infinity
and evaluation reciprocity are separate pairing dependencies.
-/
namespace EthLib.Cryptography.Bls.Embedded
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing
open Polynomial

abbrev CoordinateRing := ambientCurve.CoordinateRing

/-- Ideal of a finite implementation point; the affine ideal of infinity
is the unit ideal, since infinity is absent from this affine chart. -/
noncomputable def pointIdeal (T : EmbeddedPoint) : Ideal CoordinateRing :=
  if T.inf then 1 else XYIdeal ambientCurve T.x (C T.y)

/-- The vertical function through a finite point, or 1 at infinity. -/
noncomputable def vertical (T : EmbeddedPoint) : CoordinateRing :=
  if T.inf then 1 else XClass ambientCurve T.x

/-- The exact line chosen by the implementation's doubling branches. -/
noncomputable def doubleLine (T : EmbeddedPoint) : CoordinateRing :=
  if T.inf then 1 else if T.y = 0 then XClass ambientCurve T.x
  else YClass ambientCurve (linePolynomial T.x T.y (Line.tangentSlope T.x T.y))

/-- The exact line chosen by the implementation's addition branches. -/
noncomputable def addLine (T R : EmbeddedPoint) : CoordinateRing :=
  if T.inf then 1 else if R.inf then 1 else if T.x = R.x then
    if T.y = R.y then doubleLine T else XClass ambientCurve T.x
  else YClass ambientCurve (linePolynomial T.x T.y (Line.addSlope T.x T.y R.x R.y))

/-- Denominator of the full addition function. Identity additions use 1,
not the vertical function through the unchanged finite input. -/
noncomputable def addDenominator (T R P : EmbeddedPoint) : CoordinateRing :=
  if T.inf || R.inf then 1 else vertical (millerAdd T R P).1

/-- Principal ideal of a coordinate-ring function. -/
noncomputable def principal (f : CoordinateRing) : Ideal CoordinateRing := Ideal.span {f}

@[simp] theorem principal_one : principal 1 = 1 := by
  simp [principal]

@[simp] theorem principal_mul (f g : CoordinateRing) :
    principal (f * g) = principal f * principal g := by
  exact (Ideal.span_singleton_mul_span_singleton f g).symm

theorem vertical_ne_zero (T : EmbeddedPoint) : vertical T ≠ 0 := by
  unfold vertical
  split
  · exact one_ne_zero
  · exact XClass_ne_zero _

theorem doubleLine_ne_zero (T : EmbeddedPoint) : doubleLine T ≠ 0 := by
  unfold doubleLine
  split
  · exact one_ne_zero
  · split
    · exact XClass_ne_zero _
    · exact YClass_ne_zero _

theorem addLine_ne_zero (T R : EmbeddedPoint) : addLine T R ≠ 0 := by
  unfold addLine
  split
  · exact one_ne_zero
  · split
    · exact one_ne_zero
    · split
      · split
        · exact doubleLine_ne_zero T
        · exact XClass_ne_zero _
      · exact YClass_ne_zero _

/-- Concrete doubling ideal identity, including infinity and vertical tangents.
Equivalently, on the affine chart, (l/v) represents 2[T]-[2T]. -/
theorem millerDouble_ideal {T : EmbeddedPoint} (hT : OnCurve T) (P : EmbeddedPoint) :
    principal (vertical (millerDouble T P).1) * (pointIdeal T * pointIdeal T) =
      principal (doubleLine T) * pointIdeal (millerDouble T P).1 := by
  by_cases hi : T.inf = true
  · simp only [millerDouble, if_pos hi, vertical, pointIdeal, doubleLine,
      principal_one, mul_one]
  · have hf := Bool.eq_false_iff.mpr hi
    have ht := (ambient_equation _ _).mpr (hT hf)
    by_cases hy : T.y = 0
    · have hn := XYIdeal_neg_mul (ambient_nonsingular (hT hf))
      simp only [ambientCurve, negY, zero_mul, sub_zero, hy, neg_zero] at hn
      simp only [millerDouble, if_neg hi, Fp12.zero_eq_zero, hy, beq_self_eq_true,
        ↓reduceIte, vertical, pointIdeal, doubleLine, principal_one, one_mul, mul_one]
      exact hn
    · have he := XYIdeal_mul_XYIdeal ht ht (fun h => y_ne_negY hy h.2)
      rw [← tangentSlope_eq_ambientSlope hy] at he
      rw [millerDouble_fst_of_nonvertical hf hy]
      simp only [vertical, pointIdeal, doubleLine, if_neg hi, if_neg hy,
        Bool.false_eq_true, ↓reduceIte]
      exact he

/-- Concrete addition ideal identity, including all exceptional branches.
The vertical function is explicit: the executable loop omits it, which
must later be justified by the final exponent on the chosen subgroups. -/
theorem millerAdd_ideal {T R : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (P : EmbeddedPoint) :
    principal (addDenominator T R P) * (pointIdeal T * pointIdeal R) =
      principal (addLine T R) * pointIdeal (millerAdd T R P).1 := by
  by_cases hi : T.inf = true
  · simp [addDenominator, millerAdd, hi, pointIdeal, addLine]
  · by_cases hj : R.inf = true
    · simp [addDenominator, millerAdd, hi, hj, pointIdeal, addLine]
    · have hif := Bool.eq_false_iff.mpr hi
      have hjf := Bool.eq_false_iff.mpr hj
      simp only [addDenominator, hif, hjf, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      by_cases hx : T.x = R.x
      · by_cases hy : T.y = R.y
        · have he : T = R := by cases T; cases R; simp_all
          subst R
          simpa only [millerAdd_self_eq_millerDouble, addLine, if_neg hi,
            if_pos rfl] using millerDouble_ideal hT P
        · have hn := (Y_eq_of_X_eq ((ambient_equation _ _).mpr (hT hif))
            ((ambient_equation _ _).mpr (hR hjf)) hx).resolve_left hy
          have he := XYIdeal_neg_mul (ambient_nonsingular (hR hjf))
          rw [← hn, ← hx] at he
          simp only [millerAdd, if_neg hi, if_neg hj, beq_iff_eq, hx, hy,
            ↓reduceIte, vertical, pointIdeal, addLine, principal_one, one_mul, mul_one]
          simpa only [hx] using he
      · have he := XYIdeal_mul_XYIdeal ((ambient_equation _ _).mpr (hT hif))
          ((ambient_equation _ _).mpr (hR hjf)) (fun h => hx h.1)
        rw [← addSlope_eq_ambientSlope hx] at he
        rw [millerAdd_fst_of_nonvertical hif hjf hx]
        simp only [vertical, pointIdeal, addLine, if_neg hi, if_neg hj, if_neg hx,
          Bool.false_eq_true, ↓reduceIte]
        exact he

end EthLib.Cryptography.Bls.Embedded
