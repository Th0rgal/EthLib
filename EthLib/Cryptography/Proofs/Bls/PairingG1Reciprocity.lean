import EthLib.Cryptography.Proofs.Bls.PairingEvaluationReciprocity

/-!
# Proofs: points on chords and tangents

A line through two curve points meets the curve in a third point.

This file identifies the three intersection points of each chord and tangent used by the Miller loop.

It also shows when two embedded points denote the same curve point.
-/

namespace EthLib.Cryptography.Bls.Embedded
open WeierstrassCurve.Affine

theorem finite_ext {P Q : EmbeddedPoint} (hp : P.inf = false) (hq : Q.inf = false)
    (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q := by
  cases P; cases Q; simp_all

theorem inf_eq_of_toAmbient_eq {P Q : EmbeddedPoint} (hP : OnCurve P) (hQ : OnCurve Q)
    (he : toAmbient P hP = toAmbient Q hQ) : P.inf = Q.inf := by
  by_cases hp : P.inf = true
  · have hq := Tate.inf_of_toAmbient_zero hQ (he.symm.trans (toAmbient_inf hP hp))
    exact hp.trans hq.symm
  · have hq : Q.inf ≠ true := fun hq => hp (Tate.inf_of_toAmbient_zero hP
      (he.trans (toAmbient_inf hQ hq)))
    exact (Bool.eq_false_iff.mpr hp).trans (Bool.eq_false_iff.mpr hq).symm

theorem eq_of_toAmbient_eq_of_finite {P Q : EmbeddedPoint} (hP : OnCurve P) (hQ : OnCurve Q)
    (hp : P.inf = false) (he : toAmbient P hP = toAmbient Q hQ) : P = Q := by
  have hq := (inf_eq_of_toAmbient_eq hP hQ he).symm.trans hp
  rw [toAmbient_finite hP hp, toAmbient_finite hQ hq] at he
  have hxy := Point.some.inj he
  exact finite_ext hp hq hxy.1 hxy.2

private theorem mk_finite (P : EmbeddedPoint) (hi : P.inf = false) :
    (⟨P.x, P.y, false⟩ : EmbeddedPoint) = P := by
  cases P
  cases hi
  rfl

namespace SplitLine

theorem secant_point₁ {T R : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (ht : T.inf = false) (hr : R.inf = false) (hx : T.x ≠ R.x) :
    (secant hT hR ht hr hx).point₁ = T := by
  dsimp only [secant, ofChord, point₁]
  have hy : Line.addSlope T.x T.y R.x R.y * T.x +
      (T.y - Line.addSlope T.x T.y R.x R.y * T.x) = T.y := by ring
  exact (congrArg (fun y => (⟨T.x, y, false⟩ : EmbeddedPoint)) hy).trans (mk_finite T ht)

theorem secant_point₂ {T R : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (ht : T.inf = false) (hr : R.inf = false) (hx : T.x ≠ R.x) :
    (secant hT hR ht hr hx).point₂ = R := by
  dsimp only [secant, ofChord, point₂]
  have hy : Line.addSlope T.x T.y R.x R.y * R.x +
      (T.y - Line.addSlope T.x T.y R.x R.y * T.x) = R.y := by
    linear_combination addSlope_mul_sub (y := T.y) (z := R.y) hx
  exact (congrArg (fun y => (⟨R.x, y, false⟩ : EmbeddedPoint)) hy).trans (mk_finite R hr)

theorem secant_point₃ {T R : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (ht : T.inf = false) (hr : R.inf = false) (hx : T.x ≠ R.x) (U : EmbeddedPoint) :
    (secant hT hR ht hr hx).point₃ = negate (millerAdd T R U).1 := by
  rw [millerAdd_fst_of_nonvertical ht hr hx]
  dsimp only [secant, ofChord, point₃, negate]
  apply congrArg (fun y => (⟨ambientCurve.addX T.x R.x (Line.addSlope T.x T.y R.x R.y), y, false⟩ : EmbeddedPoint))
  change Line.addSlope T.x T.y R.x R.y *
      (ambientCurve.addX T.x R.x (Line.addSlope T.x T.y R.x R.y)) +
      (T.y - Line.addSlope T.x T.y R.x R.y * T.x) =
    -ambientCurve.addY T.x R.x T.y (Line.addSlope T.x T.y R.x R.y)
  simp only [ambient_addX, ambient_addY]
  ring

theorem tangent_point₁ {T : EmbeddedPoint} (hT : OnCurve T)
    (ht : T.inf = false) (hy : T.y ≠ 0) : (tangent hT ht hy).point₁ = T := by
  dsimp only [tangent, ofChord, point₁]
  have hy : Line.tangentSlope T.x T.y * T.x + (T.y - Line.tangentSlope T.x T.y * T.x) = T.y := by ring
  exact (congrArg (fun y => (⟨T.x, y, false⟩ : EmbeddedPoint)) hy).trans (mk_finite T ht)

theorem tangent_point₂ {T : EmbeddedPoint} (hT : OnCurve T)
    (ht : T.inf = false) (hy : T.y ≠ 0) : (tangent hT ht hy).point₂ = T :=
  tangent_point₁ hT ht hy

theorem tangent_point₃ {T : EmbeddedPoint} (hT : OnCurve T)
    (ht : T.inf = false) (hy : T.y ≠ 0) (U : EmbeddedPoint) :
    (tangent hT ht hy).point₃ = negate (millerDouble T U).1 := by
  rw [millerDouble_fst_of_nonvertical ht hy]
  dsimp only [tangent, ofChord, point₃, negate]
  apply congrArg (fun y => (⟨ambientCurve.addX T.x T.x (Line.tangentSlope T.x T.y), y, false⟩ : EmbeddedPoint))
  change Line.tangentSlope T.x T.y * (ambientCurve.addX T.x T.x (Line.tangentSlope T.x T.y)) +
      (T.y - Line.tangentSlope T.x T.y * T.x) =
    -ambientCurve.addY T.x T.x T.y (Line.tangentSlope T.x T.y)
  simp only [ambient_addX, ambient_addY]
  ring

/-- Every finite nonvertical sum supplies the split section used by reciprocity. -/
theorem exists_of_finite_add {T R : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (ht : T.inf = false) (hr : R.inf = false) (U : EmbeddedPoint)
    (hs : (millerAdd T R U).1.inf = false) :
    ∃ s : SplitLine, s.point₁ = T ∧ s.point₂ = R ∧ s.point₃ = negate (millerAdd T R U).1 := by
  by_cases hx : T.x = R.x
  · by_cases hy : T.y = R.y
    · have he := finite_ext ht hr hx hy
      subst R
      rw [millerAdd_self_eq_millerDouble] at hs ⊢
      have hy0 : T.y ≠ 0 := by
        intro hz
        simp only [millerDouble, ht, Bool.false_eq_true, ↓reduceIte, hz,
          Fp12.zero_eq_zero, beq_self_eq_true] at hs
        cases hs
      exact ⟨tangent hT ht hy0, tangent_point₁ hT ht hy0,
        tangent_point₂ hT ht hy0, tangent_point₃ hT ht hy0 U⟩
    · simp only [millerAdd, ht, hr, Bool.false_eq_true, ↓reduceIte,
        beq_iff_eq, hx, hy] at hs
      cases hs
  · exact ⟨secant hT hR ht hr hx, secant_point₁ hT hR ht hr hx,
      secant_point₂ hT hR ht hr hx, secant_point₃ hT hR ht hr hx U⟩

end SplitLine
namespace Tate

theorem value_add_eval_finite {R T U : EmbeddedPoint}
    (hR : OnCurve R) (hpar : TwistParity R)
    (hT : OnCurve T) (hU : OnCurve U) (ht : T.inf = false) (hu : U.inf = false)
    (hS : (millerAdd T U T).1.inf = false)
    (hTsep : Separated T) (hUsep : Separated U) (hSsep : Separated (millerAdd T U T).1)
    (hr : Fr.modulus • toAmbient R hR = 0) :
    value R (millerAdd T U T).1 (millerAdd_onCurve hT hU T) hS =
      value R T hT ht * value R U hU hu := by
  obtain ⟨s, hs₁, hs₂, hs₃⟩ := SplitLine.exists_of_finite_add hT hU ht hu T hS
  have hp := value_product_line s hR hpar hr (by simpa only [hs₁] using hTsep)
    (by simpa only [hs₂] using hUsep) (by simpa only [hs₃] using hSsep.negate)
  simp only [hs₁, hs₂, hs₃] at hp
  have hn := value_mul_neg_eval hR hpar (millerAdd_onCurve hT hU T) hS
    hSsep.1 hSsep.2.1 hSsep.2.2 hr
  have hv : value R (negate (millerAdd T U T).1)
      (negate_onCurve (millerAdd_onCurve hT hU T)) hS ≠ 0 := by
    have hs := hSsep.negate
    have h0 := state_evaluate_nonzero hR hpar (negate_onCurve (millerAdd_onCurve hT hU T)) hS
      hs.1 hs.2.1 hs.2.2
    exact finalExponentiation_ne_zero (div_ne_zero h0.1 h0.2)
  exact mul_right_cancel₀ hv (hn.trans hp.symm)


/-- Reduced Tate evaluation on a curve point, normalized to one at infinity. -/
noncomputable def atPoint (R P : EmbeddedPoint) (hP : OnCurve P) : Fp12 :=
  if hi : P.inf = true then 1 else value R P hP (Bool.eq_false_iff.mpr hi)

theorem atPoint_inf (R : EmbeddedPoint) {P : EmbeddedPoint} (hP : OnCurve P)
    (hi : P.inf = true) : atPoint R P hP = 1 := by simp only [atPoint, dif_pos hi]

theorem atPoint_finite (R : EmbeddedPoint) {P : EmbeddedPoint} (hP : OnCurve P)
    (hi : P.inf = false) : atPoint R P hP = value R P hP hi := by
  simp only [atPoint, hi, Bool.false_eq_true, ↓reduceDIte]

theorem atPoint_eq_of_toAmbient_eq (R : EmbeddedPoint) {P Q : EmbeddedPoint}
    (hP : OnCurve P) (hQ : OnCurve Q) (he : toAmbient P hP = toAmbient Q hQ) :
    atPoint R P hP = atPoint R Q hQ := by
  by_cases hi : P.inf = true
  · have hj := (inf_eq_of_toAmbient_eq hP hQ he).symm.trans hi
    rw [atPoint_inf R hP hi, atPoint_inf R hQ hj]
  · have hpq := eq_of_toAmbient_eq_of_finite hP hQ (Bool.eq_false_iff.mpr hi) he
    subst Q
    rfl

/-- Evaluation additivity, including identity, inverse and tangent branches. -/
theorem atPoint_add {R T U : EmbeddedPoint} (hR : OnCurve R) (hpar : TwistParity R)
    (hT : OnCurve T) (hU : OnCurve U)
    (hTsep : T.inf = false → Separated T) (hUsep : U.inf = false → Separated U)
    (hSsep : (millerAdd T U T).1.inf = false → Separated (millerAdd T U T).1)
    (hr : Fr.modulus • toAmbient R hR = 0) :
    atPoint R (millerAdd T U T).1 (millerAdd_onCurve hT hU T) =
      atPoint R T hT * atPoint R U hU := by
  by_cases ht : T.inf = true
  · simp only [millerAdd, if_pos ht, atPoint_inf R hT ht, one_mul]
  · by_cases hu : U.inf = true
    · simp only [millerAdd, if_neg ht, if_pos hu, atPoint_inf R hU hu, mul_one]
    · have htf := Bool.eq_false_iff.mpr ht
      have huf := Bool.eq_false_iff.mpr hu
      by_cases hs : (millerAdd T U T).1.inf = true
      · have hsum : toAmbient T hT + toAmbient U hU = 0 :=
          (millerAdd_toAmbient hT hU T).symm.trans (toAmbient_inf (millerAdd_onCurve hT hU T) hs)
        have hneg : toAmbient U hU = toAmbient (negate T) (negate_onCurve hT) := by
          rw [negate_toAmbient hT]
          exact eq_neg_of_add_eq_zero_right hsum
        have he := eq_of_toAmbient_eq_of_finite hU (negate_onCurve hT) huf hneg
        rw [atPoint_inf R (millerAdd_onCurve hT hU T) hs,
          atPoint_finite R hT htf, atPoint_finite R hU huf]
        have hn := value_mul_neg_eval hR hpar hT htf (hTsep htf).1 (hTsep htf).2.1
          (hTsep htf).2.2 hr
        simpa only [he] using hn.symm
      · have hsf := Bool.eq_false_iff.mpr hs
        rw [atPoint_finite R _ hsf, atPoint_finite R hT htf, atPoint_finite R hU huf]
        exact value_add_eval_finite hR hpar hT hU htf huf hsf
          (hTsep htf) (hUsep huf) (hSsep hsf) hr

end Tate
end EthLib.Cryptography.Bls.Embedded
