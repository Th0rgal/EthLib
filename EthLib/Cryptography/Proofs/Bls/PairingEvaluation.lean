import EthLib.Cryptography.Proofs.Bls.PairingDivisor

namespace EthLib.Cryptography.Bls.Embedded
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing
open Polynomial

/-- Evaluation on the actual ambient coordinate ring, well-defined because
its argument satisfies the curve equation. This is only for affine points. -/
noncomputable def evaluate (P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false) :
    CoordinateRing →+* Fp12 :=
  AdjoinRoot.lift (evalRingHom P.x) P.y (by
    change (eval₂RingHom (evalRingHom P.x) P.y) ambientCurve.polynomial = 0
    rw [← evalEvalRingHom_eq]
    exact (ambient_equation _ _).mpr (hP hi))

theorem evaluate_mk (P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false)
    (f : Fp12[X][X]) :
    evaluate P hP hi (mk ambientCurve f) = f.evalEval P.x P.y := by
  rw [evaluate, mk, AdjoinRoot.lift_mk]
  exact congrArg (fun g : Fp12[X][X] →+* Fp12 => g f) (congrFun (evalEvalRingHom_eq P.x) P.y).symm

@[simp] theorem evaluate_XClass (P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false)
    (x : Fp12) : evaluate P hP hi (XClass ambientCurve x) = P.x - x := by
  rw [XClass, evaluate_mk]
  simp [evalEval]

@[simp] theorem evaluate_YClass (P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false)
    (f : Fp12[X]) : evaluate P hP hi (YClass ambientCurve f) = P.y - f.eval P.x := by
  rw [YClass, evaluate_mk]
  simp [evalEval]

/-- The coordinate-ring tangent/vertical function evaluates to the exact
value emitted by `millerDouble` at an affine, valid evaluation point. -/
theorem evaluate_doubleLine (T P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false) :
    evaluate P hP hi (doubleLine T) = (millerDouble T P).2 := by
  by_cases ht : T.inf = true
  · simp only [doubleLine, millerDouble, if_pos ht, map_one, Fp12.one_eq_one]
  · by_cases hy : T.y = 0
    · simp only [doubleLine, millerDouble, if_neg ht, Fp12.zero_eq_zero,
        hy, beq_self_eq_true, ↓reduceIte, hi, Bool.false_eq_true, evaluate_XClass]
    · simp only [doubleLine, millerDouble, if_neg ht, Fp12.zero_eq_zero,
        beq_iff_eq, hy, ↓reduceIte, hi, Bool.false_eq_true, evaluate_YClass]
      exact (evalAt_eq_polynomial_eval _ _ _ _ _).symm

/-- The coordinate-ring secant/vertical function evaluates to the exact
value emitted by `millerAdd` at an affine, valid evaluation point. -/
theorem evaluate_addLine (T R P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false) :
    evaluate P hP hi (addLine T R) = (millerAdd T R P).2 := by
  by_cases ht : T.inf = true
  · simp only [addLine, millerAdd, if_pos ht, map_one, Fp12.one_eq_one]
  · by_cases hr : R.inf = true
    · simp only [addLine, millerAdd, if_neg ht, if_pos hr, map_one, Fp12.one_eq_one]
    · by_cases hx : T.x = R.x
      · by_cases hy : T.y = R.y
        · simp only [addLine, millerAdd, if_neg ht, if_neg hr,
            beq_iff_eq, hx, hy, ↓reduceIte, evaluate_doubleLine]
        · simp only [addLine, millerAdd, if_neg ht, if_neg hr,
            beq_iff_eq, hx, hy, ↓reduceIte, hi, Bool.false_eq_true, evaluate_XClass]
      · simp only [addLine, millerAdd, if_neg ht, if_neg hr,
          beq_iff_eq, hx, ↓reduceIte, hi, Bool.false_eq_true, evaluate_YClass]
        exact (evalAt_eq_polynomial_eval _ _ _ _ _).symm

end EthLib.Cryptography.Bls.Embedded
