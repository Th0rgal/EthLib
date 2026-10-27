import EthLib.Cryptography.Proofs.Bls.PairingLine

namespace EthLib.Cryptography.Bls.Embedded
open WeierstrassCurve.Affine

@[simp] theorem toAmbient_inf {p : EmbeddedPoint} (hp : OnCurve p)
    (hi : p.inf = true) : toAmbient p hp = 0 := by
  simp only [toAmbient, dif_pos hi]

theorem toAmbient_finite {p : EmbeddedPoint} (hp : OnCurve p)
    (hi : p.inf = false) :
    toAmbient p hp = .some p.x p.y (ambient_nonsingular (hp hi)) := by
  simp only [toAmbient, hi, Bool.false_eq_true, ↓reduceDIte]

theorem y_ne_negY {x y : Fp12} (hy : y ≠ 0) : y ≠ ambientCurve.negY x y := by
  simp only [negY, ambientCurve, zero_mul, sub_zero]
  intro h
  apply hy
  have hz : 2 * y = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (by decide)

/-- The concrete Miller doubling step refines the ambient elliptic-curve group law. -/
theorem millerDouble_toAmbient {T : EmbeddedPoint} (hT : OnCurve T) (P : EmbeddedPoint) :
    toAmbient (millerDouble T P).1 (millerDouble_onCurve hT P) =
      toAmbient T hT + toAmbient T hT := by
  by_cases hi : T.inf = true
  · simp only [millerDouble, if_pos hi, toAmbient_inf hT hi, zero_add]
  · have hf := Bool.eq_false_iff.mpr hi
    rw [toAmbient_finite hT hf]
    by_cases hy : T.y = 0
    · rw [Point.add_self_of_Y_eq (by simp only [negY, ambientCurve, hy, neg_zero,
        zero_mul, sub_zero])]
      apply toAmbient_inf
      simp only [millerDouble, if_neg hi, hy, Fp12.zero_eq_zero, beq_self_eq_true,
        ↓reduceIte]
    · rw [Point.add_self_of_Y_ne (y_ne_negY hy)]
      simp only [millerDouble_fst_of_nonvertical hf hy, toAmbient,
        Bool.false_eq_true, ↓reduceDIte, tangentSlope_eq_ambientSlope hy]

/-- The concrete Miller addition step refines the ambient elliptic-curve group law. -/
theorem millerAdd_toAmbient {T R : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (P : EmbeddedPoint) :
    toAmbient (millerAdd T R P).1 (millerAdd_onCurve hT hR P) =
      toAmbient T hT + toAmbient R hR := by
  by_cases hi : T.inf = true
  · simp only [millerAdd, if_pos hi, toAmbient_inf hT hi, zero_add]
  · by_cases hj : R.inf = true
    · simp only [millerAdd, if_neg hi, if_pos hj, toAmbient_inf hR hj, add_zero]
    · have hif := Bool.eq_false_iff.mpr hi
      have hjf := Bool.eq_false_iff.mpr hj
      by_cases hx : T.x = R.x
      · by_cases hy : T.y = R.y
        · have he : T = R := by
            cases T; cases R
            simp_all
          subst R
          simpa only [millerAdd_self_eq_millerDouble] using millerDouble_toAmbient hT P
        · have ht := (ambient_equation _ _).mpr (hT hif)
          have hr := (ambient_equation _ _).mpr (hR hjf)
          have hn := (Y_eq_of_X_eq ht hr hx).resolve_left hy
          rw [toAmbient_finite hT hif, toAmbient_finite hR hjf,
            Point.add_of_Y_eq hx hn]
          apply toAmbient_inf
          simp only [millerAdd, if_neg hi, if_neg hj, beq_iff_eq, hx, hy, ↓reduceIte]
      · rw [toAmbient_finite hT hif, toAmbient_finite hR hjf,
          Point.add_some (fun h => hx h.1)]
        simp only [millerAdd_fst_of_nonvertical hif hjf hx, toAmbient,
          Bool.false_eq_true, ↓reduceDIte, addSlope_eq_ambientSlope hx]

end EthLib.Cryptography.Bls.Embedded
