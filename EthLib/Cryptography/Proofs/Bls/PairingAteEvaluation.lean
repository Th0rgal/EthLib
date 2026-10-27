import EthLib.Cryptography.Proofs.Bls.PairingSignedReciprocity

/-!
# Proofs: the Miller value as a function on the curve

The Miller loop builds a rational function on the curve, and its executable value is that function evaluated at a point.

This file defines the reduced value for the negative BLS parameter and proves it equals what the code computes.

It also proves the value is nonzero, and that values at opposite points multiply to one.
-/

namespace EthLib.Cryptography.Bls.Embedded
open PairingTower PairingSource
namespace SplitLine

theorem exists_fixed_of_finite_add {T U : EmbeddedPoint}
    (hT : OnCurve T) (hU : OnCurve U) (ht : T.inf = false) (hu : U.inf = false)
    (hTx : primeFrobenius T.x = T.x) (hTy : primeFrobenius T.y = T.y)
    (hUx : primeFrobenius U.x = U.x) (hUy : primeFrobenius U.y = U.y)
    (P : EmbeddedPoint) (hs : (millerAdd T U P).1.inf = false) :
    ∃ s : SplitLine, s.point₁ = T ∧ s.point₂ = U ∧ s.point₃ = negate (millerAdd T U P).1 ∧
      primeFrobenius s.slope = s.slope ∧ primeFrobenius s.offset = s.offset := by
  by_cases hx : T.x = U.x
  · by_cases hy : T.y = U.y
    · have he := finite_ext ht hu hx hy
      subst U
      rw [millerAdd_self_eq_millerDouble] at hs ⊢
      have hy0 : T.y ≠ 0 := by
        intro hz
        simp only [millerDouble, ht, Bool.false_eq_true, ↓reduceIte, hz,
          Fp12.zero_eq_zero, beq_self_eq_true] at hs
        cases hs
      have hm : primeFrobenius (Line.tangentSlope T.x T.y) = Line.tangentSlope T.x T.y := by
        rw [tangentSlope_fieldMap, hTx, hTy]
      refine ⟨tangent hT ht hy0, tangent_point₁ hT ht hy0, tangent_point₂ hT ht hy0,
        tangent_point₃ hT ht hy0 P, hm, ?_⟩
      change primeFrobenius (T.y - Line.tangentSlope T.x T.y * T.x) = _
      rw [map_sub, map_mul, hm, hTx, hTy]
      rfl
    · simp only [millerAdd, ht, hu, Bool.false_eq_true, ↓reduceIte,
        beq_iff_eq, hx, hy] at hs
      cases hs
  · have hm : primeFrobenius (Line.addSlope T.x T.y U.x U.y) = Line.addSlope T.x T.y U.x U.y := by
      rw [addSlope_fieldMap, hTx, hTy, hUx, hUy]
    refine ⟨secant hT hU ht hu hx, secant_point₁ hT hU ht hu hx, secant_point₂ hT hU ht hu hx,
      secant_point₃ hT hU ht hu hx P, hm, ?_⟩
    change primeFrobenius (T.y - Line.addSlope T.x T.y U.x U.y * T.x) = _
    rw [map_sub, map_mul, hm, hTx, hTy]
    rfl

end SplitLine

namespace Ate

noncomputable def state (R P : EmbeddedPoint) : MillerState :=
  MillerState.run blsX R P blsX.log2 (MillerState.initial R)

/-- Reduced value of the actual negative-parameter Miller function. -/
noncomputable def value (R P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false) : Fp12 :=
  let s := state R P
  finalExponentiation (evaluate P hP hi s.denominator /
    evaluate P hP hi (s.numerator * vertical s.point))

theorem state_evalIndependent (R P Q : EmbeddedPoint) : state R P = state R Q :=
  MillerState.run_evalIndependent _ _ _ _ _ _

theorem value_eq_actual {p : G1} {q : G2} (hp : G1.Valid p)
    (hi : p.isInfinity = false) :
    value (ofG2 q) (ofG1 p) (ofG1_onCurve hp) (by simpa only [ofG1_inf] using hi) =
      finalExponentiation (blsNegativeMillerValue p hp hi q) := by
  rfl

theorem value_eq_of_toAmbient_eq {R P Q : EmbeddedPoint}
    (hP : OnCurve P) (hQ : OnCurve Q) (hp : P.inf = false)
    (he : toAmbient P hP = toAmbient Q hQ) :
    value R P hP hp = value R Q hQ (by
      have hq := (inf_eq_of_toAmbient_eq hP hQ he).symm.trans hp
      exact hq) := by
  have hq := (inf_eq_of_toAmbient_eq hP hQ he).symm.trans hp
  have heq := eq_of_toAmbient_eq_of_finite hP hQ hp he
  subst Q
  rfl

theorem value_ne_zero {R P : EmbeddedPoint} (hR : OnCurve R) (hpar : TwistParity R)
    (hP : OnCurve P) (hi : P.inf = false) (hsep : Tate.Separated P) : value R P hP hi ≠ 0 := by
  have h := MillerState.run_evaluate_nonzero_at hR hpar hP hi hsep blsX P
  have hv := evaluate_vertical_ne_zero (MillerState.run_onCurve hR _ _ _ hR) hP hi
    (MillerState.run_twistParity (R := R) hpar P blsX blsX.log2 (s := MillerState.initial R) hpar) hsep.2.1 hsep.2.2
  apply finalExponentiation_ne_zero
  apply div_ne_zero h.2
  rw [map_mul]
  exact mul_ne_zero h.1 hv

/-- Signed values at opposite fixed evaluation points multiply to one. -/
theorem value_mul_neg_eval (k : Nat) {P : EmbeddedPoint} (hP : OnCurve P)
    (hi : P.inf = false) (hsep : Tate.Separated P) (hfix : primeFrobenius P.x = P.x) :
    value (ofG2 (G2.mulNat G2.generator k)) P hP hi *
      value (ofG2 (G2.mulNat G2.generator k)) (negate P) (negate_onCurve hP) hi = 1 := by
  let R := ofG2 (G2.mulNat G2.generator k)
  have hR := ofG2_onCurve (G2.valid_mulNat G2.valid_generator k)
  have hpar := ofG2_twistParity (G2.mulNat G2.generator k)
  let N := VerticalNorm.millerNorm P hP hi
  have hD : N.norm (state R P).denominator ≠ 0 :=
    mul_ne_zero (MillerState.run_evaluate_nonzero_at hR hpar hP hi hsep blsX P).2
      (MillerState.run_evaluate_nonzero_at hR hpar (negate_onCurve hP) hi hsep.negate blsX P).2
  have hn := N.reduced_negative_of_weight_eigen hR P
    (fun T _ => VerticalNorm.norm_vertical_weight P hP hi T) hD
    (VerticalNorm.weight_ne_zero hP hi hsep hR hpar)
    (N.negative_cursor_weight hR P (fun T => VerticalNorm.weight_frobenius P T hfix)
      (frobenius_generator_mulNat_signed k))
  unfold value
  rw [state_evalIndependent _ (negate P) P, ← finalExponentiation_mul, ← mul_div_mul_comm]
  exact hn

/-- Signed values at a split Fp line's intersections multiply to one. -/
theorem value_product_line (s : SplitLine) (k : Nat)
    (hm : primeFrobenius s.slope = s.slope) (hb : primeFrobenius s.offset = s.offset)
    (h₁ : Tate.Separated s.point₁) (h₂ : Tate.Separated s.point₂) (h₃ : Tate.Separated s.point₃) :
    value (ofG2 (G2.mulNat G2.generator k)) s.point₁ s.point₁_onCurve rfl *
      value (ofG2 (G2.mulNat G2.generator k)) s.point₂ s.point₂_onCurve rfl *
      value (ofG2 (G2.mulNat G2.generator k)) s.point₃ s.point₃_onCurve rfl = 1 := by
  have h := s.reduced_negative_generator_norm hm hb h₁ h₂ h₃ k s.point₁
  unfold value
  rw [state_evalIndependent _ s.point₂ s.point₁, state_evalIndependent _ s.point₃ s.point₁,
    ← finalExponentiation_mul, ← finalExponentiation_mul,
    ← mul_div_mul_comm, ← mul_div_mul_comm]
  exact h


/-- Signed evaluation additivity when the two inputs and their sum are finite. -/
theorem value_add_eval_finite (k : Nat) {T U : EmbeddedPoint}
    (hT : OnCurve T) (hU : OnCurve U) (ht : T.inf = false) (hu : U.inf = false)
    (hTx : primeFrobenius T.x = T.x) (hTy : primeFrobenius T.y = T.y)
    (hUx : primeFrobenius U.x = U.x) (hUy : primeFrobenius U.y = U.y)
    (hS : (millerAdd T U T).1.inf = false)
    (hSx : primeFrobenius (millerAdd T U T).1.x = (millerAdd T U T).1.x)
    (hTsep : Tate.Separated T) (hUsep : Tate.Separated U) (hSsep : Tate.Separated (millerAdd T U T).1) :
    value (ofG2 (G2.mulNat G2.generator k)) (millerAdd T U T).1 (millerAdd_onCurve hT hU T) hS =
      value (ofG2 (G2.mulNat G2.generator k)) T hT ht *
      value (ofG2 (G2.mulNat G2.generator k)) U hU hu := by
  obtain ⟨s, hs₁, hs₂, hs₃, hm, hb⟩ := SplitLine.exists_fixed_of_finite_add hT hU ht hu
    hTx hTy hUx hUy T hS
  have hp := value_product_line s k hm hb (by simpa only [hs₁] using hTsep)
    (by simpa only [hs₂] using hUsep) (by simpa only [hs₃] using hSsep.negate)
  simp only [hs₁, hs₂, hs₃] at hp
  have hn := value_mul_neg_eval k (millerAdd_onCurve hT hU T) hS hSsep hSx
  have hv := value_ne_zero (ofG2_onCurve (G2.valid_mulNat G2.valid_generator k))
    (ofG2_twistParity (G2.mulNat G2.generator k)) (negate_onCurve (millerAdd_onCurve hT hU T))
    hS hSsep.negate
  exact mul_right_cancel₀ hv (hn.trans hp.symm)


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
  · rw [atPoint_inf R hP hi,
      atPoint_inf R hQ ((inf_eq_of_toAmbient_eq hP hQ he).symm.trans hi)]
  · have heq := eq_of_toAmbient_eq_of_finite hP hQ (Bool.eq_false_iff.mpr hi) he
    subst Q
    rfl

/-- Signed-Ate evaluation additivity, with all exceptional branches. -/
theorem atPoint_add (k : Nat) {T U : EmbeddedPoint} (hT : OnCurve T) (hU : OnCurve U)
    (hTx : primeFrobenius T.x = T.x) (hTy : primeFrobenius T.y = T.y)
    (hUx : primeFrobenius U.x = U.x) (hUy : primeFrobenius U.y = U.y)
    (hTsep : T.inf = false → Tate.Separated T) (hUsep : U.inf = false → Tate.Separated U)
    (hSsep : (millerAdd T U T).1.inf = false → Tate.Separated (millerAdd T U T).1)
    (hSx : (millerAdd T U T).1.inf = false →
      primeFrobenius (millerAdd T U T).1.x = (millerAdd T U T).1.x) :
    atPoint (ofG2 (G2.mulNat G2.generator k)) (millerAdd T U T).1 (millerAdd_onCurve hT hU T) =
      atPoint (ofG2 (G2.mulNat G2.generator k)) T hT *
      atPoint (ofG2 (G2.mulNat G2.generator k)) U hU := by
  let R := ofG2 (G2.mulNat G2.generator k)
  change atPoint R _ _ = atPoint R T hT * atPoint R U hU
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
        have hn := value_mul_neg_eval k hT htf (hTsep htf) hTx
        simpa only [he] using hn.symm
      · have hsf := Bool.eq_false_iff.mpr hs
        rw [atPoint_finite R _ hsf, atPoint_finite R hT htf, atPoint_finite R hU huf]
        exact value_add_eval_finite k hT hU htf huf hTx hTy hUx hUy hsf (hSx hsf)
          (hTsep htf) (hUsep huf) (hSsep hsf)

end Ate
end EthLib.Cryptography.Bls.Embedded
