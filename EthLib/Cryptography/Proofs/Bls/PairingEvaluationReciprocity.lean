import EthLib.Cryptography.Proofs.Bls.PairingVerticalReciprocity

namespace EthLib.Cryptography.Bls.Embedded
namespace Tate

/-- Finite evaluation support separated from twisted Miller cursors. -/
def Separated (P : EmbeddedPoint) : Prop :=
  P.x.conjugate = P.x ∧ P.y.conjugate = P.y ∧ P.y ≠ 0

theorem Separated.negate {P : EmbeddedPoint} (h : Separated P) : Separated (negate P) :=
  ⟨h.1, by simpa only [Embedded.negate, Fp12.conjugate_neg] using congrArg Neg.neg h.2.1,
    neg_ne_zero.mpr h.2.2⟩

theorem ofG1_separated {p : G1} (hp : G1.Valid p) (hi : p.isInfinity = false) :
    Separated (ofG1 p) :=
  ⟨ofG1_conjugate_x p, ofG1_conjugate_y p, ofG1_y_ne_zero hp hi⟩

/-- The reduced Miller values at opposite evaluation points multiply to one.
This is reciprocity for the vertical section, with its support proved. -/
theorem value_mul_neg_eval {R P : EmbeddedPoint}
    (hR : OnCurve R) (hpar : TwistParity R)
    (hP : OnCurve P) (hi : P.inf = false)
    (hx : P.x.conjugate = P.x) (hy : P.y.conjugate = P.y) (hy0 : P.y ≠ 0)
    (hr : Fr.modulus • toAmbient R hR = 0) :
    value R P hP hi * value R (negate P) (negate_onCurve hP) hi = 1 := by
  have hp0 := state_evaluate_nonzero hR hpar hP hi hx hy hy0
  have hn0 := state_evaluate_nonzero hR hpar (negate_onCurve hP) hi hx
    (by simpa only [negate, Fp12.conjugate_neg] using congrArg Neg.neg hy)
    (neg_ne_zero.mpr hy0)
  rw [state_evalIndependent R (negate P) P] at hn0
  let N := VerticalNorm.millerNorm P hP hi
  have hf : N.norm (state R P).numerator ≠ 0 := mul_ne_zero hp0.1 hn0.1
  have hd : N.norm (state R P).denominator ≠ 0 := mul_ne_zero hp0.2 hn0.2
  have h := N.reduced_tate hR P hr hf hd
  unfold value
  rw [state_evalIndependent R (negate P) P, ← finalExponentiation_mul, ← mul_div_mul_comm]
  exact h


/-- The reduced r-Miller values at the three intersections of a line have product one. -/
theorem value_product_line (s : SplitLine) {R : EmbeddedPoint}
    (hR : OnCurve R) (hpar : TwistParity R)
    (hr : Fr.modulus • toAmbient R hR = 0)
    (h₁ : Separated s.point₁) (h₂ : Separated s.point₂) (h₃ : Separated s.point₃) :
    value R s.point₁ s.point₁_onCurve rfl * value R s.point₂ s.point₂_onCurve rfl *
      value R s.point₃ s.point₃_onCurve rfl = 1 := by
  have hn₁ := state_evaluate_nonzero hR hpar s.point₁_onCurve rfl h₁.1 h₁.2.1 h₁.2.2
  have hn₂ := state_evaluate_nonzero hR hpar s.point₂_onCurve rfl h₂.1 h₂.2.1 h₂.2.2
  have hn₃ := state_evaluate_nonzero hR hpar s.point₃_onCurve rfl h₃.1 h₃.2.1 h₃.2.2
  rw [state_evalIndependent R s.point₂ s.point₁] at hn₂
  rw [state_evalIndependent R s.point₃ s.point₁] at hn₃
  have hf : s.millerNorm.norm (state R s.point₁).numerator ≠ 0 :=
    mul_ne_zero (mul_ne_zero hn₁.1 hn₂.1) hn₃.1
  have hd : s.millerNorm.norm (state R s.point₁).denominator ≠ 0 :=
    mul_ne_zero (mul_ne_zero hn₁.2 hn₂.2) hn₃.2
  have h := s.millerNorm.reduced_tate hR s.point₁ hr hf hd
  unfold value
  rw [state_evalIndependent R s.point₂ s.point₁, state_evalIndependent R s.point₃ s.point₁,
    ← finalExponentiation_mul, ← finalExponentiation_mul,
    ← mul_div_mul_comm, ← mul_div_mul_comm]
  exact h

end Tate
end EthLib.Cryptography.Bls.Embedded
