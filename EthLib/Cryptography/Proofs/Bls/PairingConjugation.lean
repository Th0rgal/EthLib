import EthLib.Cryptography.Proofs.Bls.PairingRefinement

/-!
# Conjugation and the concrete Miller cursor

The sextic untwist has conjugation-fixed x and conjugation-negated y.
The executable doubling and addition preserve this property, so their
vertical denominator values at embedded G1 points lie in Fp6.
-/
namespace EthLib.Cryptography.Bls
namespace PairingTower

def conjugation : Fp12 →+* Fp12 where
  toFun := Fp12.conjugate
  map_zero' := by apply Fp12.ext <;> simp
  map_one' := by apply Fp12.ext <;> simp
  map_add' := Fp12.conjugate_add
  map_mul' := Fp12.conjugate_mul

@[simp] theorem conjugation_apply (a : Fp12) : conjugation a = a.conjugate := rfl

@[simp] theorem conjugate_inv (a : Fp12) : (a⁻¹).conjugate = a.conjugate⁻¹ :=
  map_inv₀ conjugation a

@[simp] theorem conjugate_zero : (0 : Fp12).conjugate = 0 := map_zero conjugation
@[simp] theorem conjugate_one : (1 : Fp12).conjugate = 1 := map_one conjugation

theorem conjugate_natCast (n : Nat) : (n : Fp12).conjugate = n := map_natCast conjugation n

@[simp] theorem conjugate_fp6 (a : Fp6) :
    (fp6ToFp12 a).conjugate = fp6ToFp12 a := by
  apply Fp12.ext <;> simp [fp6ToFp12]

@[simp] theorem conjugate_fp2 (a : Fp2) :
    (fp2ToFp12 a).conjugate = fp2ToFp12 a := conjugate_fp6 _

@[simp] theorem conjugate_wInv2 : Embedded.wInv2.conjugate = Embedded.wInv2 := by
  apply Fp12.ext <;> simp [Embedded.wInv2]

@[simp] theorem conjugate_wInv3 : Embedded.wInv3.conjugate = -Embedded.wInv3 := by
  apply Fp12.ext <;> simp [Embedded.wInv3]

/-- Fixed elements are exactly the actual Fp6 inclusion. -/
theorem conjugate_eq_self_iff (a : Fp12) :
    a.conjugate = a ↔ a = fp6ToFp12 a.c0 := by
  constructor
  · intro h
    have hc : -a.c1 = a.c1 := congrArg Fp12.c1 h
    have h2 : (2 : Fp6) ≠ 0 := by decide
    have hz : a.c1 = 0 := by
      apply (mul_eq_zero.mp (show 2 * a.c1 = 0 by linear_combination -hc)).resolve_left h2
    apply Fp12.ext
    · rfl
    · exact hz
  · intro h
    rw [h, conjugate_fp6]

end PairingTower
namespace Embedded
open PairingTower

/-- The two conjugation eigenspaces occupied by an untwisted G2 point. -/
def TwistParity (T : EmbeddedPoint) : Prop :=
  T.x.conjugate = T.x ∧ T.y.conjugate = -T.y

theorem ofG2_twistParity (q : G2) : TwistParity (ofG2 q) := by
  unfold ofG2 TwistParity
  split
  · simp only [Fp12.zero_eq_zero, conjugate_zero, neg_zero, and_self]
  · change (fp2ToFp12 q.toAffine.1 * wInv2).conjugate = _ ∧
      (fp2ToFp12 q.toAffine.2 * wInv3).conjugate = _
    simp only [Fp12.conjugate_mul, conjugate_fp2, conjugate_wInv2, conjugate_wInv3,
      mul_neg]
    exact ⟨rfl, rfl⟩

theorem ofG1_conjugate_x (p : G1) : (ofG1 p).x.conjugate = (ofG1 p).x := by
  unfold ofG1
  split
  · exact conjugate_zero
  · exact conjugate_fp6 _

theorem ofG1_conjugate_y (p : G1) : (ofG1 p).y.conjugate = (ofG1 p).y := by
  unfold ofG1
  split
  · exact conjugate_zero
  · exact conjugate_fp6 _

theorem addSlope_conjugate {T R : EmbeddedPoint} (hT : TwistParity T)
    (hR : TwistParity R) :
    (Line.addSlope T.x T.y R.x R.y).conjugate = -Line.addSlope T.x T.y R.x R.y := by
  change ((R.y - T.y) * (R.x - T.x)⁻¹).conjugate = -((R.y - T.y) * (R.x - T.x)⁻¹)
  rw [Fp12.conjugate_mul, Fp12.conjugate_sub, conjugate_inv,
    Fp12.conjugate_sub, hT.1, hT.2, hR.1, hR.2]
  ring

theorem tangentSlope_conjugate {T : EmbeddedPoint} (hT : TwistParity T) :
    (Line.tangentSlope T.x T.y).conjugate = -Line.tangentSlope T.x T.y := by
  have hc2 : (⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 2)), Fp6.zero⟩ : Fp12) = 2 := by decide
  have hc3 : (⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 3)), Fp6.zero⟩ : Fp12) = 3 := by decide
  simp only [Line.tangentSlope, hc2, hc3]
  change (3 * T.x * T.x * (2 * T.y)⁻¹).conjugate = -(3 * T.x * T.x * (2 * T.y)⁻¹)
  have h2c : (2 : Fp12).conjugate = 2 := map_ofNat conjugation 2
  have h3c : (3 : Fp12).conjugate = 3 := map_ofNat conjugation 3
  simp only [Fp12.conjugate_mul, conjugate_inv, h2c, h3c, hT.1, hT.2,
    mul_neg, inv_neg]

/-- The algebra common to the nonvertical tangent and secant branches. -/
theorem chord_twistParity {T R : EmbeddedPoint} (hT : TwistParity T)
    (hR : TwistParity R) {m : Fp12} (hm : m.conjugate = -m) :
    TwistParity ⟨m * m - T.x - R.x, m * (T.x - (m * m - T.x - R.x)) - T.y, false⟩ := by
  constructor
  · simp only [Fp12.conjugate_sub, Fp12.conjugate_mul, hT.1, hR.1, hm, neg_mul_neg]
  · simp only [Fp12.conjugate_sub, Fp12.conjugate_mul, hT.1, hT.2, hR.1, hm,
      neg_mul_neg]
    ring

theorem millerDouble_twistParity {T : EmbeddedPoint} (hT : TwistParity T)
    (P : EmbeddedPoint) : TwistParity (millerDouble T P).1 := by
  unfold millerDouble
  split
  · exact hT
  · split
    · constructor <;> simp [Fp12.zero_eq_zero]
    · exact chord_twistParity hT hT (tangentSlope_conjugate hT)

theorem millerAdd_twistParity {T R : EmbeddedPoint} (hT : TwistParity T)
    (hR : TwistParity R) (P : EmbeddedPoint) : TwistParity (millerAdd T R P).1 := by
  unfold millerAdd
  split
  · exact hR
  · split
    · exact hT
    · split
      · split
        · exact millerDouble_twistParity hT P
        · constructor <;> simp [Fp12.zero_eq_zero]
      · exact chord_twistParity hT hR (addSlope_conjugate hT hR)

/-- Evaluated vertical factors are fixed whenever both x coordinates are fixed. -/
theorem evaluate_vertical_conjugate {T P : EmbeddedPoint} (hP : OnCurve P)
    (hi : P.inf = false) (hT : TwistParity T) (hx : P.x.conjugate = P.x) :
    (evaluate P hP hi (vertical T)).conjugate = evaluate P hP hi (vertical T) := by
  unfold vertical
  split
  · simp only [map_one, conjugate_one]
  · simp only [evaluate_XClass, Fp12.conjugate_sub, hx, hT.1]

theorem evaluate_addDenominator_conjugate {T R P : EmbeddedPoint} (hP : OnCurve P)
    (hi : P.inf = false) (hT : TwistParity T) (hR : TwistParity R)
    (hx : P.x.conjugate = P.x) :
    (evaluate P hP hi (addDenominator T R P)).conjugate =
      evaluate P hP hi (addDenominator T R P) := by
  unfold addDenominator
  split
  · simp only [map_one, conjugate_one]
  · exact evaluate_vertical_conjugate hP hi (millerAdd_twistParity hT hR P) hx

namespace MillerState

theorem run_twistParity {R : EmbeddedPoint} (hR : TwistParity R) (P : EmbeddedPoint)
    (n i : Nat) {s : MillerState} (hs : TwistParity s.point) :
    TwistParity (run n R P i s).point := by
  induction i generalizing s with
  | zero => exact hs
  | succ i ih =>
    simp only [run]
    split
    · exact ih (millerAdd_twistParity (millerDouble_twistParity hs P) hR P)
    · exact ih (millerDouble_twistParity hs P)

/-- Conjugation invariance of the omitted denominator holds throughout the
actual bit recurrence; no nonvanishing assumption is used here. -/
theorem run_denominator_conjugate {R P : EmbeddedPoint} (hR : TwistParity R)
    (hP : OnCurve P) (hi : P.inf = false) (hx : P.x.conjugate = P.x)
    (n i : Nat) {s : MillerState} (hs : TwistParity s.point)
    (hd : (evaluate P hP hi s.denominator).conjugate = evaluate P hP hi s.denominator) :
    (evaluate P hP hi (run n R P i s).denominator).conjugate =
      evaluate P hP hi (run n R P i s).denominator := by
  induction i generalizing s with
  | zero => exact hd
  | succ i ih =>
    have hds : TwistParity (s.double P).point := millerDouble_twistParity hs P
    have hdd : (evaluate P hP hi (s.double P).denominator).conjugate =
        evaluate P hP hi (s.double P).denominator := by
      simp only [double, map_mul, Fp12.conjugate_mul, hd,
        evaluate_vertical_conjugate hP hi (millerDouble_twistParity hs P) hx]
    simp only [run]
    split
    · apply ih (millerAdd_twistParity hds hR P)
      change (evaluate P hP hi ((s.double P).denominator *
        addDenominator (s.double P).point R P)).conjugate =
          evaluate P hP hi ((s.double P).denominator * addDenominator (s.double P).point R P)
      simp only [map_mul, Fp12.conjugate_mul, hdd,
        evaluate_addDenominator_conjugate hP hi hds hR hx]
    · exact ih hds hdd

end MillerState
end Embedded
open Embedded PairingTower

theorem blsMillerState_twistParity (p : G1) (q : G2) :
    TwistParity (blsMillerState p q).point :=
  MillerState.run_twistParity (ofG2_twistParity q) _ _ _ (ofG2_twistParity q)

theorem blsMillerState_denominator_conjugate {p : G1} (hp : G1.Valid p)
    (hi : p.isInfinity = false) (q : G2) :
    let ev := evaluate (ofG1 p) (ofG1_onCurve hp) (by simpa using hi)
    (ev (blsMillerState p q).denominator).conjugate = ev (blsMillerState p q).denominator := by
  apply MillerState.run_denominator_conjugate (ofG2_twistParity q)
    (ofG1_onCurve hp) (by simpa using hi) (ofG1_conjugate_x p) _ _ (ofG2_twistParity q)
  simp only [MillerState.initial, map_one, conjugate_one]

/-- The actual omitted denominator value is in the explicitly embedded Fp6. -/
theorem blsMillerState_denominator_in_fp6 {p : G1} (hp : G1.Valid p)
    (hi : p.isInfinity = false) (q : G2) :
    let ev := evaluate (ofG1 p) (ofG1_onCurve hp) (by simpa using hi)
    ev (blsMillerState p q).denominator =
      fp6ToFp12 (ev (blsMillerState p q).denominator).c0 :=
  (conjugate_eq_self_iff _).mp (blsMillerState_denominator_conjugate hp hi q)

end EthLib.Cryptography.Bls
