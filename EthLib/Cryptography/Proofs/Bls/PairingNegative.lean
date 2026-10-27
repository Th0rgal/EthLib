import EthLib.Cryptography.Proofs.Bls.PairingGlobalIdeal
import EthLib.Cryptography.Proofs.Bls.PairingFrobenius
import EthLib.Cryptography.Proofs.Bls.PairingSourceGroup

/-!
# The actual negative-parameter Miller function

For n=|x| and cursor S=[n]Q, the negative Miller function is
1/(f_n v_S). Its affine ideals and infinity order are proved below;
the executable conjugation yields exactly its reduced value.
-/
namespace EthLib.Cryptography.Bls
set_option maxRecDepth 4000
set_option maxHeartbeats 200000
namespace Embedded
open WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing Polynomial

/-- Negation on the implementation record; the infinity flag is preserved. -/
def negate (T : EmbeddedPoint) : EmbeddedPoint := ⟨T.x, -T.y, T.inf⟩

theorem negate_onCurve {T : EmbeddedPoint} (hT : OnCurve T) : OnCurve (negate T) := by
  intro hi
  change (-T.y) ^ 2 = T.x ^ 3 + 4
  rw [neg_sq, hT hi]

theorem negate_toAmbient {T : EmbeddedPoint} (hT : OnCurve T) :
    toAmbient (negate T) (negate_onCurve hT) = -toAmbient T hT := by
  by_cases hi : T.inf = true
  · rw [toAmbient_inf (p := negate T) (negate_onCurve hT) hi, toAmbient_inf hT hi, neg_zero]
  · rw [toAmbient_finite (p := negate T) (negate_onCurve hT) (Bool.eq_false_iff.mpr hi),
      toAmbient_finite hT (Bool.eq_false_iff.mpr hi), Point.neg_some]
    simp [negate, negY, ambientCurve]

/-- The two opposite point ideals multiply to the vertical principal ideal. -/
theorem pointIdeal_negate_mul {T : EmbeddedPoint} (hT : OnCurve T) :
    pointIdeal (negate T) * pointIdeal T = principal (vertical T) := by
  by_cases hi : T.inf = true
  · simp only [pointIdeal, vertical, negate, hi, ↓reduceIte, principal_one, one_mul]
  · have hf := Bool.eq_false_iff.mpr hi
    have h := XYIdeal_neg_mul (ambient_nonsingular (hT hf))
    simpa only [pointIdeal, vertical, negate, if_neg hi, negY, ambientCurve,
      zero_mul, sub_zero, principal, XIdeal] using h

theorem pointFractional_negate_mul {T : EmbeddedPoint} (hT : OnCurve T) :
    pointFractional (negate T) * pointFractional T = principalFractional (vertical T) := by
  have h := congrArg (fun I : Ideal CoordinateRing =>
    (I : FractionalIdeal NonZeroDivisors FunctionField)) (pointIdeal_negate_mul hT)
  simpa only [FractionalIdeal.coeIdeal_mul, principal, FractionalIdeal.coeIdeal_span_singleton,
    pointFractional, principalFractional] using h

end Embedded
open Embedded Embedded.Infinity
open scoped WithZero

/-- Full negative-parameter Miller function in the actual curve function field. -/
noncomputable def blsNegativeMillerFunction (p : G1) (q : G2) : FunctionField :=
  algebraMap CoordinateRing FunctionField (blsMillerState p q).denominator /
    algebraMap CoordinateRing FunctionField
      ((blsMillerState p q).numerator * vertical (blsMillerState p q).point)

theorem blsNegativeMillerFunction_ne_zero (p : G1) (q : G2) :
    blsNegativeMillerFunction p q ≠ 0 := by
  have h := blsMillerState_nonzero p q
  have hi := IsFractionRing.injective CoordinateRing FunctionField
  apply div_ne_zero
  · exact fun hz => h.2 (hi (hz.trans (map_zero _).symm))
  · exact fun hz => mul_ne_zero h.1 (vertical_ne_zero _) (hi (hz.trans (map_zero _).symm))

theorem blsNegativeMillerFunction_eq_inverse (p : G1) (q : G2) :
    blsNegativeMillerFunction p q =
      (blsMillerFunction p q * algebraMap CoordinateRing FunctionField
        (vertical (blsMillerState p q).point))⁻¹ := by
  simp only [blsNegativeMillerFunction, blsMillerFunction, map_mul, div_eq_mul_inv,
    mul_inv_rev, inv_inv]
  ring

/-- Negative Miller affine principal-ideal formula, with cursor -[|x|]Q. -/
theorem blsNegativeMillerFunction_principal (p : G1) {q : G2} (hq : G2.Valid q) :
    FractionalIdeal.spanSingleton NonZeroDivisors (blsNegativeMillerFunction p q) *
      (pointFractional (negate (blsMillerState p q).point) *
        pointFractional (ofG2 q) ^ blsX) = 1 := by
  let f := blsMillerFunction p q
  let v := algebraMap CoordinateRing FunctionField (vertical (blsMillerState p q).point)
  have hv : v ≠ 0 := by
    intro hz
    exact vertical_ne_zero _ ((IsFractionRing.injective CoordinateRing FunctionField)
      (hz.trans (map_zero _).symm))
  have hn : f * v ≠ 0 := mul_ne_zero (blsMillerFunction_ne_zero p q) hv
  rw [blsNegativeMillerFunction_eq_inverse, ← blsMillerFunction_principal p hq]
  have hneg := pointFractional_negate_mul (blsMillerState_onCurve p hq)
  have halg (a b c : FractionalIdeal NonZeroDivisors FunctionField) : a * (b * c) = b * (a * c) := mul_left_comm a b c
  rw [halg (pointFractional (negate (blsMillerState p q).point)), hneg]
  change FractionalIdeal.spanSingleton NonZeroDivisors (f * v)⁻¹ *
    (FractionalIdeal.spanSingleton NonZeroDivisors f * FractionalIdeal.spanSingleton NonZeroDivisors v) = 1
  rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hn,
    FractionalIdeal.spanSingleton_one]

/-- Exact infinity order of the negative Miller function. -/
theorem blsNegativeMillerFunction_infinity (p : G1) (q : G2) :
    valuation (blsNegativeMillerFunction p q) = WithZero.exp
      (-((blsX : Int) * affineDegree (ofG2 q)) - affineDegree (blsMillerState p q).point) := by
  have hnz := blsMillerState_nonzero p q
  have hi := MillerState.millerLoop_infinity (ofG2 q) (ofG1 p) (n := blsX) (by decide)
  change (poleDegree (blsMillerState p q).numerator : Int) -
    poleDegree (blsMillerState p q).denominator = _ at hi
  have hv : (poleDegree (vertical (blsMillerState p q).point) : Int) =
      2 * affineDegree (blsMillerState p q).point := by
    unfold vertical affineDegree
    split <;> simp [poleDegree_XClass]
  rw [blsNegativeMillerFunction, valuation_quotient hnz.2
    (mul_ne_zero hnz.1 (vertical_ne_zero _)), poleDegree_mul hnz.1 (vertical_ne_zero _)]
  apply congrArg WithZero.exp
  rw [Nat.cast_add]
  have arithmetic (A B C N R S : Int) (h : A - B = N * R - S) (hv : C = 2 * S) :
      B - (A + C) = -(N * R) - S := by omega
  exact arithmetic _ _ _ _ _ _ hi hv

/-- Evaluation of the negative function's displayed numerator/denominator. -/
noncomputable def blsNegativeMillerValue (p : G1) (hp : G1.Valid p)
    (hi : p.isInfinity = false) (q : G2) : Fp12 :=
  let ev := evaluate (ofG1 p) (ofG1_onCurve hp) (by simpa using hi)
  ev (blsMillerState p q).denominator /
    ev ((blsMillerState p q).numerator * vertical (blsMillerState p q).point)

/-- Conjugation in the executable pairing realizes the genuine negative Miller
function, including the extra vertical factor for negating its cursor. -/
theorem pairing_eq_negativeMillerValue {p : G1} {q : G2} (hp : G1.Valid p)
    (hq : G2.Valid q) (hpi : p.isInfinity = false) (hqi : q.isInfinity = false) :
    pairing p q = finalExponentiation (blsNegativeMillerValue p hp hpi q) := by
  let ev := evaluate (ofG1 p) (ofG1_onCurve hp) (by simpa using hpi)
  have hv : finalExponentiation (ev (vertical (blsMillerState p q).point)) = 1 :=
    finalExponentiation_of_conjugate_eq
      (evaluate_vertical_ne_zero (blsMillerState_onCurve p hq) (ofG1_onCurve hp)
        (by simpa using hpi) (blsMillerState_twistParity p q) (ofG1_conjugate_y p)
        (ofG1_y_ne_zero hp hpi))
      (evaluate_vertical_conjugate (ofG1_onCurve hp) (by simpa using hpi)
        (blsMillerState_twistParity p q) (ofG1_conjugate_x p))
  rw [pairing_eq_full_millerValue hp hq hpi hqi,
    finalExponentiation_conjugate (blsMillerValue_ne_zero hp hq hpi)]
  have he : blsNegativeMillerValue p hp hpi q =
      (blsMillerValue p hp hpi q * ev (vertical (blsMillerState p q).point))⁻¹ := by
    simp only [blsNegativeMillerValue, blsMillerValue, map_mul, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [he]
  have hfinv (a : Fp12) : finalExponentiation a⁻¹ = (finalExponentiation a)⁻¹ := by
    simp only [finalExponentiation, Fp12.powNat_eq_pow, inv_pow]
  rw [hfinv, finalExponentiation_mul, hv, mul_one]

end EthLib.Cryptography.Bls
