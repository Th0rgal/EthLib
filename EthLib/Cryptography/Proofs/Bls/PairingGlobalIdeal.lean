import EthLib.Cryptography.Proofs.Bls.PairingInfinityInvariant
import Mathlib.RingTheory.FractionalIdeal.Operations

/-!
# Global fractional-ideal refinement of the Miller invariant

The affine ideal equation is lifted into the actual function field's
fractional ideals. This makes the numerator/denominator relation a
statement about principal fractional ideals and the point ideals; it is
stronger than an equality confined to the affine coordinate ring. The
point at infinity still needs its own divisor class to turn this into a
full divisor theorem.
-/
namespace EthLib.Cryptography.Bls
namespace Embedded
open WeierstrassCurve.Affine.CoordinateRing

abbrev FunctionField := ambientCurve.FunctionField
noncomputable abbrev NonZeroDivisors := nonZeroDivisors CoordinateRing

noncomputable def principalFractional (f : CoordinateRing) :
    FractionalIdeal NonZeroDivisors FunctionField :=
  FractionalIdeal.spanSingleton NonZeroDivisors
    (algebraMap CoordinateRing FunctionField f)

noncomputable def pointFractional (T : EmbeddedPoint) :
    FractionalIdeal NonZeroDivisors FunctionField :=
  (pointIdeal T : FractionalIdeal NonZeroDivisors FunctionField)

@[simp] theorem principalFractional_mul (f g : CoordinateRing) :
    principalFractional (f * g) = principalFractional f * principalFractional g := by
  simp [principalFractional, map_mul]

@[simp] theorem principalFractional_pow (f : CoordinateRing) (n : Nat) :
    principalFractional (f ^ n) = principalFractional f ^ n := by
  simp [principalFractional]

theorem miller_global_fractionalIdeal {R : EmbeddedPoint} (hR : OnCurve R)
    (P : EmbeddedPoint) {n : Nat} (hn : n ≠ 0) :
    principalFractional (MillerState.run n R P n.log2 (MillerState.initial R)).numerator *
      pointFractional (MillerState.run n R P n.log2 (MillerState.initial R)).point =
      principalFractional (MillerState.run n R P n.log2 (MillerState.initial R)).denominator *
        pointFractional R ^ n := by
  have h := MillerState.millerLoop_ideal_eq hR P hn
  have hc := congrArg (fun I : Ideal CoordinateRing =>
    (I : FractionalIdeal NonZeroDivisors FunctionField)) h
  simpa only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow, principal,
    FractionalIdeal.coeIdeal_span_singleton, principalFractional, pointFractional] using hc

theorem blsMiller_global_fractionalIdeal (p : G1) {q : G2} (hq : G2.Valid q) :
    principalFractional (blsMillerState p q).numerator *
      pointFractional (blsMillerState p q).point =
      principalFractional (blsMillerState p q).denominator *
        pointFractional (ofG2 q) ^ blsX := by
  exact miller_global_fractionalIdeal (ofG2_onCurve hq) _ (by decide)

/-- Principal fractional ideal of the actual full Miller function. The
coordinate-ring denominator is cancelled inside the function field. -/
theorem blsMillerFunction_principal (p : G1) {q : G2} (hq : G2.Valid q) :
    FractionalIdeal.spanSingleton NonZeroDivisors (blsMillerFunction p q) *
      pointFractional (blsMillerState p q).point = pointFractional (ofG2 q) ^ blsX := by
  let F := algebraMap CoordinateRing FunctionField (blsMillerState p q).numerator
  let D := algebraMap CoordinateRing FunctionField (blsMillerState p q).denominator
  have hD : D ≠ 0 := by
    intro hz
    apply (blsMillerState_nonzero p q).2
    exact (IsFractionRing.injective CoordinateRing FunctionField)
      (hz.trans (map_zero _).symm)
  have h := blsMiller_global_fractionalIdeal p hq
  change FractionalIdeal.spanSingleton NonZeroDivisors F * _ =
    FractionalIdeal.spanSingleton NonZeroDivisors D * _ at h
  change FractionalIdeal.spanSingleton NonZeroDivisors (F / D) * _ = _
  calc
    _ = FractionalIdeal.spanSingleton NonZeroDivisors D⁻¹ *
        (FractionalIdeal.spanSingleton NonZeroDivisors F *
          pointFractional (blsMillerState p q).point) := by
      rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
      rw [mul_comm (FractionalIdeal.spanSingleton NonZeroDivisors F), mul_assoc]
    _ = FractionalIdeal.spanSingleton NonZeroDivisors D⁻¹ *
        (FractionalIdeal.spanSingleton NonZeroDivisors D * pointFractional (ofG2 q) ^ blsX) := by rw [h]
    _ = _ := by
      rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton,
        inv_mul_cancel₀ hD, FractionalIdeal.spanSingleton_one, one_mul]

end Embedded
end EthLib.Cryptography.Bls
