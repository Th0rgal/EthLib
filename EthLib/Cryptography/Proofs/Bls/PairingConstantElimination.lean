import EthLib.Cryptography.Proofs.Bls.PairingFunctionSymmetry
import EthLib.Cryptography.Proofs.Bls.PairingFrobenius

/-!
# Conjugation symmetry removes the Miller-function constant ambiguity
-/
namespace EthLib.Cryptography.Bls
open PairingTower

/-- The exact final exponent kills both conjugation eigenspaces. The
hypothesis includes fixed and anti-fixed nonzero constants. -/
theorem finalExponentiation_of_conjugate_sq {c : Fp12} (hc : c ≠ 0)
    (hs : c.conjugate ^ 2 = c ^ 2) : finalExponentiation c = 1 := by
  have hsquare : finalExponentiation (c ^ 2) = 1 :=
    finalExponentiation_of_conjugate_eq (pow_ne_zero 2 hc) (by
      simpa only [← conjugation_apply, map_pow] using hs)
  have htwo : (finalExponentiation c) ^ 2 = 1 := by
    simpa only [finalExponentiation, Fp12.powNat_eq_pow, ← pow_mul, Nat.mul_comm] using hsquare
  have hr := finalExponentiation_pow_modulus hc
  have he : Fr.modulus = 2 * (Fr.modulus / 2) + 1 := by decide +kernel
  rw [he, pow_succ, pow_mul, htwo, one_pow, one_mul] at hr
  exact hr

namespace Embedded
open FunctionSymmetry

/-- Equal principal ideals of symmetric nonzero rational functions differ
by a constant that the actual final exponent kills. -/
theorem reduced_constant_of_principal_eq {f g : FunctionField} (hf : f ≠ 0)
    (hsf : RationalSymmetric f) (hsg : RationalSymmetric g)
    (hi : FractionalIdeal.spanSingleton NonZeroDivisors f =
      FractionalIdeal.spanSingleton NonZeroDivisors g) :
    ∃ c : Fp12, c ≠ 0 ∧ finalExponentiation c = 1 ∧
      algebraMap Fp12 FunctionField c * f = g := by
  obtain ⟨c, hc, he⟩ := eq_constant_mul_of_principal_eq hi
  exact ⟨c, hc, finalExponentiation_of_conjugate_sq hc
    (constant_conjugate_sq hf hsf hsg he), he⟩

@[simp] theorem evaluate_constant (P : EmbeddedPoint) (hP : OnCurve P)
    (hi : P.inf = false) (c : Fp12) :
    evaluate P hP hi (algebraMap Fp12 CoordinateRing c) = c := by
  change evaluate P hP hi
    (WeierstrassCurve.Affine.CoordinateRing.mk ambientCurve (Polynomial.C (Polynomial.C c))) = c
  rw [evaluate_mk]
  simp [Polynomial.evalEval]

/-- Evaluation of a rational function is independent of the chosen
regular numerator/denominator presentation, when both denominators are nonzero. -/
theorem evaluate_fraction_eq {P : EmbeddedPoint} (hP : OnCurve P) (hi : P.inf = false)
    {a b c d : CoordinateRing} (hb : b ≠ 0) (hd : d ≠ 0)
    (heb : evaluate P hP hi b ≠ 0) (hed : evaluate P hP hi d ≠ 0)
    (he : algebraMap CoordinateRing FunctionField a / algebraMap CoordinateRing FunctionField b =
      algebraMap CoordinateRing FunctionField c / algebraMap CoordinateRing FunctionField d) :
    evaluate P hP hi a / evaluate P hP hi b = evaluate P hP hi c / evaluate P hP hi d := by
  have inj := IsFractionRing.injective CoordinateRing FunctionField
  have hb' : algebraMap CoordinateRing FunctionField b ≠ 0 := by
    intro h
    exact hb (inj (h.trans (map_zero _).symm))
  have hd' : algebraMap CoordinateRing FunctionField d ≠ 0 := by
    intro h
    exact hd (inj (h.trans (map_zero _).symm))
  have hc : a * d = c * b := inj (by
    simpa only [map_mul] using (div_eq_div_iff hb' hd').mp he)
  apply (div_eq_div_iff heb hed).mpr
  simpa only [map_mul] using congrArg (evaluate P hP hi) hc

/-- For symmetric rational functions, equality of principal ideals suffices
for equality of their actual reduced values. All evaluation-domain conditions
are explicit; no evaluation map on poles is postulated. -/
theorem reduced_evaluate_eq_of_principal_eq {P : EmbeddedPoint} (hP : OnCurve P)
    (hi : P.inf = false) {a b c d : CoordinateRing} (ha : a ≠ 0) (hb : b ≠ 0)
    (hd : d ≠ 0) (heb : evaluate P hP hi b ≠ 0) (hed : evaluate P hP hi d ≠ 0)
    (hsf : RationalSymmetric
      (algebraMap CoordinateRing FunctionField a / algebraMap CoordinateRing FunctionField b))
    (hsg : RationalSymmetric
      (algebraMap CoordinateRing FunctionField c / algebraMap CoordinateRing FunctionField d))
    (hid : FractionalIdeal.spanSingleton NonZeroDivisors
        (algebraMap CoordinateRing FunctionField a / algebraMap CoordinateRing FunctionField b) =
      FractionalIdeal.spanSingleton NonZeroDivisors
        (algebraMap CoordinateRing FunctionField c / algebraMap CoordinateRing FunctionField d)) :
    finalExponentiation (evaluate P hP hi a / evaluate P hP hi b) =
      finalExponentiation (evaluate P hP hi c / evaluate P hP hi d) := by
  have inj := IsFractionRing.injective CoordinateRing FunctionField
  have hf : algebraMap CoordinateRing FunctionField a /
      algebraMap CoordinateRing FunctionField b ≠ 0 := div_ne_zero
    (fun h => ha (inj (h.trans (map_zero _).symm)))
    (fun h => hb (inj (h.trans (map_zero _).symm)))
  obtain ⟨u, _hu, hred, he⟩ := reduced_constant_of_principal_eq hf hsf hsg hid
  have he' : algebraMap CoordinateRing FunctionField (algebraMap Fp12 CoordinateRing u * a) /
      algebraMap CoordinateRing FunctionField b =
      algebraMap CoordinateRing FunctionField c / algebraMap CoordinateRing FunctionField d := by
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply Fp12 CoordinateRing FunctionField,
      mul_div_assoc] using he
  have hev := evaluate_fraction_eq hP hi hb hd heb hed he'
  simp only [map_mul, evaluate_constant, mul_div_assoc] at hev
  rw [← hev, finalExponentiation_mul, hred, one_mul]

/-- A convenient regular-function form of reduced uniqueness. -/
theorem reduced_evaluate_eq_of_ideal_eq {P : EmbeddedPoint} (hP : OnCurve P)
    (hi : P.inf = false) {a c : CoordinateRing} (ha : a ≠ 0)
    (hsa : Symmetric a) (hsc : Symmetric c) (hid : principal a = principal c) :
    finalExponentiation (evaluate P hP hi a) = finalExponentiation (evaluate P hP hi c) := by
  have hfrac : FractionalIdeal.spanSingleton NonZeroDivisors
        (algebraMap CoordinateRing FunctionField a) =
      FractionalIdeal.spanSingleton NonZeroDivisors (algebraMap CoordinateRing FunctionField c) := by
    have hc := congrArg (fun I : Ideal CoordinateRing =>
      (I : FractionalIdeal NonZeroDivisors FunctionField)) hid
    simpa only [principal, FractionalIdeal.coeIdeal_span_singleton] using hc
  have he := reduced_evaluate_eq_of_principal_eq hP hi ha (one_ne_zero : (1 : CoordinateRing) ≠ 0)
    (one_ne_zero : (1 : CoordinateRing) ≠ 0)
    (by simpa only [map_one] using (one_ne_zero : (1 : Fp12) ≠ 0))
    (by simpa only [map_one] using (one_ne_zero : (1 : Fp12) ≠ 0))
    (by simpa only [map_one, div_one] using rationalSymmetric_of_coordinate hsa)
    (by simpa only [map_one, div_one] using rationalSymmetric_of_coordinate hsc)
    (by simpa only [map_one, div_one] using hfrac)
  simpa only [map_one, div_one] using he

end Embedded
end EthLib.Cryptography.Bls
