import EthLib.Cryptography.Proofs.Bls.PairingRefinement
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.NumberTheory.FunctionField

/-!
# The infinity valuation of the actual pairing curve

The coordinate ring has basis (1,Y) over Fp12[X]. Its norm degree is
max(2 deg p, 2 deg q + 3) on p+qY. This constructs the valuation from
proved norm and degree laws, rather than postulating orders of lines.
-/
namespace EthLib.Cryptography.Bls.Embedded
namespace Infinity
open Polynomial
open WeierstrassCurve.Affine.CoordinateRing

local instance : Module.Free Fp12[X] CoordinateRing :=
  Module.Free.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis ambientCurve)
local instance : Module.Finite Fp12[X] CoordinateRing :=
  Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis ambientCurve)

noncomputable def poleDegree (f : CoordinateRing) : Nat := (Algebra.norm Fp12[X] f).natDegree

theorem poleDegree_mul {f g : CoordinateRing} (hf : f ≠ 0) (hg : g ≠ 0) :
    poleDegree (f * g) = poleDegree f + poleDegree g := by
  unfold poleDegree
  rw [map_mul, natDegree_mul ((Algebra.norm_ne_zero_iff).mpr hf)
    ((Algebra.norm_ne_zero_iff).mpr hg)]

theorem norm_degree_add_le (f g : CoordinateRing) :
    (Algebra.norm Fp12[X] (f + g)).degree ≤
      max (Algebra.norm Fp12[X] f).degree (Algebra.norm Fp12[X] g).degree := by
  obtain ⟨p,q,rfl⟩ := exists_smul_basis_eq f
  obtain ⟨r,s,rfl⟩ := exists_smul_basis_eq g
  have he : (p + r) • (1 : CoordinateRing) + (q + s) • mk ambientCurve X =
      (p • (1 : CoordinateRing) + q • mk ambientCurve X) +
        (r • (1 : CoordinateRing) + s • mk ambientCurve X) := by
    module
  rw [← he, degree_norm_smul_basis, degree_norm_smul_basis, degree_norm_smul_basis]
  grw [degree_add_le, degree_add_le]
  have hn (a b : WithBot Nat) : 2 • max a b = max (2 • a) (2 • b) := by
    rcases le_total a b with h | h
    · rw [max_eq_right h, max_eq_right (nsmul_le_nsmul_right h 2)]
    · rw [max_eq_left h, max_eq_left (nsmul_le_nsmul_right h 2)]
  rw [hn, hn, ← max_add_add_right]
  exact max_le (max_le (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_right _ _)))
    (max_le (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_trans (le_max_right _ _) (le_max_right _ _)))

theorem poleDegree_add_le (f g : CoordinateRing) :
    poleDegree (f + g) ≤ max (poleDegree f) (poleDegree g) := by
  have h := norm_degree_add_le f g
  rcases le_max_iff.mp h with h | h
  · exact (natDegree_le_natDegree h).trans (le_max_left _ _)
  · exact (natDegree_le_natDegree h).trans (le_max_right _ _)

open scoped WithZero nonZeroDivisors
open WithZero

noncomputable def value (f : CoordinateRing) : ℤᵐ⁰ :=
  if f = 0 then 0 else exp (poleDegree f : Int)

@[simp] theorem value_zero : value 0 = 0 := by simp [value]
@[simp] theorem value_one : value 1 = 1 := by simp [value, poleDegree]

theorem value_mul (f g : CoordinateRing) : value (f * g) = value f * value g := by
  classical
  by_cases hf : f = 0
  · simp [hf]
  · by_cases hg : g = 0
    · simp [hg]
    · simp only [value, if_neg hf, if_neg hg, if_neg (mul_ne_zero hf hg),
        poleDegree_mul hf hg, Nat.cast_add, exp_add]

theorem value_add_le (f g : CoordinateRing) : value (f + g) ≤ max (value f) (value g) := by
  classical
  by_cases hf : f = 0
  · simp [hf]
  · by_cases hg : g = 0
    · simp [hg]
    · by_cases hs : f + g = 0
      · simp [hs]
      · simp only [value, if_neg hf, if_neg hg, if_neg hs]
        rcases le_max_iff.mp (poleDegree_add_le f g) with h | h
        · exact le_max_of_le_left (exp_le_exp.mpr (by exact_mod_cast h))
        · exact le_max_of_le_right (exp_le_exp.mpr (by exact_mod_cast h))

/-- The normalized infinity valuation on regular functions of the curve.
The normalization is justified below by v(X)=exp(2), v(Y)=exp(3), so X/Y
has valuation exp(-1). -/
noncomputable def coordinateValuation : Valuation CoordinateRing ℤᵐ⁰ where
  toFun := value
  map_zero' := value_zero
  map_one' := value_one
  map_mul' := value_mul
  map_add_le_max' := value_add_le

theorem coordinateValuation_ne_zero {f : CoordinateRing} (hf : f ≠ 0) :
    coordinateValuation f ≠ 0 := by
  change value f ≠ 0
  simp only [value, if_neg hf, exp_ne_zero, ne_eq, not_false_eq_true]

/-- Extend the proved coordinate-ring valuation to the actual function field. -/
noncomputable def valuation : Valuation ambientCurve.FunctionField ℤᵐ⁰ :=
  coordinateValuation.extendToLocalization
    (S := nonZeroDivisors CoordinateRing)
    (fun _ hf => coordinateValuation_ne_zero ((mem_nonZeroDivisors_iff_ne_zero).mp hf)) _

@[simp] theorem valuation_algebraMap (f : CoordinateRing) :
    valuation (algebraMap CoordinateRing ambientCurve.FunctionField f) = coordinateValuation f :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ f

/-- Exact infinity-valuation formula for any quotient of regular functions. -/
theorem valuation_quotient {f g : CoordinateRing} (hf : f ≠ 0) (hg : g ≠ 0) :
    valuation (algebraMap CoordinateRing ambientCurve.FunctionField f /
      algebraMap CoordinateRing ambientCurve.FunctionField g) =
      exp ((poleDegree f : Int) - poleDegree g) := by
  rw [map_div₀, valuation_algebraMap, valuation_algebraMap]
  change value f / value g = _
  simp only [value, if_neg hf, if_neg hg, exp_sub]

@[simp] theorem poleDegree_one : poleDegree 1 = 0 := by simp [poleDegree]

/-- A vertical line has a pole of order two at infinity. -/
theorem poleDegree_XClass (x : Fp12) : poleDegree (XClass ambientCurve x) = 2 := by
  have he : XClass ambientCurve x =
      (X - C x) • (1 : CoordinateRing) + (0 : Fp12[X]) • mk ambientCurve X := by
    simp [XClass, smul]
  rw [he, poleDegree]
  apply natDegree_eq_of_degree_eq_some
  rw [degree_norm_smul_basis]
  simp

/-- Every nonvertical affine line has a pole of order three at infinity. -/
theorem poleDegree_YClass_linear (l : Fp12[X]) (hl : l.degree ≤ 1) :
    poleDegree (YClass ambientCurve l) = 3 := by
  have he : YClass ambientCurve l =
      (-l) • (1 : CoordinateRing) + (1 : Fp12[X]) • mk ambientCurve X := by
    simp [YClass, smul]
    ring
  rw [he, poleDegree]
  apply natDegree_eq_of_degree_eq_some
  rw [degree_norm_smul_basis]
  simp only [degree_neg, degree_one, nsmul_zero, zero_add]
  apply max_eq_right
  calc
    2 • l.degree ≤ 2 • (1 : WithBot Nat) := nsmul_le_nsmul_right hl 2
    _ ≤ 3 := by decide

theorem poleDegree_line (x y m : Fp12) :
    poleDegree (YClass ambientCurve (WeierstrassCurve.Affine.linePolynomial x y m)) = 3 := by
  apply poleDegree_YClass_linear
  unfold WeierstrassCurve.Affine.linePolynomial
  calc
    _ ≤ max ((C m * (X - C x)).degree) (C y).degree := degree_add_le _ _
    _ ≤ max (0 + 1 : WithBot Nat) 0 := max_le_max
      ((degree_mul_le _ _).trans (add_le_add degree_C_le (degree_X_sub_C_le x))) degree_C_le
    _ ≤ 1 := by decide

/-- x/y is a uniformizer for the constructed valuation. Its value exp(-1)
fixes the integral normalization, rather than merely a positive multiple. -/
theorem uniformizer_value :
    valuation (algebraMap CoordinateRing ambientCurve.FunctionField (XClass ambientCurve 0) /
      algebraMap CoordinateRing ambientCurve.FunctionField
        (YClass ambientCurve (0 : Fp12[X]))) = exp (-1) := by
  rw [valuation_quotient (XClass_ne_zero _) (YClass_ne_zero _), poleDegree_XClass,
    poleDegree_YClass_linear 0 (by simp)]
  rfl

end Infinity
end EthLib.Cryptography.Bls.Embedded
