import EthLib.Cryptography.Proofs.Bls.PairingInfinityInvariant

/-!
# Proofs: a chart at the point at infinity

The functions `x` and `y` are nonzero elements of the curve's function field, and satisfy `y^2 = x^3 + 4`.

Near infinity the chart `u = x / y`, `v = 1 / y` is used.

This lets the proofs compute the order of a function at the point at infinity.
-/

namespace EthLib.Cryptography.Bls.Embedded.Infinity
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing
open Polynomial
open scoped WithZero

noncomputable def xFunction : ambientCurve.FunctionField :=
  algebraMap CoordinateRing ambientCurve.FunctionField (XClass ambientCurve 0)
noncomputable def yFunction : ambientCurve.FunctionField :=
  algebraMap CoordinateRing ambientCurve.FunctionField (YClass ambientCurve (0 : Fp12[X]))

theorem xFunction_ne_zero : xFunction ≠ 0 := by
  intro h
  have hinj := IsFractionRing.injective CoordinateRing ambientCurve.FunctionField
  exact XClass_ne_zero 0 (hinj (h.trans (map_zero _).symm))

theorem yFunction_ne_zero : yFunction ≠ 0 := by
  intro h
  have hinj := IsFractionRing.injective CoordinateRing ambientCurve.FunctionField
  exact YClass_ne_zero 0 (hinj (h.trans (map_zero _).symm))

/-- The generic point satisfies the actual curve equation in its function field. -/
theorem function_equation : yFunction ^ 2 = xFunction ^ 3 + 4 := by
  have he : (mk ambientCurve) ambientCurve.polynomial = 0 := AdjoinRoot.mk_self
  have hc : (YClass ambientCurve (0 : Fp12[X])) ^ 2 = (XClass ambientCurve 0) ^ 3 + 4 := by
    have hpoly : ambientCurve.polynomial = (X : Fp12[X][X]) ^ 2 - ((C X) ^ 3 + 4) := by
      simp only [WeierstrassCurve.Affine.polynomial, ambientCurve, map_zero, map_ofNat,
        zero_mul, add_zero, map_add, map_pow]
    have he' : (mk ambientCurve) (X ^ 2 - ((C X) ^ 3 + 4)) = 0 :=
      (congrArg (mk ambientCurve) hpoly).symm.trans he
    rw [map_sub, map_add, map_pow, map_pow, map_ofNat, sub_eq_zero] at he'
    simpa only [XClass, YClass, C_0, sub_zero] using he'
  have hm := congrArg (algebraMap CoordinateRing ambientCurve.FunctionField) hc
  simpa only [map_pow, map_add, map_ofNat, xFunction, yFunction] using hm

/-- Coordinates on the projective chart Y=1: u=X/Y and v=Z/Y. -/
noncomputable def chartU : ambientCurve.FunctionField := xFunction / yFunction
noncomputable def chartV : ambientCurve.FunctionField := yFunction⁻¹

/-- The chart equation is v=u³+4v³, whose origin is [0:1:0]. -/
theorem chart_equation : chartV = chartU ^ 3 + 4 * chartV ^ 3 := by
  unfold chartV chartU
  field_simp [yFunction_ne_zero]
  linear_combination function_equation

@[simp] theorem valuation_xFunction : valuation xFunction = WithZero.exp 2 := by
  rw [xFunction, valuation_algebraMap]
  change value (XClass ambientCurve 0) = _
  rw [value, if_neg (XClass_ne_zero _), poleDegree_XClass]
  norm_num

@[simp] theorem valuation_yFunction : valuation yFunction = WithZero.exp 3 := by
  rw [yFunction, valuation_algebraMap]
  change value (YClass ambientCurve 0) = _
  rw [value, if_neg (YClass_ne_zero _), poleDegree_YClass_linear 0 (by simp)]
  norm_num

/-- Both chart coordinates vanish at the center of the infinity valuation. -/
theorem chart_values : valuation chartU = WithZero.exp (-1) ∧
    valuation chartV = WithZero.exp (-3) := by
  constructor
  · exact uniformizer_value
  · rw [chartV, map_inv₀, valuation_yFunction, ← WithZero.exp_neg]

/-- The valuation is centered at the origin of the Y=1 chart, the point
at infinity of the projective cubic. Both coordinates are in its maximal ideal. -/
theorem chart_values_lt_one : valuation chartU < 1 ∧ valuation chartV < 1 := by
  rw [chart_values.1, chart_values.2, ← WithZero.exp_zero]
  constructor <;> apply WithZero.exp_lt_exp.mpr <;> norm_num

end EthLib.Cryptography.Bls.Embedded.Infinity
