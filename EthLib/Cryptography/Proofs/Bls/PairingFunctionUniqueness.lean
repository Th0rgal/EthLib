import EthLib.Cryptography.Proofs.Bls.PairingGlobalIdeal

/-!
# Uniqueness of the concrete Miller function up to a nonzero constant

The coordinate ring of y²=x³+4 has no nonconstant units. Consequently,
equal principal fractional ideals determine rational functions up to a
nonzero Fp12 constant. This is a proved input to divisor-based identities,
not an assumption of reciprocity or bilinearity.
-/
namespace EthLib.Cryptography.Bls.Embedded
open Polynomial WeierstrassCurve.Affine.CoordinateRing Infinity

/-- Pole degree zero forces a coordinate-ring function to be a constant. -/
theorem constant_of_poleDegree_zero {f : CoordinateRing} (hf : poleDegree f = 0) :
    ∃ c : Fp12, f = algebraMap Fp12 CoordinateRing c := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  have hd := natDegree_eq_zero_iff_degree_le_zero.mp hf
  rw [degree_norm_smul_basis] at hd
  have hq : q = 0 := by
    by_contra hq
    have h := (le_max_right (2 • p.degree) (2 • q.degree + 3)).trans hd
    rw [degree_eq_natDegree hq] at h
    simp only [two_nsmul] at h
    have hn : q.natDegree + q.natDegree + 3 ≤ 0 := by exact_mod_cast h
    omega
  have hp : p.degree ≤ 0 := by
    by_cases hp : p = 0
    · simp [hp]
    · have h := (le_max_left (2 • p.degree) (2 • q.degree + 3)).trans hd
      rw [degree_eq_natDegree hp] at h
      simp only [two_nsmul] at h
      have hn : p.natDegree + p.natDegree ≤ 0 := by exact_mod_cast h
      rw [degree_eq_natDegree hp]
      exact_mod_cast (show p.natDegree ≤ 0 by omega)
  refine ⟨p.coeff 0, ?_⟩
  simp only [hq, smul, map_zero, zero_mul, add_zero, mul_one]
  nth_rw 1 [eq_C_of_degree_le_zero hp]
  rfl

/-- Every unit of the actual affine coordinate ring is a base-field constant. -/
theorem coordinateRing_unit_constant (u : CoordinateRingˣ) :
    ∃ c : Fp12, c ≠ 0 ∧ (u : CoordinateRing) = algebraMap Fp12 CoordinateRing c := by
  have hd := poleDegree_mul u.ne_zero (u⁻¹).ne_zero
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, poleDegree_one] at hd
  obtain ⟨c, hc⟩ := constant_of_poleDegree_zero (show poleDegree (u : CoordinateRing) = 0 by omega)
  refine ⟨c, ?_, hc⟩
  intro hz
  apply u.ne_zero
  rw [hc, hz, map_zero]

/-- Equal principal fractional ideals determine their generating functions
up to a nonzero actual Fp12 constant. -/
theorem eq_constant_mul_of_principal_eq {f g : FunctionField}
    (h : FractionalIdeal.spanSingleton NonZeroDivisors f =
      FractionalIdeal.spanSingleton NonZeroDivisors g) :
    ∃ c : Fp12, c ≠ 0 ∧ algebraMap Fp12 FunctionField c * f = g := by
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp h
  obtain ⟨c, hc, he⟩ := coordinateRing_unit_constant u
  refine ⟨c, hc, ?_⟩
  rw [Units.smul_def, Algebra.smul_def] at hu
  rw [he, ← IsScalarTower.algebraMap_apply Fp12 CoordinateRing FunctionField] at hu
  exact hu

/-- Every valid point ideal is invertible, including the affine unit ideal
used for infinity. The inverse is provided by Mathlib's chord/tangent construction. -/
theorem pointFractional_isUnit {T : EmbeddedPoint} (hT : OnCurve T) :
    IsUnit (pointFractional T) := by
  by_cases hi : T.inf = true
  · simp [pointFractional, pointIdeal, hi]
  · have hns := ambient_nonsingular (hT (Bool.eq_false_iff.mpr hi))
    change IsUnit ((pointIdeal T : Ideal CoordinateRing) : FractionalIdeal NonZeroDivisors FunctionField)
    simp only [pointIdeal, if_neg hi]
    exact (XYIdeal' hns).isUnit

/-- A concrete fractional-ideal Miller relation determines the function up
to a nonzero constant; the cursor factor can be cancelled because it is invertible. -/
theorem blsMillerFunction_unique_up_to_constant (p : G1) {q : G2} (hq : G2.Valid q)
    {g : FunctionField}
    (hg : FractionalIdeal.spanSingleton NonZeroDivisors g *
      pointFractional (blsMillerState p q).point = pointFractional (ofG2 q) ^ blsX) :
    ∃ c : Fp12, c ≠ 0 ∧ algebraMap Fp12 FunctionField c * blsMillerFunction p q = g := by
  apply eq_constant_mul_of_principal_eq
  apply (pointFractional_isUnit (blsMillerState_onCurve p hq)).mul_left_inj.mp
  exact (blsMillerFunction_principal p hq).trans hg.symm

end EthLib.Cryptography.Bls.Embedded
