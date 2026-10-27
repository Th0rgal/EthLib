import EthLib.Cryptography.Proofs.Bls.G2Order
import EthLib.Cryptography.Proofs.Bls.G2Equiv

/-! # Semantics of the G2 subgroup check

For valid curve representatives, the implementation check is exactly
annihilation by the scalar modulus in the Mathlib curve group. This does
not assert that every such point is a generator multiple: that stronger
claim needs a group-cardinality or torsion-structure argument.
-/
namespace EthLib.Cryptography.Bls.G2
open WeierstrassCurve.Jacobian

/-- Infinity testing agrees with the identity in the curve group. -/
theorem isInfinity_eq_true_iff_toPoint_eq_zero {p : G2} (hp : Valid p) :
    p.isInfinity = true ↔ toPoint p = 0 := by
  constructor
  · intro h
    exact Point.toAffine_of_Z_eq_zero (Fp2.isZero_iff.mp h)
  · intro h
    by_contra hne
    have hz : p.z ≠ 0 := fun hz0 => hne (Fp2.isZero_iff.mpr hz0)
    rw [toPoint, Point.toAffine_of_Z_ne_zero hp hz] at h
    cases h

/-- The concrete subgroup check is precisely the r-torsion test. -/
theorem inSubgroup_iff_modulus_smul_eq_zero {p : G2} (hp : Valid p) :
    inSubgroup p = true ↔ Fr.modulus • toPoint p = 0 := by
  rw [inSubgroup]
  by_cases hi : p.isInfinity = true
  · rw [if_pos hi, (isInfinity_eq_true_iff_toPoint_eq_zero hp).mp hi]
    simp
  · rw [if_neg hi, isInfinity_eq_true_iff_toPoint_eq_zero (valid_mulNat hp _),
      toPoint_mulNat hp]

/-- Every successfully decoded point is checked against actual r-torsion. -/
theorem inSubgroup_iff_of_uncompress {bytes : ByteArray} {p : G2}
    (h : uncompress bytes = .ok p) :
    inSubgroup p = true ↔ Fr.modulus • toPoint p = 0 :=
  inSubgroup_iff_modulus_smul_eq_zero (valid_of_uncompress h)

/-- The concrete generator passes the subgroup test. -/
theorem inSubgroup_generator : inSubgroup generator = true :=
  (inSubgroup_iff_modulus_smul_eq_zero valid_generator).mpr modulus_smul_generator

/-- Multiplication preserves the subgroup test on valid points. -/
theorem inSubgroup_mulNat {p : G2} (hp : Valid p) (hs : inSubgroup p = true)
    (k : Nat) : inSubgroup (mulNat p k) = true := by
  apply (inSubgroup_iff_modulus_smul_eq_zero (valid_mulNat hp k)).mpr
  rw [toPoint_mulNat hp, smul_comm,
    (inSubgroup_iff_modulus_smul_eq_zero hp).mp hs, nsmul_zero]

/-- Every concrete scalar multiple of the generator passes the subgroup test. -/
theorem inSubgroup_mul_generator (s : Fr) : inSubgroup (mul generator s) = true :=
  inSubgroup_mulNat valid_generator inSubgroup_generator s.val

/-- A scalar multiple of the generator is infinity exactly for scalar zero. -/
theorem mul_generator_isInfinity_iff (s : Fr) :
    (mul generator s).isInfinity = true ↔ s = 0 := by
  rw [isInfinity_eq_true_iff_toPoint_eq_zero (valid_mul valid_generator s),
    toPoint_mul valid_generator, ← addOrderOf_dvd_iff_nsmul_eq_zero,
    addOrderOf_toPoint_generator]
  constructor
  · intro h
    exact Fin.ext (Nat.eq_zero_of_dvd_of_lt h s.isLt)
  · rintro rfl
    exact Nat.dvd_zero _

/-- Addition preserves the subgroup check on valid representatives. -/
theorem inSubgroup_add {p q : G2} (hp : Valid p) (hq : Valid q)
    (hs : inSubgroup p = true) (ht : inSubgroup q = true) :
    inSubgroup (add p q) = true := by
  apply (inSubgroup_iff_modulus_smul_eq_zero (valid_add hp hq)).mpr
  rw [toPoint_add hp hq, nsmul_add,
    (inSubgroup_iff_modulus_smul_eq_zero hp).mp hs,
    (inSubgroup_iff_modulus_smul_eq_zero hq).mp ht]
  simp

/-- Negation preserves the subgroup check on valid representatives. -/
theorem inSubgroup_neg {p : G2} (hp : Valid p) (hs : inSubgroup p = true) :
    inSubgroup (neg p) = true := by
  apply (inSubgroup_iff_modulus_smul_eq_zero (valid_neg hp)).mpr
  rw [toPoint_neg hp, neg_nsmul,
    (inSubgroup_iff_modulus_smul_eq_zero hp).mp hs]
  simp

end EthLib.Cryptography.Bls.G2
