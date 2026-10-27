import EthLib.Cryptography.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.G1Cardinality
import EthLib.Cryptography.Proofs.Bls.CofactorSpan

/-! Completeness of the standard G1 generator span for all r-torsion points.

The elementary curve-size bound is already smaller than r². Therefore two
independent r-torsion points cannot exist. No full curve-order formula or
cofactor-factorization assumption is needed. -/
namespace EthLib.Cryptography.Bls.G1
open WeierstrassCurve.Jacobian

theorem isInfinity_eq_true_iff_toPoint_eq_zero {P : G1} (hP : Valid P) :
    P.isInfinity = true ↔ toPoint P = 0 := by
  constructor
  · intro h
    exact Point.toAffine_of_Z_eq_zero (isZero_iff.mp h)
  · intro h
    by_contra hne
    have hz : (P.z : ZMod Fp.modulus) ≠ 0 := fun hz0 => hne (isZero_iff.mpr hz0)
    rw [toPoint, Point.toAffine_of_Z_ne_zero hP hz] at h
    cases h

/-- The executable G1 subgroup check is exactly the r-torsion predicate. -/
theorem inSubgroup_iff_modulus_smul_eq_zero {P : G1} (hP : Valid P) :
    inSubgroup P = true ↔ Fr.modulus • toPoint P = 0 := by
  rw [inSubgroup]
  by_cases hi : P.isInfinity = true
  · rw [if_pos hi, (isInfinity_eq_true_iff_toPoint_eq_zero hP).mp hi]
    simp
  · rw [if_neg hi, isInfinity_eq_true_iff_toPoint_eq_zero (valid_mulNat hP _),
      toPoint_mulNat hP]

theorem modulus_sq_gt_card_bound : 2 * Fp.modulus + 1 < Fr.modulus ^ 2 := by
  decide +kernel

/-- Every r-torsion G1 curve point is a bounded natural multiple of the
standard generator; independence would force at least r² curve points. -/
theorem exists_nsmul_generator_of_modulus_smul_eq_zero {Q : curve.toAffine.Point}
    (hQ : Fr.modulus • Q = 0) :
    ∃ n : Nat, n < Fr.modulus ∧ Q = n • toPoint generator := by
  classical
  by_contra hnot
  have hind : ∀ i : Fin Fr.modulus, Q ≠ i.val • toPoint generator := by
    intro i he
    exact hnot ⟨i.val, i.isLt, he⟩
  have hd : Fr.modulus ^ 2 ∣ Nat.card curve.toAffine.Point :=
    CofactorSpan.prime_sq_dvd_card_of_independent Fr.modulus_prime
      (toPoint generator) Q modulus_smul_generator hQ toPoint_generator_ne_zero hind
  have hle := Nat.le_of_dvd (Nat.card_pos (α := curve.toAffine.Point)) hd
  have hc := card_point_le
  have hn := modulus_sq_gt_card_bound
  omega

/-- Valid representatives accepted by the subgroup check are generator
multiples, with equality in the curve group. -/
theorem exists_mulNat_generator_of_inSubgroup {P : G1} (hP : Valid P)
    (hsub : inSubgroup P = true) :
    ∃ n : Nat, n < Fr.modulus ∧ toPoint P = toPoint (mulNat generator n) := by
  obtain ⟨n, hn, he⟩ := exists_nsmul_generator_of_modulus_smul_eq_zero
    ((inSubgroup_iff_modulus_smul_eq_zero hP).mp hsub)
  exact ⟨n, hn, he.trans (toPoint_mulNat valid_generator n).symm⟩

theorem exists_mul_generator_of_inSubgroup {P : G1} (hP : Valid P)
    (hsub : inSubgroup P = true) :
    ∃ a : Fr, toPoint P = toPoint (mul generator a) := by
  obtain ⟨n, hn, he⟩ := exists_mulNat_generator_of_inSubgroup hP hsub
  exact ⟨⟨n, hn⟩, he⟩

/-- The generator multiple represents infinity precisely for the zero scalar. -/
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

end EthLib.Cryptography.Bls.G1

