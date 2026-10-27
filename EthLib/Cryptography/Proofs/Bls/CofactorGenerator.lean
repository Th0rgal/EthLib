import EthLib.Cryptography.Proofs.Bls.CofactorSubgroupPreservation

/-!
# The exact cofactor-clearing action on concrete generator multiples

The scalar is derived from the executable cofactor expression and the proved
psi eigenrelation, not assumed. These results do not establish the image of
cofactor clearing for arbitrary points outside the generator subgroup.
-/
namespace EthLib.Cryptography.Bls.HashToCurve

/-- Scalar induced by the implemented cofactor map on the generator subgroup. -/
def cofactorGeneratorScalar : Nat := 4 * blsAbsX * blsAbsX + 2 * blsAbsX - 1

private theorem scalar_succ : cofactorGeneratorScalar + 1 =
    4 * blsAbsX * blsAbsX + 2 * blsAbsX := by decide +kernel

/-- Exact group action of the executable cofactor map on every generator multiple. -/
theorem clearCofactor_generator_multiple (n : Nat) :
    G2.toPoint (clearCofactor (G2.mulNat G2.generator n)) =
      cofactorGeneratorScalar • (n • G2.toPoint G2.generator) := by
  have hP := G2.valid_mulNat G2.valid_generator n
  rw [clearCofactor_group_expression hP]
  rw [← psi_psi_eq_psi2, PairingPsi.toPoint_psi (psi_valid (G2.valid_double hP)),
    PairingPsi.toPoint_psi (G2.valid_double hP), G2.toPoint_double hP,
    map_add, map_add, G2.toPoint_mulNat G2.valid_generator,
    PairingPsi.hom_generator_nsmul, map_neg, map_nsmul,
    PairingPsi.hom_generator_nsmul,
    PairingPsi.toPoint_psi hP, G2.toPoint_mulNat G2.valid_generator,
    PairingPsi.hom_generator_nsmul]
  calc
    _ = (4 * blsAbsX * blsAbsX + 2 * blsAbsX) •
        (n • G2.toPoint G2.generator) - n • G2.toPoint G2.generator := by module
    _ = _ := by rw [← scalar_succ, add_nsmul, one_nsmul, add_sub_cancel_right]

/-- Every cofactor-cleared concrete generator multiple passes the subgroup check. -/
theorem clearCofactor_mulNat_generator_inSubgroup (n : Nat) :
    G2.inSubgroup (clearCofactor (G2.mulNat G2.generator n)) = true :=
  clearCofactor_inSubgroup_of_inSubgroup (G2.valid_mulNat G2.valid_generator n)
    (G2.inSubgroup_mulNat G2.valid_generator G2.inSubgroup_generator n)

/-- Cofactor clearing the generator does not collapse it to infinity. -/
theorem clearCofactor_generator_not_infinity :
    (clearCofactor G2.generator).isInfinity = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hz := (G2.isInfinity_eq_true_iff_toPoint_eq_zero
    (clearCofactor_valid G2.valid_generator)).mp h
  have hc := clearCofactor_generator_multiple 1
  have hm : G2.mulNat G2.generator 1 = G2.generator := by decide +kernel
  rw [hm, one_nsmul] at hc
  rw [hc, ← addOrderOf_dvd_iff_nsmul_eq_zero, G2.addOrderOf_toPoint_generator] at hz
  have hn : ¬Fr.modulus ∣ cofactorGeneratorScalar := by decide +kernel
  exact hn hz

end EthLib.Cryptography.Bls.HashToCurve
