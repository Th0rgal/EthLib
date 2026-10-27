import EthLib.Cryptography.Proofs.Bls.PairingPsi
import EthLib.Cryptography.Proofs.Bls.CofactorAlgebra

/-!
# Cofactor clearing on the existing r-subgroup

The concrete psi endomorphism preserves r-torsion, so the executable cofactor
map preserves membership in the checked subgroup. This is not the stronger
claim that cofactor clearing sends every valid curve point into that subgroup.
-/
namespace EthLib.Cryptography.Bls.HashToCurve

/-- The actual psi implementation preserves checked subgroup membership. -/
theorem psi_inSubgroup {P : G2} (hP : G2.Valid P) (hs : G2.inSubgroup P = true) :
    G2.inSubgroup (psi P) = true := by
  apply (G2.inSubgroup_iff_modulus_smul_eq_zero (psi_valid hP)).mpr
  rw [PairingPsi.toPoint_psi hP, ← map_nsmul,
    (G2.inSubgroup_iff_modulus_smul_eq_zero hP).mp hs, map_zero]

/-- The actual optimized psi2 implementation preserves checked subgroup membership. -/
theorem psi2_inSubgroup {P : G2} (hP : G2.Valid P) (hs : G2.inSubgroup P = true) :
    G2.inSubgroup (psi2 P) = true := by
  rw [← psi_psi_eq_psi2]
  exact psi_inSubgroup (psi_valid hP) (psi_inSubgroup hP hs)

/-- Cofactor clearing preserves the checked subgroup on valid input representatives.
The input subgroup premise is essential to the scope of this theorem. -/
theorem clearCofactor_inSubgroup_of_inSubgroup {P : G2} (hP : G2.Valid P)
    (hs : G2.inSubgroup P = true) : G2.inSubgroup (clearCofactor P) = true := by
  apply (G2.inSubgroup_iff_modulus_smul_eq_zero (clearCofactor_valid hP)).mpr
  rw [clearCofactor_group_expression hP]
  have h0 := (G2.inSubgroup_iff_modulus_smul_eq_zero hP).mp hs
  have h1 := (G2.inSubgroup_iff_modulus_smul_eq_zero (psi_valid hP)).mp
    (psi_inSubgroup hP hs)
  have hd : G2.inSubgroup (G2.double P) = true := by
    apply (G2.inSubgroup_iff_modulus_smul_eq_zero (G2.valid_double hP)).mpr
    rw [G2.toPoint_double hP, nsmul_add, h0, zero_add]
  have h2 := (G2.inSubgroup_iff_modulus_smul_eq_zero (psi2_valid (G2.valid_double hP))).mp
    (psi2_inSubgroup (G2.valid_double hP) hd)
  simp only [nsmul_sub, nsmul_add, h0, h1, h2]
  rw [smul_comm Fr.modulus (blsAbsX * blsAbsX + blsAbsX),
    smul_comm Fr.modulus blsAbsX, h0, h1]
  simp

end EthLib.Cryptography.Bls.HashToCurve
