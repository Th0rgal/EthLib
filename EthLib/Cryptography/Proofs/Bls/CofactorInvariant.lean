import EthLib.Cryptography.Proofs.Bls.CofactorAlgebra
import EthLib.Cryptography.Proofs.Bls.PairingInvariant

/-! Projective representation independence of the concrete cofactor maps.
These results do not assert that the output is r-torsion. -/
namespace EthLib.Cryptography.Bls.HashToCurve

/-- Cofactor clearing is well-defined on valid projective curve points. -/
theorem clearCofactor_beq_of_beq {P Q : G2} (hP : G2.Valid P) (hQ : G2.Valid Q)
    (h : (P == Q) = true) : (clearCofactor P == clearCofactor Q) = true := by
  apply (G2.beq_eq_true_iff_toPoint_eq (clearCofactor_valid hP)
    (clearCofactor_valid hQ)).mpr
  have he := (G2.beq_eq_true_iff_toPoint_eq hP hQ).mp h
  have hs := (G2.beq_eq_true_iff_toPoint_eq (psi_valid hP) (psi_valid hQ)).mp
    (psi_beq_of_beq h)
  have hd : (G2.double P == G2.double Q) = true := by
    apply (G2.beq_eq_true_iff_toPoint_eq (G2.valid_double hP) (G2.valid_double hQ)).mpr
    rw [G2.toPoint_double hP, G2.toPoint_double hQ, he]
  have ht := (G2.beq_eq_true_iff_toPoint_eq (psi2_valid (G2.valid_double hP))
    (psi2_valid (G2.valid_double hQ))).mp (psi2_beq_of_beq hd)
  rw [clearCofactor_group_expression hP, clearCofactor_group_expression hQ, he, hs, ht]

end EthLib.Cryptography.Bls.HashToCurve
