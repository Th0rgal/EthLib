import EthLib.Cryptography.Proofs.Bls.CofactorAlgebra
import EthLib.Cryptography.Proofs.Bls.PairingInvariant

/-! Projective representation independence of the concrete cofactor maps.
These results do not assert that the output is r-torsion. -/
namespace EthLib.Cryptography.Bls.HashToCurve

private theorem infinity_eq_of_beq {P Q : G2} (h : (P == Q) = true) :
    P.z.isZero = Q.z.isZero := by
  change (if P.z.isZero then Q.z.isZero else if Q.z.isZero then false else _) = true at h
  cases hp : P.z.isZero <;> cases hq : Q.z.isZero <;> simp_all

/-- Psi respects projective equality, including arbitrary infinity representatives. -/
theorem psi_beq_of_beq {P Q : G2} (h : (P == Q) = true) :
    (psi P == psi Q) = true := by
  have hi := infinity_eq_of_beq h
  unfold psi
  cases hp : P.z.isZero with
  | true => simpa [hp, ← hi] using h
  | false =>
    simp only [hp, ← hi, Bool.false_eq_true, ↓reduceIte]
    rw [G2.toAffine_eq_of_beq h]
    exact G2.beq_refl _

/-- The optimized psi2 map also respects projective equality. -/
theorem psi2_beq_of_beq {P Q : G2} (h : (P == Q) = true) :
    (psi2 P == psi2 Q) = true := by
  rw [← psi_psi_eq_psi2, ← psi_psi_eq_psi2]
  exact psi_beq_of_beq (psi_beq_of_beq h)

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
