import EthLib.Cryptography.Proofs.Bls.HashToCurveValidity
import EthLib.Cryptography.Proofs.Bls.G2Subgroup

/-!
# Algebra of the concrete cofactor-clearing maps

Source: RFC 9380, Appendix G.3.
These results identify the implemented psi composition and cofactor expression.
They do not assume or prove the Frobenius characteristic polynomial.
-/
namespace EthLib.Cryptography.Bls.HashToCurve
open EthLib.Cryptography.Bls
set_option maxRecDepth 8000
set_option maxHeartbeats 1600000

private def c1 : Fp2 := (Fp2.powNat ⟨Fp.one, Fp.one⟩ ((Fp.modulus-1)/3)).inverse
private def c2 : Fp2 := (Fp2.powNat ⟨Fp.one, Fp.one⟩ ((Fp.modulus-1)/2)).inverse
private def c12 : Fp2 := ⟨(Fp.powNat (Fp.ofNat 2) ((Fp.modulus-1)/3)).inverse, Fp.zero⟩

private theorem c1_norm : c1 * c1.conjugate = c12 := by decide +kernel
private theorem c2_norm : c2 * c2.conjugate = -1 := by decide +kernel
private theorem c12_cube : c12 ^ 3 = 1 := by decide +kernel

private theorem toAffine_one (x y : Fp2) :
    G2.toAffine ⟨x, y, Fp2.one⟩ = (x,y) := by
  unfold G2.toAffine
  have hz : Fp2.one.isZero = false := by decide
  have hi : Fp2.one.inverse = (1 : Fp2) := inv_one
  simp only [hz, Bool.false_eq_true, ↓reduceIte, hi, mul_one]

private theorem psi_noninf (P : G2) (hz : P.z.isZero = false) :
    psi P = ⟨c1 * P.toAffine.1.conjugate, c2 * P.toAffine.2.conjugate, Fp2.one⟩ := by
  unfold psi
  rw [hz]
  rfl

private theorem psi2_noninf (P : G2) (hz : P.z.isZero = false) :
    psi2 P = ⟨c12 * P.toAffine.1, -P.toAffine.2, Fp2.one⟩ := by
  unfold psi2
  rw [hz]
  rfl

/-- The optimized psi2 map is exactly two applications of psi. -/
theorem psi_psi_eq_psi2 (P : G2) : psi (psi P) = psi2 P := by
  cases hz : P.z.isZero with
  | true => simp [psi, psi2, hz]
  | false =>
    rw [psi_noninf P hz]
    rw [psi_noninf _ (by rfl), psi2_noninf P hz, toAffine_one]
    simp only [Fp2.conjugate_mul, Fp2.conjugate_conjugate]
    congr 1
    · rw [← mul_assoc, c1_norm]
    · rw [← mul_assoc, c2_norm, neg_one_mul]

/-- Applying the optimized psi2 map three times negates affine coordinates. -/
theorem psi2_cube_noninf (P : G2) (hz : P.z.isZero = false) :
    psi2 (psi2 (psi2 P)) = ⟨P.toAffine.1, -P.toAffine.2, Fp2.one⟩ := by
  rw [psi2_noninf P hz, psi2_noninf _ (by rfl), psi2_noninf _ (by rfl)]
  simp only [toAffine_one, neg_neg]
  congr 1
  have h := congrArg (fun c : Fp2 => c * P.toAffine.1) c12_cube
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h

/-- The negative BLS scalar is represented by the group scalar action. -/
theorem toPoint_mulNegX {P : G2} (hP : G2.Valid P) :
    G2.toPoint (mulNegX P) = -(blsAbsX • G2.toPoint P) := by
  rw [mulNegX, G2.toPoint_neg (G2.valid_mulNat hP _), G2.toPoint_mulNat hP]

/-- The implemented cofactor expression agrees with its group polynomial.
The psi2 term still applies to twice the input; this does not assert a
Frobenius characteristic relation or a subgroup annihilator. -/
theorem clearCofactor_group_expression {P : G2} (hP : G2.Valid P) :
    G2.toPoint (clearCofactor P) =
      G2.toPoint (psi2 (G2.double P)) - G2.toPoint (psi P) +
      (blsAbsX * blsAbsX + blsAbsX) • G2.toPoint P -
      blsAbsX • G2.toPoint (psi P) - G2.toPoint P := by
  unfold clearCofactor
  rw [G2.toPoint_add (G2.valid_add (G2.valid_add
    (G2.valid_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP)))
    (mulNegX_valid (G2.valid_add (mulNegX_valid hP) (psi_valid hP))))
    (G2.valid_neg (mulNegX_valid hP))) (G2.valid_neg hP)]
  rw [G2.toPoint_add (G2.valid_add
    (G2.valid_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP)))
    (mulNegX_valid (G2.valid_add (mulNegX_valid hP) (psi_valid hP))))
    (G2.valid_neg (mulNegX_valid hP))]
  rw [G2.toPoint_add
    (G2.valid_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP)))
    (mulNegX_valid (G2.valid_add (mulNegX_valid hP) (psi_valid hP)))]
  rw [G2.toPoint_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP)),
    G2.toPoint_neg (psi_valid hP), G2.toPoint_neg (mulNegX_valid hP),
    G2.toPoint_neg hP, toPoint_mulNegX (G2.valid_add (mulNegX_valid hP) (psi_valid hP)),
    G2.toPoint_add (mulNegX_valid hP) (psi_valid hP), toPoint_mulNegX hP]
  module

end EthLib.Cryptography.Bls.HashToCurve
