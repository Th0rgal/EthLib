import EthLib.Cryptography.Proofs.Bls.CofactorSubgroupPreservation

/-! The complete executable cofactor expression as an additive endomorphism.
The bridge applies to every valid twist point, not only generator multiples.
It does not yet assert that this endomorphism has r-torsion image. -/
namespace EthLib.Cryptography.Bls.HashToCurve

/-- The endomorphism polynomial implemented by `clearCofactor`. -/
noncomputable def cofactorHom : G2.curve.toAffine.Point →+ G2.curve.toAffine.Point :=
  PairingPsi.hom.comp PairingPsi.hom + PairingPsi.hom.comp PairingPsi.hom -
    PairingPsi.hom + (blsAbsX * blsAbsX + blsAbsX) • AddMonoidHom.id _ -
    blsAbsX • PairingPsi.hom - AddMonoidHom.id _

/-- Refinement of the actual cofactor implementation by its endomorphism polynomial. -/
theorem toPoint_clearCofactor {P : G2} (hP : G2.Valid P) :
    G2.toPoint (clearCofactor P) = cofactorHom (G2.toPoint P) := by
  rw [clearCofactor_group_expression hP, ← psi_psi_eq_psi2,
    PairingPsi.toPoint_psi (psi_valid (G2.valid_double hP)),
    PairingPsi.toPoint_psi (G2.valid_double hP), G2.toPoint_double hP,
    map_add, map_add, PairingPsi.toPoint_psi hP]
  rfl

/-- Cofactor clearing respects concrete addition on all valid twist representatives. -/
theorem toPoint_clearCofactor_add {P Q : G2} (hP : G2.Valid P) (hQ : G2.Valid Q) :
    G2.toPoint (clearCofactor (G2.add P Q)) =
      G2.toPoint (clearCofactor P) + G2.toPoint (clearCofactor Q) := by
  rw [toPoint_clearCofactor (G2.valid_add hP hQ), G2.toPoint_add hP hQ,
    map_add, toPoint_clearCofactor hP, toPoint_clearCofactor hQ]

/-- Cofactor clearing commutes with scalar multiplication on all valid points. -/
theorem toPoint_clearCofactor_mulNat {P : G2} (hP : G2.Valid P) (n : Nat) :
    G2.toPoint (clearCofactor (G2.mulNat P n)) = n • G2.toPoint (clearCofactor P) := by
  rw [toPoint_clearCofactor (G2.valid_mulNat hP n), G2.toPoint_mulNat hP,
    map_nsmul, toPoint_clearCofactor hP]

end EthLib.Cryptography.Bls.HashToCurve
