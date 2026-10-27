import EthLib.Cryptography.Proofs.Bls.CofactorCertificateHelpers

/-!
# Proofs: a G2 test point of order 23, independent of the first

A certificate point used to bound the size of the G2 curve group.

The file proves, by kernel evaluation, that the point:

- lies on the curve,
- is not the point at infinity,
- is killed by multiplication by 23, independent of the first,
- is sent to infinity by the cofactor-clearing formula, computed with fuel-bounded multiplication.
-/
namespace EthLib.Cryptography.Bls.CofactorCertificate
def independent23 : G2 := ⟨⟨Fp.ofNat 2709995428003268608871894472228856346337839268359478051610933685877360518813348186307165653556980764463340627527317, Fp.ofNat 3554443526158050189626448917867136396708755108860714478547527567704052590003136535872275788661066543853688497564247⟩, ⟨Fp.ofNat 1473716000648057153732370793749569872625382979758951807858832989805910300066502167700706499893185223611335808515777, Fp.ofNat 3344235560376118688516689358070514142701873435005234113818031012772657324870196060098815547126141301608517003735704⟩, Fp2.one⟩
theorem independent23_valid : G2.Valid independent23 := G2.valid_of_affine_equation (by decide +kernel)
theorem independent23_nonzero : G2.toPoint independent23 ≠ 0 := by
  intro hz
  have h := (G2.isInfinity_eq_true_iff_toPoint_eq_zero independent23_valid).mpr hz
  exact Bool.noConfusion h
theorem independent23_annihilator : 23 • G2.toPoint independent23 = 0 :=
  nsmul_zero_cert independent23 independent23_valid 23 6 (by decide +kernel) (by decide +kernel)
theorem independent23_clear_zero : (clearAux independent23).isInfinity = true := by decide +kernel
end EthLib.Cryptography.Bls.CofactorCertificate
