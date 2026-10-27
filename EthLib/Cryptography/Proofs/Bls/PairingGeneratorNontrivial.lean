import EthLib.Cryptography.Proofs.Bls.PairingGeneratorExp8
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace EthLib.Cryptography.Bls.PairingCertificate
open scoped EthLib.Cryptography.Bls.Fp
theorem pairing_value : pairing G1.generator G2.generator = e4313 := by
  calc
    pairing G1.generator G2.generator = finalExponentiation f62.conjugate :=
      congrArg (fun f : Fp12 => finalExponentiation f.conjugate) loop_eq
    _ = finalExponentiation base := congrArg finalExponentiation base_eq
    _ = base ^ finalExpExponent := Fp12.powNat_eq_pow _ _
    _ = e4313 := exp4313

theorem generator_pairing_ne_one : pairing G1.generator G2.generator ≠ 1 := by
  rw [pairing_value]
  decide +kernel

end EthLib.Cryptography.Bls.PairingCertificate

