import EthLib.Cryptography.Proofs.Bls.PairingSourceGroup
import EthLib.Cryptography.Proofs.Bls.PairingFrobenius
import EthLib.Cryptography.Proofs.Bls.HashToCurveValidity

/-! # The p-Frobenius on the concrete pairing curve -/
namespace EthLib.Cryptography.Bls
namespace PairingTower

noncomputable def primeFrobenius : Fp12 →+* Fp12 := by
  letI : Algebra (ZMod Fp.modulus) Fp12 := fpToFp12.toAlgebra
  exact (FiniteField.frobeniusAlgHom (ZMod Fp.modulus) Fp12).toRingHom

theorem primeFrobenius_apply (a : Fp12) : primeFrobenius a = a ^ Fp.modulus := by
  change a ^ Fintype.card (ZMod Fp.modulus) = _
  rw [ZMod.card]

noncomputable def primeFrobenius2 : Fp2 →+* Fp2 := by
  letI : Algebra (ZMod Fp.modulus) Fp2 := fpToFp2.toAlgebra
  exact (FiniteField.frobeniusAlgHom (ZMod Fp.modulus) Fp2).toRingHom

theorem primeFrobenius2_apply (a : Fp2) : primeFrobenius2 a = a ^ Fp.modulus := by
  change a ^ Fintype.card (ZMod Fp.modulus) = _
  rw [ZMod.card]

theorem fp2_pow_p_eq_conjugate (a : Fp2) : a ^ Fp.modulus = a.conjugate := by
  have hi4 : Fp2.i ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by decide, pow_mul, pow_two Fp2.i, Fp2.i_sq, neg_one_sq]
  have hi3 : Fp2.i ^ 3 = -Fp2.i := by
    rw [pow_succ, pow_two, Fp2.i_sq, neg_one_mul]
  have hip : primeFrobenius2 Fp2.i = -Fp2.i := by
    rw [primeFrobenius2_apply,
      show Fp.modulus = 4 * ((Fp.modulus - 3) / 4) + 3 by decide,
      pow_add, pow_mul, hi4, one_pow, one_mul, hi3]
  have hf (b : ZMod Fp.modulus) : primeFrobenius2 (fpToFp2 b) = fpToFp2 b := by
    rw [primeFrobenius2_apply, ← map_pow, ZMod.pow_card]
  have hd : a = fpToFp2 a.c0 + fpToFp2 a.c1 * Fp2.i := by
    apply Fp2.ext <;> simp [fpToFp2]
  rw [← primeFrobenius2_apply]
  conv_lhs => rw [hd, map_add, map_mul, hf, hf, hip]
  apply Fp2.ext <;> simp [fpToFp2]

theorem primeFrobenius_fp2 (a : Fp2) :
    primeFrobenius (fp2ToFp12 a) = fp2ToFp12 a.conjugate := by
  rw [primeFrobenius_apply, ← map_pow, fp2_pow_p_eq_conjugate]

theorem primeFrobenius_fp (a : ZMod Fp.modulus) :
    primeFrobenius (fpToFp12 a) = fpToFp12 a := by
  rw [primeFrobenius_apply, ← map_pow, ZMod.pow_card]

/-- Definitionally identical to the coefficient in executable ψ. -/
def psiAlpha : Fp2 := (Fp2.powNat ⟨Fp.one, Fp.one⟩ ((Fp.modulus - 1) / 3)).inverse

def psiBeta : Fp2 := (Fp2.powNat ⟨Fp.one, Fp.one⟩ ((Fp.modulus - 1) / 2)).inverse

theorem psiAlpha_eq : psiAlpha = (Fp2.xi ^ ((Fp.modulus - 1) / 3))⁻¹ := by
  unfold psiAlpha
  rw [Fp2.powNat_eq_pow]
  rfl

theorem psiBeta_eq : psiBeta = (Fp2.xi ^ ((Fp.modulus - 1) / 2))⁻¹ := by
  unfold psiBeta
  rw [Fp2.powNat_eq_pow]
  rfl

theorem primeFrobenius_wInv2 :
    primeFrobenius Embedded.wInv2 = fp2ToFp12 psiAlpha * Embedded.wInv2 := by
  rw [wInv2_eq, primeFrobenius_apply, ← inv_pow, ← pow_mul,
    show 2 * Fp.modulus = 6 * ((Fp.modulus - 1) / 3) + 2 by decide,
    pow_add, pow_mul, inv_pow, w_sixth, inv_pow, ← map_pow, psiAlpha_eq, map_inv₀]

theorem primeFrobenius_wInv3 :
    primeFrobenius Embedded.wInv3 = fp2ToFp12 psiBeta * Embedded.wInv3 := by
  rw [wInv3_eq, primeFrobenius_apply, ← inv_pow, ← pow_mul,
    show 3 * Fp.modulus = 6 * ((Fp.modulus - 1) / 2) + 3 by decide,
    pow_add, pow_mul, inv_pow, w_sixth, inv_pow, ← map_pow, psiBeta_eq, map_inv₀]

end PairingTower
namespace PairingSource
open PairingTower Embedded

/-- The p-power map on the actual ambient elliptic-curve group. -/
noncomputable def primeFrobeniusHom : ambientCurve.Point →+ ambientCurve.Point :=
  scaledHom primeFrobenius 1 one_ne_zero (by rw [one_pow, mul_one, map_ofNat])

theorem primeFrobeniusHom_apply (P : ambientCurve.Point) :
    primeFrobeniusHom P = scaledPoint primeFrobenius 1
      (by rw [one_pow, mul_one, map_ofNat]) P := rfl

end PairingSource
end EthLib.Cryptography.Bls
