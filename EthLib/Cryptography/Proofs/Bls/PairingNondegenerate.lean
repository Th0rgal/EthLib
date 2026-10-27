import EthLib.Cryptography.Proofs.Bls.PairingChecker
import EthLib.Cryptography.Proofs.Bls.PairingGeneratorNontrivial
namespace EthLib.Cryptography.Bls
open scoped Fr

/-- The signed generator pairing has exact prime order r. -/
theorem pairing_generator_order :
    orderOf (pairing G1.generator G2.generator) = Fr.modulus := by
  exact orderOf_eq_prime (pairing_pow_modulus G1.valid_generator G2.valid_generator) PairingCertificate.generator_pairing_ne_one

theorem pairing_generators_eq_iff
    (a b c d : Fr) :
    pairing (G1.mul G1.generator a) (G2.mul G2.generator b) =
      pairing (G1.mul G1.generator c) (G2.mul G2.generator d) ↔ a * b = c * d := by
  change pairing (G1.mulNat G1.generator a.val) (G2.mulNat G2.generator b.val) =
    pairing (G1.mulNat G1.generator c.val) (G2.mulNat G2.generator d.val) ↔ _
  rw [pairing_mulNat_generators, pairing_mulNat_generators]
  have hf : IsOfFinOrder (pairing G1.generator G2.generator) := by
    rw [← orderOf_pos_iff, pairing_generator_order]
    exact Fr.modulus_pos
  rw [hf.pow_inj_mod, pairing_generator_order]
  exact (@Fin.ext_iff _ (a * b) (c * d)).symm

theorem pairingCheck_generators_iff
    (a b c d : Fr) :
    pairingCheck #[(G1.mul G1.generator a, G2.mul G2.generator b),
      (G1.neg (G1.mul G1.generator c), G2.mul G2.generator d)] = true ↔ a * b = c * d := by
  rw [pairingCheck_two]
  change pairing (G1.mulNat G1.generator a.val) (G2.mulNat G2.generator b.val) *
    pairing (G1.neg (G1.mulNat G1.generator c.val)) (G2.mulNat G2.generator d.val) = 1 ↔ _
  rw [pairing_neg_g1_generator_mulNat (G1.valid_mulNat G1.valid_generator c.val)]
  rw [mul_inv_eq_one₀ (pairing_ne_zero (G1.valid_mulNat G1.valid_generator c.val)
    (G2.valid_mulNat G2.valid_generator d.val))]
  exact pairing_generators_eq_iff a b c d

/-- On the two prime-order generator spans, the pairing is one precisely when
    at least one scalar is zero. -/
theorem pairing_mul_generators_eq_one_iff (a b : Fr) :
    pairing (G1.mul G1.generator a) (G2.mul G2.generator b) = 1 ↔ a = 0 ∨ b = 0 := by
  have h := pairing_generators_eq_iff a b 0 0
  have hz : G1.mul G1.generator (0 : Fr) = G1.zero := by
    change G1.mulNat G1.generator 0 = G1.zero
    rw [G1.mulNat_def]
    rfl
  rw [hz, pairing_zero_left, Fp12.one_eq_one, zero_mul] at h
  apply h.trans
  exact @mul_eq_zero (ZMod Fr.modulus) _ _ a b

end EthLib.Cryptography.Bls
