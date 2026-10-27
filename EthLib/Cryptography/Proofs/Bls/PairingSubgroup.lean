import EthLib.Cryptography.Proofs.Bls.G2SubgroupSpan
import EthLib.Cryptography.Proofs.Bls.PairingNondegenerate

/-! Signed executable optimal-Ate bilinearity for arbitrary representatives
accepted by the concrete G2 subgroup check. -/
namespace EthLib.Cryptography.Bls

theorem pairing_eq_of_g2_toPoint_eq (p : G1) {q t : G2}
    (hq : G2.Valid q) (ht : G2.Valid t) (he : G2.toPoint q = G2.toPoint t) :
    pairing p q = pairing p t :=
  pairing_eq_of_g2_beq p ((G2.beq_eq_true_iff_toPoint_eq hq ht).mpr he)

/-- G2 scalar bilinearity for every valid point passing the actual subgroup check. -/
theorem pairing_mulNat_g2_of_inSubgroup {p : G1} {q : G2}
    (hp : G1.Valid p) (hq : G2.Valid q) (hs : G2.inSubgroup q = true) (n : Nat) :
    pairing p (G2.mulNat q n) = pairing p q ^ n := by
  obtain ⟨m, _, hm⟩ := G2.exists_nsmul_generator_of_modulus_smul_eq_zero
    ((G2.inSubgroup_iff_modulus_smul_eq_zero hq).mp hs)
  have he : G2.toPoint q = G2.toPoint (G2.mulNat G2.generator m) := by
    rw [G2.toPoint_mulNat G2.valid_generator, hm]
  have hen : G2.toPoint (G2.mulNat q n) =
      G2.toPoint (G2.mulNat G2.generator (m * n)) := by
    rw [G2.toPoint_mulNat hq, G2.toPoint_mulNat G2.valid_generator, hm, mul_nsmul]
  rw [pairing_eq_of_g2_toPoint_eq p (G2.valid_mulNat hq n)
      (G2.valid_mulNat G2.valid_generator (m * n)) hen,
    pairing_eq_of_g2_toPoint_eq p hq (G2.valid_mulNat G2.valid_generator m) he,
    pairing_mulNat_g2_generator hp, pairing_mulNat_g2_generator hp, pow_mul]

/-- G2 additivity for arbitrary valid checked subgroup representatives. -/
theorem pairing_add_g2_of_inSubgroup {p : G1} {q t : G2}
    (hp : G1.Valid p) (hq : G2.Valid q) (ht : G2.Valid t)
    (hqs : G2.inSubgroup q = true) (hts : G2.inSubgroup t = true) :
    pairing p (G2.add q t) = pairing p q * pairing p t := by
  obtain ⟨m, _, hm⟩ := G2.exists_nsmul_generator_of_modulus_smul_eq_zero
    ((G2.inSubgroup_iff_modulus_smul_eq_zero hq).mp hqs)
  obtain ⟨n, _, hn⟩ := G2.exists_nsmul_generator_of_modulus_smul_eq_zero
    ((G2.inSubgroup_iff_modulus_smul_eq_zero ht).mp hts)
  have heq : G2.toPoint q = G2.toPoint (G2.mulNat G2.generator m) := by
    rwa [G2.toPoint_mulNat G2.valid_generator]
  have het : G2.toPoint t = G2.toPoint (G2.mulNat G2.generator n) := by
    rwa [G2.toPoint_mulNat G2.valid_generator]
  have hea : G2.toPoint (G2.add q t) =
      G2.toPoint (G2.mulNat G2.generator (m + n)) := by
    rw [G2.toPoint_add hq ht, G2.toPoint_mulNat G2.valid_generator, hm, hn, add_nsmul]
  rw [pairing_eq_of_g2_toPoint_eq p (G2.valid_add hq ht)
      (G2.valid_mulNat G2.valid_generator (m + n)) hea,
    pairing_eq_of_g2_toPoint_eq p hq (G2.valid_mulNat G2.valid_generator m) heq,
    pairing_eq_of_g2_toPoint_eq p ht (G2.valid_mulNat G2.valid_generator n) het,
    pairing_mulNat_g2_generator hp, pairing_mulNat_g2_generator hp,
    pairing_mulNat_g2_generator hp, pow_add]

/-- G1 additivity when the second argument is any valid checked G2 point. -/
theorem pairing_add_g1_of_g2_inSubgroup {p t : G1} {q : G2}
    (hp : G1.Valid p) (ht : G1.Valid t) (hq : G2.Valid q)
    (hs : G2.inSubgroup q = true) :
    pairing (G1.add p t) q = pairing p q * pairing t q := by
  obtain ⟨m, _, hm⟩ := G2.exists_mulNat_generator_of_inSubgroup hq hs
  rw [pairing_eq_of_g2_toPoint_eq (G1.add p t) hq
      (G2.valid_mulNat G2.valid_generator m) hm,
    pairing_eq_of_g2_toPoint_eq p hq (G2.valid_mulNat G2.valid_generator m) hm,
    pairing_eq_of_g2_toPoint_eq t hq (G2.valid_mulNat G2.valid_generator m) hm]
  exact pairing_add_g1_generator_mulNat hp ht m

theorem pairing_mulNat_g1_of_g2_inSubgroup {p : G1} {q : G2}
    (hp : G1.Valid p) (hq : G2.Valid q) (hs : G2.inSubgroup q = true) (n : Nat) :
    pairing (G1.mulNat p n) q = pairing p q ^ n := by
  obtain ⟨m, _, hm⟩ := G2.exists_mulNat_generator_of_inSubgroup hq hs
  rw [pairing_eq_of_g2_toPoint_eq (G1.mulNat p n) hq
      (G2.valid_mulNat G2.valid_generator m) hm,
    pairing_eq_of_g2_toPoint_eq p hq (G2.valid_mulNat G2.valid_generator m) hm]
  exact pairing_mulNat_g1_generator_mulNat hp m n

theorem pairing_mulNat_of_inSubgroup {p : G1} {q : G2}
    (hp : G1.Valid p) (hq : G2.Valid q) (hs : G2.inSubgroup q = true) (m n : Nat) :
    pairing (G1.mulNat p m) (G2.mulNat q n) = pairing p q ^ (m * n) := by
  rw [pairing_mulNat_g2_of_inSubgroup (G1.valid_mulNat hp m) hq hs n,
    pairing_mulNat_g1_of_g2_inSubgroup hp hq hs m, ← pow_mul]

end EthLib.Cryptography.Bls

