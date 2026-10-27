import EthLib.Cryptography.Proofs.Bls.PairingSubgroup
import EthLib.Cryptography.Proofs.Bls.G1SubgroupSpan

/-! Nondegeneracy of the actual signed pairing on both subgroups accepted by
the executable subgroup checks, including arbitrary valid representatives. -/
namespace EthLib.Cryptography.Bls

/-- On valid accepted subgroup inputs, the pairing is one exactly when one
input is the curve identity. -/
theorem pairing_eq_one_iff_of_inSubgroup {p : G1} {q : G2}
    (hp : G1.Valid p) (hq : G2.Valid q)
    (hps : G1.inSubgroup p = true) (hqs : G2.inSubgroup q = true) :
    pairing p q = 1 ↔ p.isInfinity = true ∨ q.isInfinity = true := by
  obtain ⟨a, ha⟩ := G1.exists_mul_generator_of_inSubgroup hp hps
  obtain ⟨b, hb⟩ := G2.exists_mul_generator_of_inSubgroup hq hqs
  have he : pairing p q = pairing (G1.mul G1.generator a) (G2.mul G2.generator b) := by
    rw [pairing_eq_of_g1_toPoint_eq hp (G1.valid_mul G1.valid_generator a) hq ha,
      pairing_eq_of_g2_toPoint_eq (G1.mul G1.generator a) hq
        (G2.valid_mul G2.valid_generator b) hb]
  have hpa : p.isInfinity = true ↔ a = 0 := by
    rw [G1.isInfinity_eq_true_iff_toPoint_eq_zero hp, ha,
      ← G1.isInfinity_eq_true_iff_toPoint_eq_zero (G1.valid_mul G1.valid_generator a),
      G1.mul_generator_isInfinity_iff]
  have hqb : q.isInfinity = true ↔ b = 0 := by
    rw [G2.isInfinity_eq_true_iff_toPoint_eq_zero hq, hb,
      ← G2.isInfinity_eq_true_iff_toPoint_eq_zero (G2.valid_mul G2.valid_generator b),
      G2.mul_generator_isInfinity_iff]
  rw [he, pairing_mul_generators_eq_one_iff, hpa, hqb]

/-- Any pair of nonidentity accepted subgroup points has nontrivial pairing. -/
theorem pairing_ne_one_of_inSubgroup {p : G1} {q : G2}
    (hp : G1.Valid p) (hq : G2.Valid q)
    (hps : G1.inSubgroup p = true) (hqs : G2.inSubgroup q = true)
    (hpi : p.isInfinity = false) (hqi : q.isInfinity = false) :
    pairing p q ≠ 1 := by
  intro he
  have hz := (pairing_eq_one_iff_of_inSubgroup hp hq hps hqs).mp he
  cases hz with
  | inl h => exact Bool.noConfusion (hpi ▸ h)
  | inr h => exact Bool.noConfusion (hqi ▸ h)

end EthLib.Cryptography.Bls

#print axioms EthLib.Cryptography.Bls.pairing_eq_one_iff_of_inSubgroup
#print axioms EthLib.Cryptography.Bls.pairing_ne_one_of_inSubgroup
