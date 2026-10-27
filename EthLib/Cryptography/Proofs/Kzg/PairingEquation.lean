import EthLib.Cryptography.Proofs.Kzg.OpeningAlgebra

namespace EthLib.Cryptography.Kzg.Opening
open Bls (Fr G1 G2)
open scoped EthLib.Cryptography.Bls.Fr

/-- Scalar semantics for two arbitrary valid representatives with negation in G2.
    This is the exact orientation used by the cell batch verifier. -/
theorem pairingCheck_neg_g2_iff (p t : G1) (q u : G2) (a b c d : Fr)
    (hp : G1.Valid p) (ht : G1.Valid t) (hq : G2.Valid q) (hu : G2.Valid u)
    (hep : G1.toPoint p = G1.ofFr a) (het : G1.toPoint t = G1.ofFr c)
    (heq : G2.toPoint q = G2.ofFr b) (heu : G2.toPoint u = G2.ofFr d) :
    Bls.pairingCheck #[(p,q),(t,G2.neg u)] = true ↔ a*b = c*d := by
  rw [Bls.pairingCheck_two]
  rw [pairing_congr hp (G1.valid_mul G1.valid_generator a)
    hq (G2.valid_mul G2.valid_generator b)
    (hep.trans (G1.toPoint_mul_generator _).symm)
    (heq.trans (G2.toPoint_mul_generator _).symm)]
  rw [pairing_congr ht (G1.valid_neg (G1.valid_mul G1.valid_generator (-c)))
    (G2.valid_neg hu) (G2.valid_mul G2.valid_generator (-d)) (by
      rw [G1.toPoint_neg (G1.valid_mul G1.valid_generator (-c)),
        G1.toPoint_mul_generator, g1_ofFr_neg, neg_neg]
      exact het) (by
      rw [G2.toPoint_neg hu, heu, G2.toPoint_mul_generator, g2_ofFr_neg])]
  rw [← Bls.pairingCheck_two, Bls.pairingCheck_generators_iff]
  have he : (-c)*(-d) = c*d := neg_mul_neg c d
  rw [he]

/-- The generator scalar map is injective, from its checked exact order. -/
theorem g1_ofFr_injective : Function.Injective G1.ofFr := by
  intro a b he
  have h := (Bls.pairing_generators_eq_iff a 1 b 1).mp
    (pairing_congr (G1.valid_mul G1.valid_generator a)
      (G1.valid_mul G1.valid_generator b)
      (G2.valid_mul G2.valid_generator 1) (G2.valid_mul G2.valid_generator 1)
      (by simpa only [G1.toPoint_mul_generator] using he) rfl)
  simpa only [Fin.mul_one] using h

end EthLib.Cryptography.Kzg.Opening
