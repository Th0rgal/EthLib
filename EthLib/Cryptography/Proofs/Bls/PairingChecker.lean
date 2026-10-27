import EthLib.Cryptography.Proofs.Bls.PairingSignedG2

/-!
# Proofs: the pairing check is a product of pairings

The check multiplies the Miller values of all pairs and applies one final exponentiation.

Pairs with the point at infinity contribute 1.

So the check passes exactly when the product of the individual pairings is 1.
-/
namespace EthLib.Cryptography.Bls

/-- The implementation's skipped identity pairs contribute the neutral Miller value. -/
def checkedMiller (p : G1) (q : G2) : Fp12 :=
  if p.isInfinity || q.isInfinity then 1
  else (millerLoop blsX (Embedded.ofG2 q) (Embedded.ofG1 p)).conjugate

theorem checkedMiller_final (p : G1) (q : G2) :
    finalExponentiation (checkedMiller p q) = pairing p q := by
  unfold checkedMiller
  split
  · rename_i hi
    have hi' := Bool.or_eq_true_iff.mp hi
    rcases hi' with hp | hq
    · rw [pairing_of_g1_inf hp]
      exact finalExponentiation_one
    · rw [pairing_of_g2_inf hq]
      exact finalExponentiation_one
  · rfl

theorem pairingCheck_two (p t : G1) (q u : G2) :
    pairingCheck #[(p,q),(t,u)] = true ↔ pairing p q * pairing t u = 1 := by
  have he : pairingCheck #[(p,q),(t,u)] =
      (finalExponentiation (checkedMiller p q * checkedMiller t u)).isOne := by
    unfold pairingCheck checkedMiller
    split <;> split <;> simp_all [Fp12.one_eq_one]
  rw [he, Fp12.isOne_iff, finalExponentiation_mul, checkedMiller_final, checkedMiller_final]

theorem pairing_neg_g1_generator_mulNat {p : G1} (hp : G1.Valid p) (k : Nat) :
    pairing (G1.neg p) (G2.mulNat G2.generator k) =
      (pairing p (G2.mulNat G2.generator k))⁻¹ := by
  have hadd := pairing_add_g1_generator_mulNat hp (G1.valid_neg hp) k
  have hz : G1.toPoint (G1.add p (G1.neg p)) = G1.toPoint G1.zero := by
    rw [G1.toPoint_add hp (G1.valid_neg hp), G1.toPoint_neg hp, add_neg_cancel,
      G1.toPoint_zero]
  have he := pairing_eq_of_g1_toPoint_eq (G1.valid_add hp (G1.valid_neg hp)) G1.valid_zero
    (G2.valid_mulNat G2.valid_generator k) hz
  rw [he, pairing_zero_left, Fp12.one_eq_one] at hadd
  exact (inv_eq_of_mul_eq_one_right hadd.symm).symm

end EthLib.Cryptography.Bls
