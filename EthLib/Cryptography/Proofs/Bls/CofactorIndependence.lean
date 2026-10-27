import EthLib.Cryptography.Proofs.Bls.CofactorPointQ13
import EthLib.Cryptography.Proofs.Bls.CofactorPointQ23
import EthLib.Cryptography.Proofs.Bls.CofactorPointIndependent13
import EthLib.Cryptography.Proofs.Bls.CofactorPointIndependent23

/-!
# Proofs: independence of the G2 test points

For the primes 13 and 23 there are two test points of that order.

The second point is not a multiple of the first.

So each of these primes appears at least squared in the group order.
-/

namespace EthLib.Cryptography.Bls.CofactorCertificate

theorem not_nsmul_cert (P Q : G2) (hp : G2.Valid P) (hq : G2.Valid Q)
    (n fuel : Nat) (hn : n < 2 ^ fuel)
    (hc : (Q == mulAux fuel P n) = false) :
    G2.toPoint Q ≠ n • G2.toPoint P := by
  intro he
  rw [mulAux_eq fuel P n hn] at hc
  have ht : (Q == G2.mulNat P n) = true := by
    apply (G2.beq_eq_true_iff_toPoint_eq hq (G2.valid_mulNat hp n)).mpr
    simpa only [G2.toPoint_mulNat hp] using he
  rw [hc] at ht
  exact Bool.noConfusion ht

theorem independent13_not_span (i : Fin 13) :
    G2.toPoint independent13 ≠ i.val • G2.toPoint q13 := by
  have hc : ∀ i : Fin 13, (independent13 == mulAux 5 q13 i.val) = false := by
    decide +kernel
  exact not_nsmul_cert q13 independent13 q13_valid independent13_valid i.val 5
    (Nat.lt_trans i.isLt (by decide)) (hc i)

theorem independent23_not_span (i : Fin 23) :
    G2.toPoint independent23 ≠ i.val • G2.toPoint q23 := by
  have hc : ∀ i : Fin 23, (independent23 == mulAux 6 q23 i.val) = false := by
    decide +kernel
  exact not_nsmul_cert q23 independent23 q23_valid independent23_valid i.val 6
    (Nat.lt_trans i.isLt (by decide)) (hc i)

end EthLib.Cryptography.Bls.CofactorCertificate
