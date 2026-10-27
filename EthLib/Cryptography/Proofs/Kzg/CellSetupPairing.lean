import EthLib.Cryptography.Proofs.Kzg.CellEquation
import EthLib.Cryptography.Proofs.Kzg.SetupCommitment

namespace EthLib.Cryptography.Kzg.Opening
open Bls (Fr G1 G2)
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

/-- Exact concrete pairing orientation used by `verifyCellKzgProofBatchImpl`.
    The three G1 terms are the commitment, interpolant, and weighted proof. -/
theorem cell_setup_pairing_complete
    (setup : TrustedSetup) (τ h : Fr) (n : Nat)
    (hsetup : MonomialSetup setup τ)
    (hg2_zero : 0 < setup.g2Monomial.size)
    (hg2_n : n < setup.g2Monomial.size)
    (ll rlc rli rlp : G1) (p I Q : _root_.Polynomial Fr)
    (hll_valid : G1.Valid ll) (hrlc_valid : G1.Valid rlc)
    (hrli_valid : G1.Valid rli) (hrlp_valid : G1.Valid rlp)
    (hll : G1.toPoint ll = G1.ofFr (Q.eval τ))
    (hrlc : G1.toPoint rlc = G1.ofFr (p.eval τ))
    (hrli : G1.toPoint rli = G1.ofFr (I.eval τ))
    (hrlp : G1.toPoint rlp = G1.ofFr (h^n * Q.eval τ))
    (hid : p - I = Q * (Polynomial.X ^ n - Polynomial.C (h^n))) :
    let lr := setup.g2Monomial[n]!
    let rl := G1.add (G1.add rlc (G1.neg rli)) rlp
    Bls.pairingCheck #[(ll, lr), (rl, G2.neg setup.g2Monomial[0]!)] = true := by
  intro lr rl
  have hrl_sub_valid : G1.Valid (G1.add rlc (G1.neg rli)) :=
    G1.valid_add hrlc_valid (G1.valid_neg hrli_valid)
  have hrl_valid : G1.Valid rl := G1.valid_add hrl_sub_valid hrlp_valid
  have hrl_point : G1.toPoint rl = G1.ofFr
      (p.eval τ - I.eval τ + h^n * Q.eval τ) := by
    rw [G1.toPoint_add hrl_sub_valid hrlp_valid,
      G1.toPoint_add hrlc_valid (G1.valid_neg hrli_valid),
      G1.toPoint_neg hrli_valid, hrlc, hrli, hrlp,
      ← g1_ofFr_neg, ← G1.ofFr_add, ← G1.ofFr_add]
    exact congrArg (fun a : Fr => G1.ofFr (a + h^n * Q.eval τ))
      (sub_eq_add_neg (p.eval τ) (I.eval τ)).symm
  have hg2_0_point : G2.toPoint setup.g2Monomial[0]! = G2.ofFr 1 := by
    simpa only [pow_zero] using hsetup.g2_power 0 (by omega)
  apply (pairingCheck_neg_g2_iff ll rl lr setup.g2Monomial[0]!
    (Q.eval τ) (τ^n) (p.eval τ - I.eval τ + h^n * Q.eval τ) 1
    hll_valid hrl_valid (hsetup.g2_valid n hg2_n)
    (hsetup.g2_valid 0 hg2_zero) hll hrl_point
    (hsetup.g2_power n hg2_n) hg2_0_point).mpr
  simpa only [Fin.mul_one] using
    (cell_scalar_identity p I Q τ h n hid).symm

end EthLib.Cryptography.Kzg.Opening
