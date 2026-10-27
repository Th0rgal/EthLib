import EthLib.Cryptography.Proofs.Kzg.PairingEquation
import Mathlib.Algebra.Polynomial.Div

namespace EthLib.Cryptography.Kzg.Opening
open Bls (Fr G1 G2)
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

private theorem cell_rearrange {R : Type*} [CommRing R] (a i q t b : R)
    (he : a-i = q*(t-b)) : a-i+b*q = q*t := by linear_combination he

/-- The scalar equation behind a cell opening: `p-I=Q(X)(X^n-h^n)`. -/
theorem cell_scalar_identity (p I Q : _root_.Polynomial Fr) (τ h : Fr) (n : Nat)
    (hid : p - I = Q * (Polynomial.X ^ n - Polynomial.C (h^n))) :
    p.eval τ - I.eval τ + h^n * Q.eval τ = Q.eval τ * τ^n := by
  have he := congrArg (fun f : _root_.Polynomial Fr => f.eval τ) hid
  simp only [Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at he
  exact cell_rearrange _ _ _ _ _ he

/-- Exact verifier completeness for one cell equation, in the actual checker orientation.
    The setup relation is represented by the scalar `τ`; no verifier result is assumed. -/
theorem cell_pairing_complete (ll rl : G1) (lr : G2)
    (τ h : Fr) (n : Nat) (q rlc rli : Fr)
    (hp : G1.Valid ll) (hr : G1.Valid rl) (hlr : G2.Valid lr)
    (hll : G1.toPoint ll = G1.ofFr q)
    (hrl : G1.toPoint rl = G1.ofFr (rlc - rli + h^n * q))
    (hlr_scalar : G2.toPoint lr = G2.ofFr (τ^n))
    (heq : rlc - rli + h^n * q = q * τ^n) :
    Bls.pairingCheck #[(ll, lr), (rl, G2.neg G2.generator)] = true := by
  apply (pairingCheck_neg_g2_iff ll rl lr G2.generator q (τ^n)
    (rlc - rli + h^n*q) 1 hp hr hlr G2.valid_generator
    hll hrl hlr_scalar G2.ofFr_one.symm).mpr
  simpa only [Fin.mul_one] using heq.symm

/-- The cell scalar identity supplies the final equation required above. -/
theorem cell_pairing_complete_of_polynomial
    (ll rl : G1) (lr : G2) (p I Q : _root_.Polynomial Fr)
    (τ h : Fr) (n : Nat) (q : Fr)
    (hp : G1.Valid ll) (hr : G1.Valid rl) (hlr : G2.Valid lr)
    (hll : G1.toPoint ll = G1.ofFr q)
    (hll_commit : G1.toPoint rl = G1.ofFr
      (p.eval τ - I.eval τ + h^n * q))
    (hlr_scalar : G2.toPoint lr = G2.ofFr (τ^n))
    (hid : p - I = Q * (Polynomial.X ^ n - Polynomial.C (h^n)))
    (hq : q = Q.eval τ) :
    Bls.pairingCheck #[(ll, lr), (rl, G2.neg G2.generator)] = true := by
  apply cell_pairing_complete ll rl lr τ h n q
    (p.eval τ) (I.eval τ) hp hr hlr hll hll_commit hlr_scalar
  rw [hq]
  exact cell_scalar_identity p I Q τ h n hid

end EthLib.Cryptography.Kzg.Opening
