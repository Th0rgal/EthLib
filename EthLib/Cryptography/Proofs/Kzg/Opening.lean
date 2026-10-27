import EthLib.Cryptography.Proofs.Kzg.OpeningAlgebra
import EthLib.Cryptography.Proofs.Kzg.Core
import EthLib.Cryptography.Proofs.Kzg.CoefficientPolynomial
import Mathlib.Algebra.Polynomial.Div

namespace EthLib.Cryptography.Kzg.Opening
open Bls (Fr G1 G2)
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

/-- Refinement of the executable verifier to the pure checker. Only visibility was changed. -/
theorem verifyKzgProofImpl_refines (commitment : G1) (z y : Fr) (proof : G1) :
    EthLib.Cryptography.Kzg.verifyKzgProofImpl
      commitment z y proof = (do
        let setup ← TrustedSetup.get!
        return check setup.g2Monomial[1]! commitment z y proof : KzgM Bool) := by
  rfl

/-- The mathematical quotient exists for every opening, including at the trapdoor.
    No division by `τ-z` is needed. -/
noncomputable def openingQuotient (p : _root_.Polynomial Fr) (z : Fr) :
    _root_.Polynomial Fr := p /ₘ (Polynomial.X - Polynomial.C z)

private theorem rearrange {R : Type*} [CommRing R] (a b c d : R)
    (he : b + c*d = a) : a-b = d*c := by linear_combination -he

/-- Polynomial division yields the KZG scalar equation at every evaluation point. -/
theorem openingQuotient_identity (p : _root_.Polynomial Fr) (z τ : Fr) :
    p.eval τ - p.eval z = (openingQuotient p z).eval τ * (τ-z) := by
  have h := congrArg (fun f : _root_.Polynomial Fr => f.eval τ)
    (Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C z))
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at h
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X] at h
  exact rearrange _ _ _ _ h


/-- Completeness for a polynomial and its opening quotient with valid concrete points.
    The hypotheses describe the commitment, quotient commitment and setup individually. -/
theorem check_polynomial_complete (tauG2 : G2) (commitment proof : G1)
    (τ z : Fr) (p : _root_.Polynomial Fr)
    (ht : G2.Valid tauG2) (hc : G1.Valid commitment) (hp : G1.Valid proof)
    (het : G2.toPoint tauG2 = G2.ofFr τ)
    (hec : G1.toPoint commitment = G1.ofFr (p.eval τ))
    (hep : G1.toPoint proof = G1.ofFr ((openingQuotient p z).eval τ)) :
    check tauG2 commitment z (p.eval z) proof = true := by
  apply (check_iff tauG2 commitment proof τ (p.eval τ)
    ((openingQuotient p z).eval τ) z (p.eval z) ht hc hp het hec hep).mpr
  exact openingQuotient_identity p z τ

/-- Read assumption for the IO setup slot is explicit; the verification result is derived. -/
theorem verifyKzgProofImpl_complete (setup : TrustedSetup) (τ z : Fr)
    (p : _root_.Polynomial Fr) (commitment proof : G1)
    (hread : TrustedSetup.get! = pure setup)
    (ht : G2.Valid setup.g2Monomial[1]!) (hc : G1.Valid commitment) (hp : G1.Valid proof)
    (het : G2.toPoint setup.g2Monomial[1]! = G2.ofFr τ)
    (hec : G1.toPoint commitment = G1.ofFr (p.eval τ))
    (hep : G1.toPoint proof = G1.ofFr ((openingQuotient p z).eval τ)) :
    EthLib.Cryptography.Kzg.verifyKzgProofImpl
      commitment z (p.eval z) proof = pure true := by
  rw [verifyKzgProofImpl_refines, hread]
  have h := check_polynomial_complete setup.g2Monomial[1]! commitment proof τ z p
    ht hc hp het hec hep
  change (do
    let s ← (pure setup : IO TrustedSetup)
    pure (.ok (check s.g2Monomial[1]! commitment z (p.eval z) proof))) =
      (pure (.ok true) : IO (Except KzgError Bool))
  exact congrArg (fun b => (pure (.ok b) : IO (Except KzgError Bool))) h

end EthLib.Cryptography.Kzg.Opening
